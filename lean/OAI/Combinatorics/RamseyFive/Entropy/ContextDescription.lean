import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.CountedExtraction

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
open SelectedTuple MessageWeights
noncomputable section
local instance descriptionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Ω β κ Θ α : Type*} [Fintype Ω] [Fintype β] [Fintype κ] [Fintype Θ] [Fintype α]

structure ContextDescription {n : ℕ} (p : Law Ω) (x : Ω→Fin n→β) (L J : ℝ) where
  context : Ω→κ
  domain : κ→Fin n→Finset β
  entropy_bound : entropy (map p context)≤L
  contains : ∀ a,0<p a→∀ i,x a i∈domain (context a) i
  cap : ∀ a,0<p a→∀ i,Real.log (domain (context a) i).card≤J

namespace ContextDescription
variable {n : ℕ} {p : Law Ω} {x : Ω→Fin n→β} {L J : ℝ}

lemma entropy_le (C : ContextDescription (κ:=κ) p x L J) :
    entropy (map p x)≤L+n*J := by
  have hh:=slot_context_entropy (pair p C.context x) C.domain L J
    (by simpa only [first_pair] using C.entropy_bound) (by
      intro z hz i
      obtain ⟨a,ha,rfl⟩:=map_positive p (fun a=>(C.context a,x a)) z hz
      exact C.contains a ha i) (by
      intro c hc i
      rw [first_pair] at hc
      obtain ⟨a,ha,rfl⟩:=map_positive p C.context c hc
      exact C.cap a ha i)
  simpa only [second_pair,Fintype.card_fin] using hh

def augment (C : ContextDescription (κ:=κ) p x L J) (q : Ω→Law Θ) :
    ContextDescription (κ:=κ) (adaptiveLaw p q) (fun z=>x z.1) L J where
  context z:=C.context z.1
  domain:=C.domain
  entropy_bound:=by rw [adaptive_stream];exact C.entropy_bound
  contains:=by
    intro z hz i
    have hp : 0<p z.1 := by
      change 0<p z.1*q z.1 z.2 at hz
      exact (mul_pos_iff.mp hz).resolve_right (fun h=>(p.nonneg _).not_gt h.1) |>.1
    exact C.contains _ hp i
  cap:=by
    intro z hz i
    have hp : 0<p z.1 := by
      change 0<p z.1*q z.1 z.2 at hz
      exact (mul_pos_iff.mp hz).resolve_right (fun h=>(p.nonneg _).not_gt h.1) |>.1
    exact C.cap _ hp i
end ContextDescription

def countedDescription {n l w : ℕ} (hl : l≤n) (p : Law Ω)
    (x : Ω→Fin n→β) (S : Ω→Finset (Fin n)) (ctx : Ω→κ) (D : κ→Fin w→Finset β)
    (slot : Ω→Fin n→Fin w) (hslot : ∀ a,Monotone (slot a))
    (hdom : ∀ a,0<p a→∀ i∈S a,x a i∈D (ctx a) (slot a i))
    (hE : 0<eventMass p (Finset.univ.filter fun a=>l≤(S a).card))
    (L M : ℝ) (hctx : entropy (map (conditionOn p _ hE) ctx)≤L)
    (hc : ∀ a,0<p a→∀ j,Real.log (D (ctx a) j).card≤M) :
    ContextDescription (κ:=κ×RunAssignment l w) (conditionOn p _ hE)
      (fun a=>retainedTuple hl (x a) (S a)) (L+w*Real.log (l+1)) M where
  context a:=(ctx a,retainedAssignment hl (S a) (slot a) (hslot a))
  domain c i:=D c.1 (c.2.val i)
  entropy_bound:=by
    have hh:=entropy_subadditive (pair (conditionOn p _ hE) ctx
      (fun a=>retainedAssignment hl (S a) (slot a) (hslot a)))
    simp only [first_pair,second_pair] at hh
    exact hh.trans (add_le_add hctx (runAssignment_entropy _))
  contains:=by
    intro a ha i
    obtain ⟨he,hp⟩:=conditionOn_positive p _ hE a ha
    exact hdom a hp _ (retainedIndices_mem hl _ (Finset.mem_filter.mp he).2 i)
  cap:=by
    intro a ha i
    exact hc a (conditionOn_positive p _ hE a ha).2 _

theorem fixed_table_stage {N n l w : ℕ} {admissible : (Fin N→α)→Prop}
    (hl : l<n) (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (tables : Law Θ) (positions : Θ→Ω→Finset (Fin n))
    (ctx : Θ→Ω→κ) (D : Θ→κ→Fin w→Finset β)
    (slot : Ω→Fin n→Fin w) (hslot : ∀ a,Monotone (slot a))
    (cost : Θ→κ→ℝ) (L M : ℝ)
    (hweight : ∀ t,(∑ m,Real.exp (-cost t m))≤1)
    (hcost : ∀ t a,0<S.law a→cost t (ctx t a)≤L)
    (hcap : ∀ t a,0<S.law a→∀ j,Real.log (D t (ctx t a) j).card≤M)
    (hdom : ∀ t a,0<S.law a→∀ i∈positions t a,S.tuple a i∈D t (ctx t a) (slot a i))
    (hloss : mean (adaptiveLaw S.law (fun _=>tables))
      (fun z=>((positions z.2 z.1)ᶜ.card:ℝ))≤((n:ℝ)-l)/10) :
    ∃ (t : Θ) (hE : 0<eventMass S.law (Finset.univ.filter fun a=>l≤(positions t a).card)),
      (9:ℝ)/10≤eventMass S.law (Finset.univ.filter fun a=>l≤(positions t a).card) ∧
      let S':=(S.restrict _ hE).extract hl.le (positions t)
      S'.density≤(10/9)*S.density ∧
      Nonempty (ContextDescription (κ:=κ×RunAssignment l w) S'.law S'.tuple
        (L+w*Real.log (l+1)) M) := by
  obtain ⟨t,hE,ht,hden,_⟩:=fixed_table_extraction hl S tables positions ctx D slot hslot
    cost L M hweight hcost hcap hdom hloss
  refine ⟨t,hE,ht,hden,⟨?_⟩⟩
  apply countedDescription hl.le S.law S.tuple (positions t) (ctx t) (D t) slot hslot
    (hdom t) hE L M _ (hcap t)
  apply entropy_le_bound _ (cost t) (hweight t)
  intro m hm
  obtain ⟨a,ha,rfl⟩:=map_positive (conditionOn S.law _ hE) (ctx t) m hm
  exact hcost t a (conditionOn_positive S.law _ hE a ha).2
end

noncomputable section
local instance dependentTableFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Ω β Θ α : Type*} [Fintype Ω] [Fintype β] [Fintype Θ] [Fintype α]

theorem fixed_table_stage_dependent {N n l w : ℕ} {admissible : (Fin N→α)→Prop}
    (hl : l<n) (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (tables : Law Θ) (κ : Θ→Type*) [∀ t,Fintype (κ t)]
    (positions : Θ→Ω→Finset (Fin n))
    (ctx : (t : Θ)→Ω→κ t) (D : (t : Θ)→κ t→Fin w→Finset β)
    (slot : Ω→Fin n→Fin w) (hslot : ∀ a,Monotone (slot a))
    (cost : (t : Θ)→κ t→ℝ) (L M : ℝ)
    (hweight : ∀ t,(∑ m,Real.exp (-cost t m))≤1)
    (hcost : ∀ t a,0<S.law a→cost t (ctx t a)≤L)
    (hcap : ∀ t a,0<S.law a→∀ j,Real.log (D t (ctx t a) j).card≤M)
    (hdom : ∀ t a,0<S.law a→∀ i∈positions t a,S.tuple a i∈D t (ctx t a) (slot a i))
    (hloss : mean (adaptiveLaw S.law (fun _=>tables))
      (fun z=>((positions z.2 z.1)ᶜ.card:ℝ))≤((n:ℝ)-l)/10) :
    ∃ (t : Θ) (hE : 0<eventMass S.law (Finset.univ.filter fun a=>l≤(positions t a).card)),
      (9:ℝ)/10≤eventMass S.law (Finset.univ.filter fun a=>l≤(positions t a).card) ∧
      let S':=(S.restrict _ hE).extract hl.le (positions t)
      S'.density≤(10/9)*S.density ∧
      Nonempty (ContextDescription (κ:=κ t×RunAssignment l w) S'.law S'.tuple
        (L+w*Real.log (l+1)) M) := by
  let E:=fun t=>Finset.univ.filter (fun a=>l≤(positions t a).card)
  have he:=extraction_probability (adaptiveLaw S.law (fun _=>tables))
    (fun z=>positions z.2 z.1) hl (by simpa only [Finset.card_compl] using hloss)
  have heq : (Finset.univ.filter fun z : Ω×Θ=>l≤(positions z.2 z.1).card)=
      (Finset.univ.filter fun z : Ω×Θ=>z.1∈E z.2) := by
    ext z
    simp only [E,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [heq,independent_event_average] at he
  obtain ⟨t,_,ht⟩:=fix_independent_table S.law tables E (9/10) he
  have hE : 0<eventMass S.law (E t) := lt_of_lt_of_le (by norm_num) ht
  refine ⟨t,hE,ht,?_,⟨?_⟩⟩
  · change S.density/eventMass S.law (E t)≤(10/9)*S.density
    have h:=div_le_div_of_nonneg_left S.density_nonneg (by norm_num : (0:ℝ)<9/10) ht
    calc
      _ ≤ S.density/(9/10) := h
      _ = _ := by ring
  · apply countedDescription hl.le S.law S.tuple (positions t) (ctx t) (D t) slot hslot
      (hdom t) hE L M _ (hcap t)
    apply entropy_le_bound _ (cost t) (hweight t)
    intro m hm
    obtain ⟨a,ha,rfl⟩:=map_positive (conditionOn S.law _ hE) (ctx t) m hm
    exact hcost t a (conditionOn_positive S.law _ hE a ha).2
end
end SharpRamseyFive.FiniteEntropy

end OAI
