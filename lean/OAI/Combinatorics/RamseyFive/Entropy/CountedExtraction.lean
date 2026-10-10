import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.MessageCounting
import OAI.Combinatorics.RamseyFive.Iteration.StageState

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
noncomputable section
local instance countedFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def RunAssignment (l w : ℕ) := {a : Fin l→Fin w // Monotone a}
instance (l w : ℕ) : Fintype (RunAssignment l w) := inferInstanceAs (Fintype {a : Fin l→Fin w // Monotone a})

def runCutoff {l w : ℕ} (a : RunAssignment l w) (j : Fin w) : Fin (l+1) :=
  ⟨(Finset.univ.filter fun i=>a.val i≤j).card,by
    have h:=Finset.card_le_univ (Finset.univ.filter fun i=>a.val i≤j)
    simp only [Fintype.card_fin] at h
    omega⟩

lemma le_iff_lt_runCutoff {l w : ℕ} (a : RunAssignment l w) (i : Fin l) (j : Fin w) :
    a.val i≤j ↔ i.val<(runCutoff a j).val := by
  constructor
  · intro ha
    have hsub : Finset.Iic i⊆Finset.univ.filter (fun k=>a.val k≤j) := by
      intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(a.property (Finset.mem_Iic.mp hk)).trans ha⟩
    have h:=Finset.card_le_card hsub
    simp only [Fin.card_Iic] at h
    exact Nat.lt_of_succ_le h
  · intro hi
    by_contra! ha
    have hsub : Finset.univ.filter (fun k=>a.val k≤j)⊆Finset.Iio i := by
      intro k hk
      apply Finset.mem_Iio.mpr
      by_contra! hik
      exact (not_le_of_gt ha) ((a.property hik).trans (Finset.mem_filter.mp hk).2)
    have h:=Finset.card_le_card hsub
    simp only [Fin.card_Iio] at h
    exact (not_lt_of_ge h) hi

lemma runCutoff_injective {l w : ℕ} : Function.Injective (@runCutoff l w) := by
  intro a b h
  apply Subtype.ext
  funext i
  apply le_antisymm
  · apply (le_iff_lt_runCutoff a i (b.val i)).mpr
    rw [h]
    exact (le_iff_lt_runCutoff b i (b.val i)).mp le_rfl
  · apply (le_iff_lt_runCutoff b i (a.val i)).mpr
    rw [←h]
    exact (le_iff_lt_runCutoff a i (a.val i)).mp le_rfl

lemma runAssignment_card (l w : ℕ) : Fintype.card (RunAssignment l w)≤(l+1)^w := by
  simpa only [Fintype.card_fun,Fintype.card_fin] using
    Fintype.card_le_of_injective (@runCutoff l w) runCutoff_injective

variable {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]

lemma runAssignment_entropy {l w : ℕ} (p : Law (RunAssignment l w)) :
    entropy p≤w*Real.log (l+1) := by
  have hc:=entropy_le_log_card p
  have hpos : 0<Fintype.card (RunAssignment l w) := by
    obtain ⟨a,ha⟩:=mean_exists_ge p (fun _=>(0:ℝ))
    exact Fintype.card_pos_iff.mpr ⟨a⟩
  have hlog:=Real.log_le_log (by exact_mod_cast hpos : (0:ℝ)<Fintype.card (RunAssignment l w))
    (show (Fintype.card (RunAssignment l w):ℝ)≤((l+1)^w:ℕ) by exact_mod_cast runAssignment_card l w)
  have he : Real.log (((l+1)^w:ℕ):ℝ)=(w:ℝ)*Real.log (l+1) := by
    rw [Nat.cast_pow,Real.log_pow]
    simp only [Nat.cast_add,Nat.cast_one]
  exact hc.trans (he ▸ hlog)

theorem slot_context_entropy {ι : Type*} [Fintype ι] (p : Law (κ×(ι→β)))
    (D : κ→ι→Finset β) (L M : ℝ) (hctx : entropy (first p)≤L)
    (hs : ∀ z,0<p z→∀ i,z.2 i∈D z.1 i)
    (hc : ∀ c,0<first p c→∀ i,Real.log (D c i).card≤M) :
    entropy (second p)≤L+Fintype.card ι*M := by
  have he : entropy p≤L+Fintype.card ι*M := by
    rw [entropy_chain]
    apply add_le_add hctx
    calc
      _ ≤ ∑ c,first p c*((Fintype.card ι:ℝ)*M) := by
        apply Finset.sum_le_sum
        intro c _
        by_cases hz : 0<first p c
        · apply mul_le_mul_of_nonneg_left _ ((first p).nonneg c)
          have hd : InDomains (fiber p c) (D c) := by
            intro x hx i
            exact hs (c,x) (by rw [mass_eq_first_mul_fiber];exact mul_pos hz hx) i
          have ht:=totalCorrelation_nonneg (fiber p c)
          have hm : (∑ i:ι,entropy (map (fiber p c) (fun x=>x i)))≤Fintype.card ι*M := by
            calc
              _ ≤ ∑ i:ι,M := Finset.sum_le_sum fun i _=>hd.entropy_cap M (hc c hz) i
              _ = _ := by simp
          dsimp only [totalCorrelation] at ht
          linarith
        · have hzero : first p c=0 := le_antisymm (le_of_not_gt hz) ((first p).nonneg c)
          simp [hzero]
      _ = _ := by rw [←Finset.sum_mul,(first p).sum_one,one_mul]
  have hh:=entropy_map_le p Prod.snd
  rw [map_second] at hh
  exact hh.trans he

def retainedAssignment {n l w : ℕ} (hl : l≤n) (S : Finset (Fin n))
    (slot : Fin n→Fin w) (hslot : Monotone slot) : RunAssignment l w :=
  ⟨slot ∘ retainedIndices hl S,hslot.comp (retainedIndices hl S).monotone⟩

theorem counted_extracted_entropy {n l w : ℕ} (hl : l≤n) (p : Law α)
    (x : α→Fin n→β) (S : α→Finset (Fin n)) (ctx : α→κ) (D : κ→Fin w→Finset β)
    (slot : α→Fin n→Fin w) (hslot : ∀ a,Monotone (slot a))
    (hdom : ∀ a,0<p a→∀ i∈S a,x a i∈D (ctx a) (slot a i))
    (hE : 0<eventMass p (Finset.univ.filter fun a=>l≤(S a).card))
    (L M : ℝ) (hctx : entropy (map (conditionOn p _ hE) ctx)≤L)
    (hc : ∀ c j,Real.log (D c j).card≤M) :
    entropy (map (conditionOn p _ hE) (fun a=>retainedTuple hl (x a) (S a)))≤
      L+w*Real.log (l+1)+l*M := by
  let q:=conditionOn p _ hE
  let runs:=fun a=>retainedAssignment hl (S a) (slot a) (hslot a)
  let outctx:=fun a=>(ctx a,runs a)
  have hout : entropy (map q outctx)≤L+w*Real.log (l+1) := by
    have hh:=entropy_subadditive (pair q ctx runs)
    simp only [first_pair,second_pair] at hh
    exact hh.trans (add_le_add hctx (runAssignment_entropy (map q runs)))
  have hh:=slot_context_entropy (pair q outctx (fun a=>retainedTuple hl (x a) (S a)))
    (fun c i=>D c.1 (c.2.val i)) (L+w*Real.log (l+1)) M
    (by simpa only [first_pair] using hout) (by
      intro z hz i
      obtain ⟨a,ha,rfl⟩:=map_positive q (fun a=>(outctx a,retainedTuple hl (x a) (S a))) z hz
      obtain ⟨he,hp⟩:=conditionOn_positive p _ hE a ha
      exact hdom a hp _ (retainedIndices_mem hl _ (Finset.mem_filter.mp he).2 i))
    (fun c _ i=>hc c.1 (c.2.val i))
  simpa only [second_pair,Fintype.card_fin] using hh
end
end

open scoped Classical BigOperators
open MessageWeights SelectedTuple
noncomputable section
local instance fixedFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {α β κ Ω Θ : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype Ω] [Fintype Θ]

theorem counted_extracted_entropy_on_support {n l w : ℕ} (hl : l≤n) (p : Law Ω)
    (x : Ω→Fin n→β) (S : Ω→Finset (Fin n)) (ctx : Ω→κ) (D : κ→Fin w→Finset β)
    (slot : Ω→Fin n→Fin w) (hslot : ∀ a,Monotone (slot a))
    (hdom : ∀ a,0<p a→∀ i∈S a,x a i∈D (ctx a) (slot a i))
    (hE : 0<eventMass p (Finset.univ.filter fun a=>l≤(S a).card))
    (L M : ℝ) (hctx : entropy (map (conditionOn p _ hE) ctx)≤L)
    (hc : ∀ a,0<p a→∀ j,Real.log (D (ctx a) j).card≤M) :
    entropy (map (conditionOn p _ hE) (fun a=>retainedTuple hl (x a) (S a)))≤
      L+w*Real.log (l+1)+l*M := by
  let q:=conditionOn p _ hE
  let runs:=fun a=>retainedAssignment hl (S a) (slot a) (hslot a)
  let outctx:=fun a=>(ctx a,runs a)
  have hout : entropy (map q outctx)≤L+w*Real.log (l+1) := by
    have hh:=entropy_subadditive (pair q ctx runs)
    simp only [first_pair,second_pair] at hh
    exact hh.trans (add_le_add hctx (runAssignment_entropy (map q runs)))
  have hh:=slot_context_entropy (pair q outctx (fun a=>retainedTuple hl (x a) (S a)))
    (fun c i=>D c.1 (c.2.val i)) (L+w*Real.log (l+1)) M
    (by simpa only [first_pair] using hout) (by
      intro z hz i
      obtain ⟨a,ha,rfl⟩:=map_positive q (fun a=>(outctx a,retainedTuple hl (x a) (S a))) z hz
      obtain ⟨he,hp⟩:=conditionOn_positive p _ hE a ha
      exact hdom a hp _ (retainedIndices_mem hl _ (Finset.mem_filter.mp he).2 i)) (by
      intro c hc' i
      rw [first_pair] at hc'
      obtain ⟨a,ha,rfl⟩:=map_positive q outctx c hc'
      exact hc a (conditionOn_positive p _ hE a ha).2 _)
  simpa only [second_pair,Fintype.card_fin] using hh

lemma independent_event_average (p : Law Ω) (tables : Law Θ) (E : Θ→Finset Ω) :
    eventMass (adaptiveLaw p (fun _=>tables))
      (Finset.univ.filter fun z=>z.1∈E z.2)=mean tables (fun t=>eventMass p (E t)) := by
  simp only [eventMass,Finset.sum_filter,adaptiveLaw,Fintype.sum_prod_type,mean]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [←Finset.sum_filter,Finset.mul_sum]
  simp only [Finset.filter_univ_mem]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem fixed_table_extraction {N n l w : ℕ} {admissible : (Fin N→α)→Prop}
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
      entropy (map S'.law S'.tuple)≤L+w*Real.log (l+1)+l*M := by
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
  refine ⟨t,hE,ht,?_⟩
  dsimp only
  constructor
  · change S.density/eventMass S.law (E t)≤(10/9)*S.density
    have h:=div_le_div_of_nonneg_left S.density_nonneg (by norm_num : (0:ℝ)<9/10) ht
    calc
      _ ≤ S.density/(9/10) := h
      _ = _ := by ring
  · apply counted_extracted_entropy_on_support hl.le S.law S.tuple
      (positions t) (ctx t) (D t) slot hslot (hdom t) hE L M
    · apply entropy_le_bound _ (cost t) (hweight t)
      intro m hm
      obtain ⟨a,ha,rfl⟩:=map_positive (conditionOn S.law (E t) hE) (ctx t) m hm
      exact hcost t a (conditionOn_positive S.law (E t) hE a ha).2
    · exact hcap t
end

end SharpRamseyFive.FiniteEntropy

end OAI
