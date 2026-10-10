import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.ContextDescription
import OAI.Combinatorics.RamseyFive.Marking.MarkedStreamExtraction

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy SelectedTuple
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
local instance mabFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance mabPDE : DecidableEq (ℙ K V) := Classical.decEq _
local instance mabDDE : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _

theorem actual_marked_deficit (hd : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hd width hw l a)))
    (hm : (1:ℝ)/39≤eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hd width hw l a)))
    (hinc : ∀z,0<S.law z→TupleIncident (S.tuple z))
    (hcons : ∀z,0<S.law z→TupleConsistent (S.tuple z))
    (D : κ→Fin n→Finset (FlagPair K V)) (cap B L : ℝ) (hcap : 1≤cap)
    (hD : ∀c i,((D c i).card:ℝ)≤cap)
    (hsupp : ∀z,0<S.law z→∀i,S.tuple z i∈D (ctx z) i)
    (hΔ : 0≤Real.log cap-Real.log (153*(Nat.card K:ℝ)^4))
    (hent : (n:ℝ)*Real.log (153*(Nat.card K:ℝ)^4)-entropy (map S.law S.tuple)≤B)
    (hctx : entropy (map S.law ctx)≤L) :
    let T:=classStream hd width hw S ctx hl a hE
    let p:=pair T.law (markedContext ctx S.tuple) T.tuple
    mean (first p) (fun c=>(l:ℝ)*Real.log (153*(Nat.card K:ℝ)^4)-entropy (fiber p c))≤
      39*(B+L+(n:ℝ)*Real.log 800+
        expensiveBound K V*(Real.log cap-Real.log (153*(Nat.card K:ℝ)^4))) := by
  let p:=pair S.law ctx S.tuple
  have hpi : ∀c x,0<p (c,x)→TupleIncident x := by
    intro c x hx
    obtain ⟨z,hz,he⟩:=map_positive S.law (fun z=>(ctx z,S.tuple z)) (c,x) hx
    cases he
    exact hinc z hz
  have hpc : ∀c x,0<p (c,x)→TupleConsistent x := by
    intro c x hx
    obtain ⟨z,hz,he⟩:=map_positive S.law (fun z=>(ctx z,S.tuple z)) (c,x) hx
    cases he
    exact hcons z hz
  have hps : ∀c x,0<p (c,x)→∀i,x i∈D c i := by
    intro c x hx
    obtain ⟨z,hz,he⟩:=map_positive S.law (fun z=>(ctx z,S.tuple z)) (c,x) hx
    cases he
    exact hsupp z hz
  have hb:=marking_expected_deficit hd p hpc D cap (Real.log (153*(Nat.card K:ℝ)^4))
    B L hcap hD hps hΔ (by simpa only [p,second_pair] using hent)
      (by simpa only [p,first_pair] using hctx)
  have hnon : 0 ≤ mean (first (withMessage p markingMessage)) (fun c=>
      activeDeficit (fiber (withMessage p markingMessage) c) (unspecified c.2)
        (Real.log (153*(Nat.card K:ℝ)^4))) := by
    rw [mean]
    apply Finset.sum_nonneg
    intro c hc
    by_cases hp : 0<first (withMessage p markingMessage) c
    · exact mul_nonneg hp.le (marking_deficit_nonneg hd p hpi hpc c.1 c.2 hp)
    · have hz : first (withMessage p markingMessage) c=0 := le_antisymm (le_of_not_gt hp) (Law.nonneg _ _)
      rw [hz,zero_mul]
  obtain ⟨hE',heq⟩:=classStream_joint hd width hw S ctx hl a hE
  dsimp only
  rw [heq]
  apply (markedClassLaw_deficit hd p hpi hpc hl width hw a hE').trans
  have hm' : (1:ℝ)/39≤eventMass (first (withMessage p markingMessage))
      (selectedClassEvent l (fun c=>unspecified c.2) (markedCode hd width hw) a) := by
    simpa only [p,markedContext_law,eventMass_map_preimage,markedEvent] using hm
  apply (div_le_div_of_nonneg_right hb hE'.le).trans
  rw [div_le_iff₀ hE']
  have hn := hnon.trans hb
  have ht:=mul_le_mul_of_nonneg_left hm' hn
  dsimp only [expensiveBound]
  nlinarith
end
end SharpRamseyFive.Marking

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {Ω κ α β I : Type} [Fintype Ω] [Fintype κ] [Fintype α] [Fintype β] [Fintype I]

lemma fiber_pair_source (p : Law Ω) (ctx : Ω→κ) (x : Ω→α) (c : κ) (y : α)
    (hc : 0<first (pair p ctx x) c) (hy : 0<fiber (pair p ctx x) c y) :
    ∃z,0<p z ∧ ctx z=c ∧ x z=y := by
  have hp : 0<pair p ctx x (c,y) := by
    rw [mass_eq_first_mul_fiber]
    exact mul_pos hc hy
  obtain ⟨z,hz,he⟩:=map_positive p (fun z=>(ctx z,x z)) (c,y) hp
  exact ⟨z,hz,congrArg Prod.fst he,congrArg Prod.snd he⟩

lemma pair_fiber_domains (p : Law Ω) (ctx : Ω→κ) (x : Ω→I→β)
    (D : κ→I→Finset β) (hD : ∀z,0<p z→∀i,x z i∈D (ctx z) i)
    (c : κ) (hc : 0<first (pair p ctx x) c) :
    InDomains (fiber (pair p ctx x) c) (D c) := by
  intro y hy i
  obtain ⟨z,hz,he,rfl⟩:=fiber_pair_source p ctx x c y hc hy
  rw [←he]
  exact hD z hz i

lemma pair_fiber_pred (p : Law Ω) (ctx : Ω→κ) (x : Ω→α) (P : α→Prop)
    (hP : ∀z,0<p z→P (x z)) (c : κ) (hc : 0<first (pair p ctx x) c) :
    ∀y,0<fiber (pair p ctx x) c y→P y := by
  intro y hy
  obtain ⟨z,hz,he,rfl⟩:=fiber_pair_source p ctx x c y hc hy
  exact hP z hz

lemma pair_map_tuple (p : Law Ω) (ctx : Ω→κ) (x : Ω→α) (f : α→β) :
    pair p ctx (fun z=>f (x z))=map (pair p ctx x) (fun z=>(z.1,f z.2)) := by
  rw [pair,pair,map_comp]
  rfl

lemma fiber_pair_map (p : Law Ω) (ctx : Ω→κ) (x : Ω→α) (f : α→β)
    (c : κ) (hc : 0 < map p ctx c) :
    fiber (pair p ctx (fun z=>f (x z))) c=map (fiber (pair p ctx x) c) f := by
  have he : pair p ctx (fun z=>f (x z))=
      adaptiveLaw (map p ctx) (fun c=>map (fiber (pair p ctx x) c) f) := by
    rw [pair_map_tuple,←first_pair p ctx x]
    apply Law.ext_mean
    intro g
    rw [mean_map,mean_adaptive]
    simp_rw [mean_map]
    have hh:=congrArg (fun p=>mean p (fun z=>g (z.1,f z.2))) (adaptive_reconstruct (pair p ctx x))
    rw [mean_adaptive] at hh
    exact hh.symm
  rw [he]
  exact fiber_adaptive _ _ _ hc

namespace ContextDescription
variable {n : ℕ} {p : Law Ω} {x : Ω→Fin n→β} {L J : ℝ}
def boundedDomain (C : ContextDescription (κ:=κ) p x L J) (c : κ) (i : Fin n) :=
  if 0 < map p C.context c then C.domain c i else ∅
omit [Fintype β] in
lemma boundedDomain_cap (C : ContextDescription (κ:=κ) p x L J) (c : κ) (i : Fin n) :
    ((C.boundedDomain c i).card:ℝ)≤Real.exp J := by
  by_cases hc : 0 < map p C.context c
  · obtain ⟨z,hz,rfl⟩:=map_positive p C.context c hc
    simp only [boundedDomain,ite_eq_left hc]
    exact Real.le_exp_of_log_le (C.cap z hz i)
  · simp only [boundedDomain,ite_eq_right hc,Finset.card_empty,Nat.cast_zero]
    exact (Real.exp_pos _).le
omit [Fintype β] in
lemma boundedDomain_contains (C : ContextDescription (κ:=κ) p x L J) :
    ∀z,0<p z→∀i,x z i∈C.boundedDomain (C.context z) i := by
  intro z hz i
  have hc : 0 < map p C.context (C.context z) := by
    apply lt_of_lt_of_le hz
    change p z ≤ ∑ a,if C.context a=C.context z then p a else 0
    apply le_trans _ (Finset.single_le_sum (fun a _ => by split_ifs; exact p.nonneg a; exact le_rfl)
      (Finset.mem_univ z))
    simp
  simp only [boundedDomain,ite_eq_left hc]
  exact C.contains z hz i
end ContextDescription
end
end SharpRamseyFive.FiniteEntropy

end OAI
