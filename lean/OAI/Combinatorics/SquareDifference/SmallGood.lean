import OAI.Combinatorics.SquareDifference.MixedTransfer

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

lemma exists_small_strict_steps (p : ℕ) [Fact p.Prime] :
    ∃δ : ℕ → ZMod (smallQuadraticModulus p),(∀j,smallStrict p (δ j)) ∧ ∑j∈range 24,δ j=0 := by
  by_cases h2 : p=2
  · subst p
    refine ⟨fun _ => 1,fun j => ?_,?_⟩
    · simp only [smallStrict,ite_true]
    · simp only [sum_const,card_range,nsmul_eq_mul,mul_one]
      change (24 : ZMod 8)=0
      decide
  · let e : ZMod (smallQuadraticModulus p) ≃+* ZMod p := RingEquiv.cast (ite_eq_right h2)
    obtain ⟨δ,hδ,h0⟩ := exists_strict_square_steps p
    refine ⟨fun j => e.symm (δ j),?_,?_⟩
    · intro j
      simp only [smallStrict,h2,ite_false]
      refine ⟨fun he => (hδ j).1 (e.symm.injective (he.trans e.symm.map_zero.symm)),?_⟩
      obtain ⟨a,ha⟩ := (hδ j).2
      exact ⟨e.symm a,by rw [ha,map_mul]⟩
    · rw [←map_sum,h0,map_zero]

section Small

variable {S : Type*} [Fintype S] [instDecidableEqS : DecidableEq S] (ps : S → ℕ) [∀s,Fact (ps s).Prime]

lemma smallModulus_pos {S : Type*}
    [Fintype S]
    [DecidableEq S]
    (ps : S → ℕ)
    [∀ (s : S), Fact (Nat.Prime (ps s))] : 0<smallModulus ps := prod_pos (fun s _ => smallQuadraticModulus_pos (Fact.out : (ps s).Prime))

noncomputable def smallResidueEquiv (hinj : Function.Injective ps) :
    ZMod (smallModulus ps) ≃+* (∀s,ZMod (smallQuadraticModulus (ps s))) :=
  ZMod.prodEquivPi _ (smallQuadraticModuli_pairwise ps (fun _ => Fact.out) hinj)

lemma smallResidueEquiv_apply (hinj : Function.Injective ps) (x : ZMod (smallModulus ps)) (s : S) :
    smallResidueEquiv ps hinj x s=smallProjection ps s x := by
  exact ZMod.prodEquivPi_apply (fun s => smallQuadraticModulus (ps s))
    (smallQuadraticModuli_pairwise ps (fun _ => Fact.out) hinj) x s

lemma exists_small_product_steps (hinj : Function.Injective ps) :
    ∃δ : ℕ → ZMod (smallModulus ps),(∀j s,smallStrict (ps s) (smallProjection ps s (δ j))) ∧ ∑j∈range 24,δ j=0 := by
  classical
  choose δ hδ hs using fun s => exists_small_strict_steps (ps s)
  let e := smallResidueEquiv ps hinj
  refine ⟨fun j => e.symm (fun s => δ s j),?_,?_⟩
  · intro j s
    rw [←smallResidueEquiv_apply ps hinj]
    change smallStrict (ps s) (e (e.symm (fun s => δ s j)) s)
    rw [e.apply_symm_apply]
    exact hδ s j
  · apply e.injective
    rw [map_sum,map_zero]
    simp only [e.apply_symm_apply]
    funext s
    simp only [Finset.sum_apply,Pi.zero_apply]
    exact hs s

noncomputable def goodSmallAssignment (s : TupleVertex → ZMod (smallModulus ps)) : Prop :=
  ∀k<24,smallStrictPair ps (s (cycleVertex k)) (s (cycleVertex (k+1)))

lemma exists_goodSmallAssignment (hinj : Function.Injective ps) : ∃s,goodSmallAssignment ps s := by
  obtain ⟨δ,hδ,hδ0⟩ := exists_small_product_steps ps hinj
  obtain ⟨s,hs⟩ := exists_cyclic_labels (fun j : Fin 24 => cycleVertex j.val) cycleVertex_fin_injective δ hδ0
  refine ⟨s,fun k hk i => ?_⟩
  have hh := hs (⟨k,hk⟩ : Fin 24)
  rw [cycleVertex_fin_successor] at hh
  change s (cycleVertex (k+1))-s (cycleVertex k)=δ k at hh
  rw [hh]
  exact hδ k i

noncomputable def goodSmallProbability : ℝ := by
  classical
  letI : NeZero (smallModulus ps) := ⟨(smallModulus_pos ps).ne'⟩
  exact 𝔼 s : TupleVertex → ZMod (smallModulus ps),if goodSmallAssignment ps s then (1:ℝ) else 0

lemma goodSmallProbability_pos (hinj : Function.Injective ps) : 0<goodSmallProbability ps := by
  classical
  let : NeZero (smallModulus ps) := ⟨(smallModulus_pos ps).ne'⟩
  exact uniform_event_positive _ (exists_goodSmallAssignment ps hinj)

lemma goodSmallProbability_le_one : goodSmallProbability ps≤1 := by
  classical
  let : NeZero (smallModulus ps) := ⟨(smallModulus_pos ps).ne'⟩
  change (𝔼 s : TupleVertex → ZMod (smallModulus ps),if goodSmallAssignment ps s then (1:ℝ) else 0)≤1
  calc
    _ ≤ 𝔼 _s : TupleVertex → ZMod (smallModulus ps),(1:ℝ) := expect_le_expect (fun _ _ => by split_ifs <;> norm_num)
    _ = 1 := Fintype.expect_const 1

end Small

end SquareDifference

end

end OAI
