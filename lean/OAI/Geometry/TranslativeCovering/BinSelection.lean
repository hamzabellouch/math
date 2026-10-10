import OAI.Geometry.TranslativeCovering.ActivityBins

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1 u_2 u_3

namespace BinSelection
open Set
open scoped Classical BigOperators

lemma score_eq {Ω : Type u_1} [MeasurableSpace Ω] {M : ℕ} (A : Set (Ω×Ω)) (x : Fin M → Ω) :
    TargetSampling.score A x =
      (((Finset.univ : Finset (Fin M×Fin M)).filter (fun p => p.1 ≠ p.2 ∧ (x p.1,x p.2) ∈ A)).card:ℝ) := by
  simp only [TargetSampling.score,TargetSampling.pairs,Finset.sum_filter,Set.indicator_apply,
    Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp_all

lemma restricted_bad {Ω : Type u_2} [MeasurableSpace Ω] {M : ℕ}
    (A : Set (Ω×Ω)) (x : Fin M → Ω) (S : Finset (Fin M)) :
    (((Finset.univ : Finset (S×S)).filter (fun p => p.1 ≠ p.2 ∧ (x p.1,x p.2) ∈ A)).card:ℝ) ≤
      TargetSampling.score A x := by
  rw [score_eq]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card_of_injOn (fun p : S×S => (p.1.val,p.2.val))
  · intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,(fun h => hp'.1 (Subtype.ext h)),hp'.2⟩
  · intro p _ q _ he
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst he)
    · exact Subtype.ext (congrArg Prod.snd he)

lemma bad_bin {Ω : Type u_3} [MeasurableSpace Ω] {M : ℕ}
    (A : Set (Ω×Ω)) (x : Fin M → Ω) (S : Finset (Fin M)) {Q f : ℝ}
    (hQ : 0 ≤ Q) (hf : 0 ≤ f) (hcard : (M:ℝ) ≤ Q*S.card)
    (hscore : TargetSampling.score A x ≤ 10*((TargetSampling.pairs M).card:ℝ)*f) :
    (((Finset.univ : Finset (S×S)).filter (fun p => p.1 ≠ p.2 ∧ (x p.1,x p.2) ∈ A)).card:ℝ) ≤
      10*f*Q^2*(Fintype.card S:ℝ)^2 := by
  have hp : ((TargetSampling.pairs M).card:ℝ) ≤ (M:ℝ)^2 := by
    have hh := Finset.card_le_card (Finset.filter_subset (s := (Finset.univ : Finset (Fin M×Fin M))) (p := fun p => p.1 ≠ p.2))
    simpa only [TargetSampling.pairs,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,pow_two] using Nat.cast_le (α := ℝ).mpr hh
  have hsq := (sq_le_sq₀ (Nat.cast_nonneg M) (mul_nonneg hQ (Nat.cast_nonneg S.card))).mpr hcard
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hp.trans hsq) (by norm_num : (0:ℝ)≤10)) hf
  exact (restricted_bad A x S).trans (hscore.trans (by simpa only [Fintype.card_coe] using hh.trans_eq (by ring)))
end BinSelection

end OAI
