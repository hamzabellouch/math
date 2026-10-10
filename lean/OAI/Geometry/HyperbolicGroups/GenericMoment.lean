import Mathlib
import OAI.Geometry.HyperbolicGroups.Concentration
import OAI.Geometry.HyperbolicGroups.GenericTable

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace BernoulliCandidates
variable {V S I A : Type*} [Fintype V] [Fintype S] [Fintype I] [Fintype A]
  [DecidableEq V] [DecidableEq S] [DecidableEq I] [DecidableEq A]

omit [Fintype S] [DecidableEq S] in
lemma overlap_power_bound {N ε : ℝ} (hN : 1 ≤ N) (support : S → Finset V)
    (c : S → ℝ) (J : Finset S)
    (gap : ε ≤ ((J.biUnion support).card : ℝ) - ∑ s ∈ J, c s) :
    N ^ (Fintype.card V - (J.biUnion support).card) * (∏ s ∈ J, N ^ (-c s))⁻¹ ≤
      N ^ Fintype.card V * N ^ (-ε) := by
  have hN0 : 0 < N := by linarith
  have he : (∏ s ∈ J, N ^ (-c s))⁻¹ = N ^ (∑ s ∈ J, c s) := by
    rw [← Real.rpow_sum_of_pos hN0, Finset.sum_neg_distrib, Real.rpow_neg hN0.le, inv_inv]
  have hc := Finset.card_le_univ (J.biUnion support)
  rw [he, ← Real.rpow_natCast N (Fintype.card V - (J.biUnion support).card),
    ← Real.rpow_natCast N (Fintype.card V), ← Real.rpow_add hN0, ← Real.rpow_add hN0]
  apply Real.rpow_le_rpow_of_exponent_le hN
  rw [Nat.cast_sub hc]
  linarith

omit [Fintype I] in
lemma sum_inverse_overlap_power [Nonempty A] (row : (V → A) → S → I)
    (support : S → Finset V)
    (read : ∀ σ τ s, row σ s = row τ s → ∀ v ∈ support s, σ v = τ v)
    (C : Finset (V → A)) (σ : V → A) (c : S → ℝ) {ε : ℝ}
    (gap : ∀ J : Finset S, J.Nonempty →
      ε ≤ ((J.biUnion support).card : ℝ) - ∑ s ∈ J, c s) :
    (∑ τ ∈ C, ((∏ s ∈ shared row σ τ, (Fintype.card A : ℝ) ^ (-c s))⁻¹ - 1)) ≤
      Fintype.card (OverlapType S) * (Fintype.card A : ℝ) ^ Fintype.card V *
        (Fintype.card A : ℝ) ^ (-ε) := by
  classical
  have hn : (1 : ℝ) ≤ Fintype.card A := by
    exact_mod_cast (show 1 ≤ Fintype.card A from Fintype.card_pos)
  calc
    _ ≤ ∑ τ ∈ C, ∑ o : OverlapType S, if OverlapEvent row σ τ o then
        (∏ s ∈ o.1.val, (Fintype.card A : ℝ) ^ (-c s))⁻¹ else 0 := by
      apply Finset.sum_le_sum
      intro τ _
      exact inverse_overlap_le row σ τ _ (fun s => TableModel.powerProbability_pos hn (c s))
    _ = ∑ o : OverlapType S, (∑ τ ∈ C, if OverlapEvent row σ τ o then (1 : ℝ) else 0) *
        (∏ s ∈ o.1.val, (Fintype.card A : ℝ) ^ (-c s))⁻¹ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro o _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro τ _
      split_ifs <;> simp
    _ ≤ ∑ o : OverlapType S,
        (Fintype.card A : ℝ) ^ (Fintype.card V - (o.1.val.biUnion support).card) *
        (∏ s ∈ o.1.val, (Fintype.card A : ℝ) ^ (-c s))⁻¹ := by
      apply Finset.sum_le_sum
      intro o _
      exact mul_le_mul_of_nonneg_right (overlap_assignment_count row support read C σ o) (by positivity)
    _ ≤ ∑ _o : OverlapType S, (Fintype.card A : ℝ) ^ Fintype.card V *
        (Fintype.card A : ℝ) ^ (-ε) := by
      apply Finset.sum_le_sum
      intro o _
      exact overlap_power_bound hn support c o.1.val (gap _ o.1.property)
    _ = _ := by simp; ring

/-- The complete overlap-counting rule for row positions in possibly repeated
arrays, before substituting a candidate-cardinality lower bound. -/
theorem variance_power [Nonempty A] (row : (V → A) → S → I)
    (support : S → Finset V)
    (read : ∀ σ τ s, row σ s = row τ s → ∀ v ∈ support s, σ v = τ v)
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (C : Finset (V → A))
    (hi : ∀ σ ∈ C, Function.Injective (row σ)) (c : S → ℝ)
    (hq : ∀ σ ∈ C, ∀ s, p (row σ s) = (Fintype.card A : ℝ) ^ (-c s))
    {ε : ℝ} (gap : ∀ J : Finset S, J.Nonempty →
      ε ≤ ((J.biUnion support).card : ℝ) - ∑ s ∈ J, c s) :
    (FiniteLaw.bernoulliProduct p hp).variance (fun w => (count row C w : ℝ)) ≤
      (∏ s, (Fintype.card A : ℝ) ^ (-c s)) ^ 2 * C.card *
      (Fintype.card (OverlapType S) * (Fintype.card A : ℝ) ^ Fintype.card V *
        (Fintype.card A : ℝ) ^ (-ε)) := by
  have hn : (1 : ℝ) ≤ Fintype.card A := by
    exact_mod_cast (show 1 ≤ Fintype.card A from Fintype.card_pos)
  rw [variance_count row p hp C hi _ (fun s => TableModel.powerProbability_pos hn (c s)) hq]
  calc
    _ ≤ (∏ s, (Fintype.card A : ℝ) ^ (-c s)) ^ 2 *
        ∑ _σ ∈ C, (Fintype.card (OverlapType S) * (Fintype.card A : ℝ) ^ Fintype.card V *
          (Fintype.card A : ℝ) ^ (-ε)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum fun σ _ => sum_inverse_overlap_power row support read C σ c gap
    _ = _ := by simp; ring

/-- Explicit relative variance; the lower cardinality is proved below from
fieldwise injectivity, not assumed as a sampling conclusion. -/
theorem relative_variance_power [Nonempty A] (row : (V → A) → S → I)
    (support : S → Finset V)
    (read : ∀ σ τ s, row σ s = row τ s → ∀ v ∈ support s, σ v = τ v)
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (C : Finset (V → A))
    (hi : ∀ σ ∈ C, Function.Injective (row σ)) (c : S → ℝ)
    (hq : ∀ σ ∈ C, ∀ s, p (row σ s) = (Fintype.card A : ℝ) ^ (-c s))
    (hC : ((Fintype.card A : ℝ) / 2) ^ Fintype.card V ≤ C.card)
    {ε : ℝ} (gap : ∀ J : Finset S, J.Nonempty →
      ε ≤ ((J.biUnion support).card : ℝ) - ∑ s ∈ J, c s) :
    (FiniteLaw.bernoulliProduct p hp).variance (fun w => (count row C w : ℝ)) ≤
      Fintype.card (OverlapType S) * 2 ^ Fintype.card V * (Fintype.card A : ℝ) ^ (-ε) *
      ((FiniteLaw.bernoulliProduct p hp).expect (fun w => (count row C w : ℝ))) ^ 2 := by
  have hpow : (Fintype.card A : ℝ) ^ Fintype.card V ≤ (2 : ℝ) ^ Fintype.card V * C.card := by
    calc
      _ = (2 : ℝ) ^ Fintype.card V * ((Fintype.card A : ℝ) / 2) ^ Fintype.card V := by
        rw [← mul_pow]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hC (by positivity)
  rw [expect_count row p hp C hi _ hq]
  refine (variance_power row support read p hp C hi c hq gap).trans ?_
  calc
    _ ≤ (∏ s, (Fintype.card A : ℝ) ^ (-c s)) ^ 2 * C.card *
        (Fintype.card (OverlapType S) * ((2 : ℝ) ^ Fintype.card V * C.card) *
          (Fintype.card A : ℝ) ^ (-ε)) := by
      gcongr
    _ = _ := by ring

end BernoulliCandidates
end HyperbolicObstruction
end
end

section

end
end

end OAI
