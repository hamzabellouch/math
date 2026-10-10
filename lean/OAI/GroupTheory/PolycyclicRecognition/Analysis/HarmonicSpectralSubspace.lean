import OAI.GroupTheory.PolycyclicRecognition.Analysis.HarmonicVolumeDeterminant
import Mathlib.LinearAlgebra.Dimension.Finite

namespace OAI

/-! # A large subspace from a determinant bound

If all eigenvalues are at least one and their product is at most `K^n`,
at least half are at most `K^2`. These coordinates give the controlled-growth
subspace used by the harmonic averaging argument.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {ι : Type*} [Fintype ι]

theorem half_eigenvalues_le_square (ev : ι → ℝ) (K : ℝ) (hK : 1 < K)
    (hev : ∀ i, 1 ≤ ev i) (hprod : ∏ i, ev i ≤ K ^ Fintype.card ι) :
    Fintype.card ι ≤ 2 * (univ.filter (fun i => ev i ≤ K ^ 2)).card := by
  classical
  let good := univ.filter (fun i => ev i ≤ K ^ 2)
  let bad := univ.filter (fun i => K ^ 2 < ev i)
  have hcount : good.card + bad.card = Fintype.card ι := by
    simpa only [good, bad, not_le, card_univ] using
      card_filter_add_card_filter_not (s := (univ : Finset ι)) (p := fun i => ev i ≤ K ^ 2)
  have hpow : K ^ (2 * bad.card) ≤ K ^ Fintype.card ι := by
    calc
      _ = ∏ _i ∈ bad, K ^ 2 := by simp [pow_mul]
      _ ≤ ∏ i ∈ bad, ev i := prod_le_prod₀ (fun _ _ => sq_nonneg K)
        (fun i hi => (mem_filter.mp hi).2.le)
      _ ≤ ∏ i, ev i := prod_le_prod_of_subset_of_one_le₀ (subset_univ bad)
        (fun i _ => (by norm_num : (0 : ℝ) ≤ 1).trans (hev i)) (fun i _ _ => hev i)
      _ ≤ _ := hprod
  have hn : 2 * bad.card ≤ Fintype.card ι := by
    by_contra h
    exact (pow_lt_pow_right₀ hK (Nat.lt_of_not_ge h)).not_ge hpow
  change Fintype.card ι ≤ 2 * good.card
  omega

def spectralSmallSubspace (ev : ι → ℝ) (K : ℝ) : Submodule ℝ (ι → ℝ) where
  carrier := {v | ∀ i, K ^ 2 < ev i → v i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by intro v w hv hw i hi; change v i + w i = 0; rw [hv i hi, hw i hi, add_zero]
  smul_mem' := by intro c v hv i hi; change c * v i = 0; rw [hv i hi, mul_zero]

def spectralSmallSubspaceEquiv (ev : ι → ℝ) (K : ℝ) :
    spectralSmallSubspace ev K ≃ₗ[ℝ] ({i : ι // ev i ≤ K ^ 2} → ℝ) := by
  classical
  exact
  { toFun := fun v i => v.val i.val
    invFun := fun f => ⟨fun i => if hi : ev i ≤ K ^ 2 then f ⟨i, hi⟩ else 0, by
      intro i hi
      simp [not_le_of_gt hi]⟩
    left_inv := fun v => by
      apply Subtype.ext
      funext i
      by_cases hi : ev i ≤ K ^ 2
      · simp [hi]
      · simp [hi, v.property i (lt_of_not_ge hi)]
    right_inv := fun f => by funext i; simp [i.property]
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem spectralSmallSubspace_finite (ev : ι → ℝ) (K : ℝ) :
    Module.Finite ℝ (spectralSmallSubspace ev K) := by
  classical
  exact Module.Finite.of_injective (spectralSmallSubspaceEquiv ev K).toLinearMap
    (spectralSmallSubspaceEquiv ev K).injective

theorem spectralSmallSubspace_finrank (ev : ι → ℝ) (K : ℝ) :
    Module.finrank ℝ (spectralSmallSubspace ev K) =
      (univ.filter (fun i => ev i ≤ K ^ 2)).card := by
  classical
  simpa only [Module.finrank_pi, Module.finrank_self, mul_one, Fintype.card_subtype] using
    (spectralSmallSubspaceEquiv ev K).finrank_eq

theorem spectralSmallSubspace_dimension (ev : ι → ℝ) (K : ℝ) (hK : 1 < K)
    (hev : ∀ i, 1 ≤ ev i) (hprod : ∏ i, ev i ≤ K ^ Fintype.card ι) :
    Fintype.card ι ≤ 2 * Module.finrank ℝ (spectralSmallSubspace ev K) := by
  rw [spectralSmallSubspace_finrank]
  exact half_eigenvalues_le_square ev K hK hev hprod

theorem spectralSmallSubspace_quadratic_bound (ev : ι → ℝ) (K : ℝ)
    (v : spectralSmallSubspace ev K) :
    (∑ i, ev i * (v.val i) ^ 2) ≤ K ^ 2 * ∑ i, (v.val i) ^ 2 := by
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  by_cases hi : ev i ≤ K ^ 2
  · exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
  · rw [v.property i (lt_of_not_ge hi)]
    simp

end PolycyclicRecognition

end

end OAI
