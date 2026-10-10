import OAI.Geometry.RCD.Harmonic.OperatorQuadraticDerivative
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.SpecificCodomains.Pi

namespace OAI

/-! # Integrating the finite polarization used by the cutoff error -/

open MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}

/-- Integration of a symmetric operator family preserves the quadratic
identity supplied by its finite polarizing tests. -/
theorem integrated_polarization_energy (B : X → Euclidean n →L[ℝ] Euclidean n)
    (hB : ∀ x, (B x).IsSymmetric)
    (hint : ∀ v, Integrable (fun x => ⟪v, B x v⟫_ℝ) μ) (v : Euclidean n) :
    ⟪v, polarizedDerivative (fun w => ∫ x, ⟪w, B x w⟫_ℝ ∂μ) v⟫_ℝ =
      ∫ x, ⟪v, B x v⟫_ℝ ∂μ := by
  have hi : Integrable B μ := by
    have h := integrable_polarizedDerivative μ (fun x w => ⟪w, B x w⟫_ℝ)
      (fun i => hint _) (fun i j => hint _)
    simpa only [polarizedDerivative_quadratic_form _ (hB _)] using h
  let S := ∫ x, B x ∂μ
  have hquad (w z : Euclidean n) : ⟪w, S z⟫_ℝ = ∫ x, ⟪w, B x z⟫_ℝ ∂μ := by
    dsimp only [S]
    rw [ContinuousLinearMap.integral_apply hi z]
    exact ((innerSL ℝ w).integral_comp_comm
      ((ContinuousLinearMap.apply ℝ (Euclidean n) z).integrable_comp hi)).symm
  have hsym : S.IsSymmetric := by
    intro w z
    change ⟪S w, z⟫_ℝ = ⟪w, S z⟫_ℝ
    rw [real_inner_comm, hquad, hquad]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      exact (real_inner_comm _ _).trans ((hB x) w z)
  have he : (fun w => ∫ x, ⟪w, B x w⟫_ℝ ∂μ) = fun w => ⟪w, S w⟫_ℝ :=
    funext fun w => (hquad w w).symm
  rw [he, polarizedDerivative_quadratic_form S hsym, hquad]

/-- One finite L1 budget controls every polarized integral operator. -/
theorem exists_polarized_integral_bound (g : Euclidean n → X → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : X → ℝ) (a : ℝ), 0 ≤ a →
      (∀ v, |∫ x, k x * g v x ∂μ| ≤ a * ∫ x, |g v x| ∂μ) →
      ‖polarizedDerivative (fun v => ∫ x, k x * g v x ∂μ)‖ ≤ C * a := by
  classical
  let m := fun v : Euclidean n => ∫ x, |g v x| ∂μ
  have hm (v) : 0 ≤ m v := integral_nonneg fun x => abs_nonneg _
  let B := 1 + (∑ i : Fin n, m (EuclideanSpace.single i 1)) +
    ∑ i : Fin n, ∑ j : Fin n, m (EuclideanSpace.single i 1 + EuclideanSpace.single j 1)
  have hS : 0 ≤ ∑ i : Fin n, m (EuclideanSpace.single i 1) := Finset.sum_nonneg fun _ _ => hm _
  have hP : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      m (EuclideanSpace.single i 1 + EuclideanSpace.single j 1) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hm _
  have hB : 0 < B := by dsimp only [B]; linarith
  have hs (i : Fin n) : m (EuclideanSpace.single i 1) ≤ B := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hm (EuclideanSpace.single j 1))
      (Finset.mem_univ i)
    dsimp only [B]
    linarith
  have hp (i j : Fin n) : m (EuclideanSpace.single i 1 + EuclideanSpace.single j 1) ≤ B := by
    have hh := Finset.single_le_sum
      (fun l (_ : l ∈ Finset.univ) => hm (EuclideanSpace.single i 1 + EuclideanSpace.single l 1))
      (Finset.mem_univ j)
    have hh' := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) =>
      Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => hm (EuclideanSpace.single l 1 + EuclideanSpace.single k 1)))
      (Finset.mem_univ i)
    dsimp only [B]
    linarith
  refine ⟨(n : ℝ) ^ 2 * (3 / 2 * B) + 1, by positivity, ?_⟩
  intro k a ha hb
  have ht := polarizedDerivative_norm_le (fun v => ∫ x, k x * g v x ∂μ) (mul_nonneg ha hB.le)
    (fun i => (hb _).trans (mul_le_mul_of_nonneg_left (hs i) ha))
    (fun i j => (hb _).trans (mul_le_mul_of_nonneg_left (hp i j) ha))
  apply ht.trans
  nlinarith only [ha]

end RegularPointCoordinates

end

end OAI
