import OAI.Geometry.RCD.Coordinates.GramNormalization
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! # Adjoint coordinate frames from exact mean normalization -/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The pointwise coordinate change associated to a coefficient frame. -/
def coordinateFrame (A : E ≃L[ℝ] E) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse' A.toContinuousLinearMap.adjoint
    A.symm.toContinuousLinearMap.adjoint
    (by rw [← ContinuousLinearMap.adjoint_comp]; simp [ContinuousLinearMap.adjoint_id])
    (by rw [← ContinuousLinearMap.adjoint_comp]; simp [ContinuousLinearMap.adjoint_id])

@[simp] theorem coordinateFrame_apply (A : E ≃L[ℝ] E) (v : E) :
    coordinateFrame A v = A.toContinuousLinearMap.adjoint v := rfl

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) (U : E →L[ℝ] SobolevSpace μ hQ)

/-- A relative mean bound controls the adjoint coordinate frames without
an absolute lower eigenvalue assumption. -/
theorem coordinateFrame_le_of_mean_comparison
    (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (A B : E ≃L[ℝ] E)
    (hA : IsExactMeanNormalization μ hQ U s hs A)
    (hB : IsExactMeanNormalization μ hQ U t ht B)
    (hcompare : ∀ v, (1 / 4 : ℝ) * ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ ≤
      ⟪v, sobolevMeanGram μ hQ U t ht v⟫_ℝ) (w : E) :
    ‖coordinateFrame B w‖ ≤ 2 * ‖coordinateFrame A w‖ := by
  let T : E →L[ℝ] E := A.symm.toContinuousLinearMap.comp B.toContinuousLinearMap
  have hT : ‖T‖ ≤ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    have h := hcompare (B v)
    rw [meanGram_energy_of_exact_normalization μ hQ U s hs A hA,
      meanGram_energy_of_exact_normalization μ hQ U t ht B hB,
      B.symm_apply_apply] at h
    change ‖A.symm (B v)‖ ≤ 2 * ‖v‖
    nlinarith only [h, norm_nonneg (A.symm (B v)), norm_nonneg v,
      sq_nonneg (‖A.symm (B v)‖ - 2 * ‖v‖)]
  have hid : T.adjoint.comp A.toContinuousLinearMap.adjoint = B.toContinuousLinearMap.adjoint := by
    rw [← ContinuousLinearMap.adjoint_comp]
    congr 1
    ext v
    simp [T]
  change ‖B.toContinuousLinearMap.adjoint w‖ ≤ 2 * ‖A.toContinuousLinearMap.adjoint w‖
  rw [← hid, ContinuousLinearMap.comp_apply]
  exact (T.adjoint.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (by simpa using hT) (norm_nonneg _))

/-- A uniform upper bound for raw mean energy gives a uniform lower bound
for every exact adjoint coordinate frame. -/
theorem norm_le_coordinateFrame_of_mean_upper
    (s : Set X) (hs : MeasurableSet s) (A : E ≃L[ℝ] E)
    (hA : IsExactMeanNormalization μ hQ U s hs A)
    {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ v, ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ ≤ C ^ 2 * ‖v‖ ^ 2)
    (w : E) : ‖w‖ ≤ C * ‖coordinateFrame A w‖ := by
  have hn : ‖A.symm.toContinuousLinearMap‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro v
    have h := hupper v
    rw [meanGram_energy_of_exact_normalization μ hQ U s hs A hA] at h
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
      (by simpa only [mul_pow, ContinuousLinearEquiv.coe_coe] using h)
  have hid : A.symm.toContinuousLinearMap.adjoint.comp A.toContinuousLinearMap.adjoint =
      ContinuousLinearMap.id ℝ E := by
    rw [← ContinuousLinearMap.adjoint_comp]
    simp [ContinuousLinearMap.adjoint_id]
  have h := A.symm.toContinuousLinearMap.adjoint.le_opNorm (coordinateFrame A w)
  have hcancel : A.symm.toContinuousLinearMap.adjoint (coordinateFrame A w) = w := by
    simpa only [coordinateFrame_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using congrArg (fun L : E →L[ℝ] E => L w) hid
  rw [hcancel] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by simpa using hn) (norm_nonneg _))

end RegularPointCoordinates

end

end OAI
