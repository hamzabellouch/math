import Mathlib.Analysis.Calculus.ContDiff.Convolution
import OAI.Geometry.NodalSets.Elliptic.RealCompactTestDerivative

namespace OAI

namespace Yau
open MeasureTheory Set ContinuousLinearMap
open scoped ContDiff Convolution
noncomputable section

theorem real_convolution_coordPartial {n : ℕ} (u k : Coord n → ℝ)
    (hu : LocallyIntegrable u volume) (hk : ContDiff ℝ ∞ k)
    (hc : HasCompactSupport k) (x : Coord n) (i : Fin n) :
    coordPartial (u ⋆ k) x i = ∫ y, u y * coordPartial k (x-y) i := by
  unfold coordPartial
  rw [(hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hu (hk.of_le (by simp)) x).fderiv]
  exact convolution_precompR_apply (lsmul ℝ ℝ) hu
    (hc.fderiv ℝ) (hk.continuous_fderiv (by simp)) x (Pi.single i 1)

theorem real_weak_convolution_derivative {n : ℕ} (u g k : Coord n → ℝ)
    (hu : LocallyIntegrable u volume) (hk : ContDiff ℝ ∞ k)
    (hc : HasCompactSupport k) (i : Fin n)
    (hw : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ y, u y * coordPartial psi y i) = -(∫ y, g y * psi y)) :
    (fun x ↦ coordPartial (u ⋆ k) x i) = g ⋆ k := by
  funext x
  let psi : Coord n → ℝ := fun y ↦ k (x-y)
  have hp : ContDiff ℝ ∞ psi := hk.comp (contDiff_const.sub contDiff_id)
  have hpc : HasCompactSupport psi :=
    hc.comp_homeomorph ((Homeomorph.neg (Coord n)).trans (Homeomorph.addLeft x))
  have hd (y : Coord n) : coordPartial psi y i = -coordPartial k (x-y) i := by
    unfold coordPartial
    have ht := (hk.differentiable (by simp) (x-y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    change HasFDerivAt psi _ y at ht
    rw [ht.fderiv]
    simp
  have he := hw psi hp hpc
  simp only [hd, mul_neg, integral_neg] at he
  rw [real_convolution_coordPartial u k hu hk hc, convolution_def]
  exact neg_injective he

theorem real_compact_convolution_smooth {n : ℕ} (u k : Coord n → ℝ)
    (hu : LocallyIntegrable u volume) (huc : HasCompactSupport u)
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) :
    ContDiff ℝ ∞ (u ⋆ k) ∧ HasCompactSupport (u ⋆ k) :=
  ⟨hkc.contDiff_convolution_right (lsmul ℝ ℝ) hu hk,
    huc.convolution (lsmul ℝ ℝ) hkc⟩

end
end Yau

end OAI
