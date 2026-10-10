import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialMainConstant
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletedPoleBound

namespace OAI

/-! The actual radial pole has the same rapid height decay, up to a fixed
constant. This uses only the proved nonvanishing of the arithmetic scalar. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem UniformLogWeights.cubicTheta_completed_pole_bound
    {ι : Type*} {W : ι→ℝ→ℂ} (h : UniformLogWeights W) (D : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ i r, primary r → ∀ X : ℝ, 0<X →
      ∀ T : ℝ, 0<T → ∀ t : ℝ, T≤|t| →
      ‖mellinPhase t X*cubicThetaActualCompletedRadialMain r
        (fun x => W i x*mellinPhase t x) X‖ ≤
        C*X^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D := by
  obtain ⟨K,hK,hbound⟩ := h.metaplectic_completed_pole_bound D
  have hB : 0<‖cubicThetaArithmeticBaseScalar‖ := norm_pos_iff.mpr cubicThetaArithmeticBaseScalar_ne_zero
  refine ⟨K/‖cubicThetaArithmeticBaseScalar‖,by positivity,?_⟩
  intro i r hr X hX T hT t ht
  have he : (mellinPhase t X*cubicThetaActualCompletedRadialMain r
      (fun x => W i x*mellinPhase t x) X)*star cubicThetaArithmeticBaseScalar=
      mellinPhase t X*metaplecticMain r 0 (fun x => W i x*mellinPhase t x) X := by
    rw [mul_assoc,cubicThetaActualCompletedRadialMain_mul_base hr _ hX]
  have hn : ‖mellinPhase t X*cubicThetaActualCompletedRadialMain r
      (fun x => W i x*mellinPhase t x) X‖=
      ‖mellinPhase t X*metaplecticMain r 0 (fun x => W i x*mellinPhase t x) X‖/
        ‖cubicThetaArithmeticBaseScalar‖ := by
    apply (eq_div_iff hB.ne').mpr
    simpa only [norm_mul,norm_star] using congrArg (fun z : ℂ => ‖z‖) he
  rw [hn]
  calc
    _ ≤ (K*X^(5/6:ℝ)*norm r^(-1/6:ℝ)/T^D)/‖cubicThetaArithmeticBaseScalar‖ :=
      div_le_div_of_nonneg_right (hbound i r hr X hX T hT t ht) hB.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
