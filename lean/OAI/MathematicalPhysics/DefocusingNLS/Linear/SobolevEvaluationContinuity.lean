import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevTorus
import Mathlib.Analysis.InnerProductSpace.Dual

namespace OAI

/-! # Norm continuity of Sobolev point evaluation -/

open Filter Topology

namespace DefocusingNLS

theorem continuous_sobolevPointEvaluation (k : ℝ) (hk : 6 < k) :
    Continuous (sobolevPointEvaluation k hk) := by
  let K := sobolevPointObservationVector k hk
  have hKn (x : SchrodingerTorus) : ‖K x‖ = ‖sobolevObservationVector k hk‖ :=
    sobolevPointObservationVector_norm k hk x
  have hinner (y x : SchrodingerTorus) :
      inner ℂ (K y) (K x) = sobolevTorusFunction k (K x) y :=
    (sobolevTorusFunction_apply k hk y (K x)).symm
  have hK : Continuous K := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hsq : Continuous (fun y => ‖K y - K x‖ ^ 2) := by
      simp_rw [norm_sub_sq (𝕜 := ℂ), hKn, hinner]
      exact (continuous_const.sub
        ((Complex.continuous_re.comp (sobolevTorusFunction k (K x)).continuous).const_mul 2)).add
          continuous_const
    have hn : Continuous (fun y => ‖K y - K x‖) := by
      convert Real.continuous_sqrt.comp hsq using 1
      funext y
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_self, norm_zero] using (hn.continuousAt (x := x)).tendsto
  exact (innerSL ℂ).continuous.comp hK

end DefocusingNLS

end OAI
