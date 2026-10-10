import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousTranslation
import Mathlib.Analysis.InnerProductSpace.Dual

namespace OAI

/-! # Norm-continuity of actual point observation

The Fourier translation isometry makes all evaluation dual norms equal.
Physical continuity gives weak continuity of their Riesz vectors; the
constant norm and the Hilbert norm-square identity give norm-continuity.
-/

open Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem continuous_homogeneousPointEvaluation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    Continuous (homogeneousPointEvaluation a k ha ha1 hk) := by
  let L : E → StrongDual ℂ (HomogeneousY a k) := homogeneousPointEvaluation a k ha ha1 hk
  let K : E → HomogeneousY a k := fun y => (InnerProductSpace.toDual ℂ _).symm (L y)
  let c := ‖L 0‖
  have hKn (y : E) : ‖K y‖ = c := by
    rw [show ‖K y‖ = ‖L y‖ from (InnerProductSpace.toDual ℂ _).symm.norm_map (L y)]
    exact homogeneousPointEvaluation_norm_const a k ha ha1 hk y
  have hinner (y x : E) : inner ℂ (K y) (K x) = L y (K x) :=
    InnerProductSpace.toDual_symm_apply
  have hK : Continuous K := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have heval : Continuous (fun y : E => (L y (K x)).re) :=
      Complex.continuous_re.comp (homogeneousPhysicalCLM a k ha ha1 hk (K x)).continuous
    have hsq : Continuous (fun y : E => ‖K y - K x‖ ^ 2) := by
      simp_rw [norm_sub_sq (𝕜 := ℂ), hKn, hinner]
      exact (continuous_const.sub (heval.const_mul 2)).add continuous_const
    have hnorm : Continuous (fun y : E => ‖K y - K x‖) := by
      convert Real.continuous_sqrt.comp hsq using 1
      funext y
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_self, norm_zero] using (hnorm.continuousAt (x := x)).tendsto
  have heq : L = fun y => InnerProductSpace.toDual ℂ (HomogeneousY a k) (K y) := by
    funext y
    exact ((InnerProductSpace.toDual ℂ _).apply_symm_apply (L y)).symm
  change Continuous L
  rw [heq]
  exact (InnerProductSpace.toDual ℂ _).continuous.comp hK

end DefocusingNLS

end OAI
