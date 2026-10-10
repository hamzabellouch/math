import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDirichletLinearity
import Mathlib.Topology.ContinuousMap.Bounded.Normed

namespace OAI

/-! The radial Dirichlet inverse as a bounded positive operator. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

def radialClamp (R r : ℝ) : ℝ := max 0 (min R r)

theorem continuous_radialClamp (R : ℝ) : Continuous (radialClamp R) := by
  unfold radialClamp
  fun_prop

theorem radialClamp_mem (R r : ℝ) (hR : 0 ≤ R) : radialClamp R r ∈ Icc 0 R := by
  exact ⟨le_max_left _ _,max_le hR (min_le_left _ _)⟩

theorem radialClamp_eq (R r : ℝ) (hr : r ∈ Icc 0 R) : radialClamp R r=r := by
  simp only [radialClamp,min_eq_right hr.2,max_eq_right hr.1]

theorem bounded_radialDirichletKernel (R : ℝ) (hR : 0 ≤ R) (f : ℝ →ᵇ ℝ) (r : ℝ) :
    ‖radialDirichletKernel R f (radialClamp R r)‖ ≤ (R^2/24)*‖f‖ := by
  obtain ⟨hr,hrR⟩ := radialClamp_mem R r hR
  calc
    _ ≤ ‖f‖*(R^2-(radialClamp R r)^2)/24 :=
      radialDirichletKernel_norm_le f R ‖f‖ _ hr hrR (fun t _ => f.norm_coe_le_norm t)
    _ ≤ ‖f‖*R^2/24 := by
      gcongr
      exact sub_le_self _ (sq_nonneg _)
    _ = _ := by ring

noncomputable def boundedRadialGreen (R : ℝ) (hR : 0 ≤ R) (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun r => radialDirichletKernel R f (radialClamp R r))
    ((continuous_radialDirichletKernel R f f.continuous).comp (continuous_radialClamp R))
    ((R^2/24)*‖f‖) (bounded_radialDirichletKernel R hR f)

theorem boundedRadialGreen_norm (R : ℝ) (hR : 0 ≤ R) (f : ℝ →ᵇ ℝ) :
    ‖boundedRadialGreen R hR f‖ ≤ (R^2/24)*‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  exact bounded_radialDirichletKernel R hR f

noncomputable def radialGreenOperator (R : ℝ) (hR : 0 ≤ R) : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := boundedRadialGreen R hR
      map_add' := by
        intro f g
        apply BoundedContinuousFunction.ext
        intro r
        exact radialDirichletKernel_add R _ f g f.continuous g.continuous
      map_smul' := by
        intro c f
        apply BoundedContinuousFunction.ext
        intro r
        exact radialDirichletKernel_smul R _ c f }
    (R^2/24) (boundedRadialGreen_norm R hR)

theorem radialGreenOperator_apply (R r : ℝ) (hR : 0 ≤ R) (f : ℝ →ᵇ ℝ) :
    radialGreenOperator R hR f r=radialDirichletKernel R f (radialClamp R r) := rfl

theorem radialGreenOperator_nonneg (R : ℝ) (hR : 0 ≤ R) (f : ℝ →ᵇ ℝ)
    (hf : ∀ r ∈ Icc 0 R, 0 ≤ f r) (r : ℝ) :
    0 ≤ radialGreenOperator R hR f r := by
  obtain ⟨hr,hrR⟩ := radialClamp_mem R r hR
  exact radialDirichletKernel_nonneg R _ f hr hrR hf

end DefocusingNLS

end OAI
