import OAI.Geometry.Perimeter.Regularity.GraphNormal
import OAI.Geometry.Perimeter.Regularity.GraphTestLift

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def graphFluxWeight (v : Euc n) (f ψ : normalPlane v → ℝ) (y : normalPlane v) : ℝ :=
  inner ℝ (gradient f y) (gradient ψ y)/graphAreaFactor v f y

theorem graphFluxWeight_zero {v : Euc n} {f ψ : normalPlane v → ℝ}
    {y : normalPlane v} (hy : y∉tsupport ψ) : graphFluxWeight v f ψ y=0 := by
  simp [graphFluxWeight,gradient,fderiv_of_notMem_tsupport ℝ hy]

theorem graphFluxWeight_tsupport {v : Euc n} (f ψ : normalPlane v → ℝ) :
    tsupport (graphFluxWeight v f ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro y hy
  by_contra hn
  exact hy (graphFluxWeight_zero hn)

theorem graphFluxWeight_continuous {v : Euc n} (hv : ‖v‖=1)
    {f ψ : normalPlane v → ℝ} (hf : ContDiffOn ℝ 1 f (Metric.ball 0 (1/4)))
    (hψ : ContDiff ℝ ∞ ψ) (hsψ : tsupport ψ ⊆ Metric.ball 0 (1/4)) :
    Continuous (graphFluxWeight v f ψ) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hy : y∈tsupport ψ
  · have hgf : ContinuousAt (gradient f) y :=
      (InnerProductSpace.toDual ℝ (normalPlane v)).symm.continuous.continuousAt.comp
        ((hf.contDiffAt (Metric.isOpen_ball.mem_nhds (hsψ hy))).continuousAt_fderiv (by norm_num))
    have hgp : ContinuousAt (gradient ψ) y :=
      (InnerProductSpace.toDual ℝ (normalPlane v)).symm.continuous.continuousAt.comp
        (hψ.contDiffAt.continuousAt_fderiv (by simp))
    have hgq : ContinuousAt (graphAreaFactor v f) y := by
      exact (continuousAt_const.sub ((normalPlane v).subtypeL.continuous.continuousAt.comp hgf)).norm
    exact (hgf.inner hgp).div hgq (graphAreaFactor_pos hv f y).ne'
  · apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hy] with z hz
    exact graphFluxWeight_zero hz

theorem graphTest_tangential_flux {v : Euc n} (hv : ‖v‖=1)
    {E : Set (Euc n)} {f ψ : normalPlane v → ℝ} {χ : ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) {b : ℝ} (hχone : ∀ s : ℝ, |s|<b → χ s=1)
    {x : Euc n} (hx : |inner ℝ v x|<b)
    (hN : approximateNormal E x=(graphAreaFactor v f (normalProjection v x))⁻¹ •
      graphNormalVector v f (normalProjection v x)) :
    inner ℝ (tangentialGradient E (normalTestLift v ψ χ) x) v=
      graphFluxWeight v f ψ (normalProjection v x)*inner ℝ (approximateNormal E x) v := by
  rw [tangentialGradient,normalTestLift_gradient hψ hχone hx,inner_sub_left,
    real_inner_smul_left,hN,real_inner_smul_left,graphNormalVector_inner_normal hv,mul_one]
  have hz : inner ℝ ((gradient ψ (normalProjection v x):normalPlane v):Euc n) v=0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp (gradient ψ (normalProjection v x)).property
  simp only [real_inner_smul_right,graphNormalVector,inner_sub_right,hz,zero_sub,
    Submodule.coe_inner,graphFluxWeight,div_eq_mul_inv]
  conv_lhs => rw [real_inner_comm]
  ring

end RPISingularHarnack

end

end OAI
