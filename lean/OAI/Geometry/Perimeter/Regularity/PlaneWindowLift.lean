import OAI.Geometry.Perimeter.Regularity.PlaneLaplacian

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace ContDiff
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n m : ℕ} {v : Euc n}

theorem normalProjection_decomposition (hv : ‖v‖=1) (x : Euc n) :
    (normalProjection v x:Euc n)+inner ℝ v x•v=x := by
  obtain ⟨⟨y,s⟩,rfl⟩ := (normalCoordinates v hv).surjective x
  simp only [normalCoordinates_apply,normalProjection_fiber,normal_fiber_inner hv]

@[simp] theorem chartInclusion_projection (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) (x : Euc n) :
    chartInclusion e (chartProjection e x) = (normalProjection v x:Euc n) := by
  change ((e (e.symm (normalProjection v x))):Euc n) = _
  rw [e.apply_symm_apply]

@[simp] theorem norm_chartInclusion (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) (y : Euc m) :
    ‖chartInclusion e y‖=‖y‖ := e.norm_map y

def planeWindowLift (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) (ψ : Euc m → ℝ)
    (χ : ℝ → ℝ) (x : Euc n) : ℝ := ψ (chartProjection e x)*χ (inner ℝ v x)

theorem planeWindowLift_contDiff (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    {ψ : Euc m → ℝ} {χ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (planeWindowLift e ψ χ) :=
  (hψ.comp (chartProjection e).contDiff).mul
    (hχ.comp (contDiff_const.inner ℝ contDiff_id))

theorem planeWindowLift_tsupport (hv : ‖v‖=1) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    (ψ : Euc m → ℝ) (χ : ℝ → ℝ) {r s : ℝ}
    (hr : Function.support ψ ⊆ Metric.closedBall 0 r)
    (hs : Function.support χ ⊆ Metric.closedBall 0 s) :
    tsupport (planeWindowLift e ψ χ) ⊆ Metric.closedBall 0 (r+s) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hprod : ψ (chartProjection e x)≠0 ∧ χ (inner ℝ v x)≠0 := mul_ne_zero_iff.mp hx
  have h1 := hr hprod.1
  have h2 := hs hprod.2
  rw [Metric.mem_closedBall,dist_zero_right] at h1 h2 ⊢
  have he : chartInclusion e (chartProjection e x)+inner ℝ v x•v=x := by
    rw [chartInclusion_projection]; exact normalProjection_decomposition hv x
  calc
    ‖x‖=‖chartInclusion e (chartProjection e x)+inner ℝ v x•v‖ := congrArg norm he.symm
    _ ≤ ‖chartInclusion e (chartProjection e x)‖+‖inner ℝ v x•v‖ := norm_add_le _ _
    _ ≤ r+s := by simpa only [norm_chartInclusion,norm_smul,hv,mul_one] using add_le_add h1 h2

theorem planeWindowLift_hasCompactSupport (hv : ‖v‖=1)
    (e : Euc m ≃ₗᵢ[ℝ] normalPlane v) {ψ : Euc m → ℝ} {χ : ℝ → ℝ}
    (hψ : HasCompactSupport ψ) (hχ : HasCompactSupport χ) :
    HasCompactSupport (planeWindowLift e ψ χ) := by
  obtain ⟨r,hr⟩ := hψ.isBounded.subset_closedBall (0:Euc m)
  obtain ⟨s,hs⟩ := hχ.isBounded.subset_closedBall (0:ℝ)
  exact (isCompact_closedBall 0 (r+s)).of_isClosed_subset (isClosed_tsupport _)
    (planeWindowLift_tsupport hv e ψ χ (subset_closure.trans hr) (subset_closure.trans hs))

theorem gradient_eventuallyEq {f g : Euc n → ℝ} {x : Euc n}
    (h : f=ᶠ[𝓝 x] g) : gradient f=ᶠ[𝓝 x] gradient g := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (InnerProductSpace.toDual ℝ (Euc n)).symm hy

theorem planeWindowLift_laplacian (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    {ψ : Euc m → ℝ} {χ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {b : ℝ}
    (hχone : ∀ s : ℝ, |s|<b → χ s=1) {x : Euc n} (hx : |inner ℝ v x|<b) :
    planarDivergence v (gradient (planeWindowLift e ψ χ)) x =
      divergence (gradient ψ) (chartProjection e x) := by
  have he : planeWindowLift e ψ χ =ᶠ[𝓝 x] fun z ↦ ψ (chartProjection e z) := by
    filter_upwards [((continuous_const.inner continuous_id).abs.continuousAt).eventually
      (gt_mem_nhds hx)] with z hz
    change |inner ℝ v z|<b at hz
    dsimp only [planeWindowLift]
    rw [hχone _ hz,mul_one]
  have hd := (gradient_eventuallyEq he).fderiv_eq (𝕜 := ℝ)
  rw [← planar_laplacian_chart_lift hψ e x]
  simp only [planarDivergence,divergence,hd]

end RPISingularHarnack

end

end OAI
