import OAI.Geometry.Perimeter.Regularity.PlaneWindowLift

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def normalTestLift (v : Euc n) (ψ : normalPlane v → ℝ) (χ : ℝ → ℝ) (x : Euc n) : ℝ :=
  ψ (normalProjection v x)*χ (inner ℝ v x)

theorem normalTestLift_contDiff {v : Euc n} {ψ : normalPlane v → ℝ} {χ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (normalTestLift v ψ χ) :=
  (hψ.comp (normalProjection v).contDiff).mul
    (hχ.comp (contDiff_const.inner ℝ contDiff_id))

theorem normalTestLift_tsupport {v : Euc n} (hv : ‖v‖=1)
    (ψ : normalPlane v → ℝ) (χ : ℝ → ℝ) {r s : ℝ}
    (hr : Function.support ψ ⊆ Metric.closedBall 0 r)
    (hs : Function.support χ ⊆ Metric.closedBall 0 s) :
    tsupport (normalTestLift v ψ χ) ⊆ Metric.closedBall 0 (r+s) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hp : ψ (normalProjection v x)≠0 ∧ χ (inner ℝ v x)≠0 := mul_ne_zero_iff.mp hx
  have h1 := hr hp.1
  have h2 := hs hp.2
  rw [Metric.mem_closedBall,dist_zero_right] at h1 h2 ⊢
  calc
    ‖x‖ = ‖(normalProjection v x:Euc n)+inner ℝ v x•v‖ :=
      congrArg norm (normalProjection_decomposition hv x).symm
    _ ≤ ‖(normalProjection v x:Euc n)‖+‖inner ℝ v x•v‖ := norm_add_le _ _
    _ ≤ r+s := by simpa only [Submodule.norm_coe,norm_smul,hv,mul_one] using add_le_add h1 h2

theorem gradient_normalProjection_comp {v : Euc n} {ψ : normalPlane v → ℝ}
    (hψ : Differentiable ℝ ψ) (x : Euc n) :
    gradient (fun z ↦ ψ (normalProjection v z)) x=
      ((gradient ψ (normalProjection v x):normalPlane v):Euc n) := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left]
  have hd : HasFDerivAt (fun z ↦ ψ (normalProjection v z))
      ((fderiv ℝ ψ (normalProjection v x)).comp (normalProjection v)) x :=
    (hψ _).hasFDerivAt.comp x (normalProjection v).hasFDerivAt
  rw [hd.fderiv]
  rw [←(normalPlane v).inner_orthogonalProjectionOnto_eq_of_mem_left,inner_gradient_left]
  rfl

theorem normalTestLift_gradient {v : Euc n} {ψ : normalPlane v → ℝ} {χ : ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) {b : ℝ}
    (hχone : ∀ s : ℝ, |s|<b → χ s=1) {x : Euc n} (hx : |inner ℝ v x|<b) :
    gradient (normalTestLift v ψ χ) x=
      ((gradient ψ (normalProjection v x):normalPlane v):Euc n) := by
  have he : normalTestLift v ψ χ =ᶠ[𝓝 x] fun z ↦ ψ (normalProjection v z) := by
    filter_upwards [((continuous_const.inner continuous_id).abs.continuousAt).eventually
      (gt_mem_nhds hx)] with z hz
    change |inner ℝ v z|<b at hz
    dsimp only [normalTestLift]
    rw [hχone _ hz,mul_one]
  rw [show gradient (normalTestLift v ψ χ) x=gradient (fun z ↦ ψ (normalProjection v z)) x from
    congrArg (InnerProductSpace.toDual ℝ (Euc n)).symm (he.fderiv_eq (𝕜 := ℝ))]
  exact gradient_normalProjection_comp hψ x

theorem normalTestLift_gradient_zero {v : Euc n} {ψ : normalPlane v → ℝ} {χ : ℝ → ℝ}
    {x : Euc n} (hx : normalProjection v x∉tsupport ψ) :
    gradient (normalTestLift v ψ χ) x=0 := by
  have he : normalTestLift v ψ χ =ᶠ[𝓝 x] fun _ ↦ (0:ℝ) := by
    filter_upwards [(normalProjection v).continuous.continuousAt.eventually
      ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hx)] with z hz
    simp only [normalTestLift,image_eq_zero_of_notMem_tsupport hz,zero_mul]
  rw [show gradient (normalTestLift v ψ χ) x=gradient (fun _ : Euc n ↦ (0:ℝ)) x from
    congrArg (InnerProductSpace.toDual ℝ (Euc n)).symm (he.fderiv_eq (𝕜 := ℝ))]
  simp [gradient]

end RPISingularHarnack

end

end OAI
