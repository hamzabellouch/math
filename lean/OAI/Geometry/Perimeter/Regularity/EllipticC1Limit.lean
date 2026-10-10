import OAI.Geometry.Perimeter.Regularity.EllipticContraction
import OAI.Geometry.Perimeter.Regularity.EllipticCompactGradient

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem C1_limit_of_uniform_gradients {f : ℕ → Euc n → ℝ} {g : Euc n → ℝ}
    (hf : ∀ i, ContDiff ℝ 1 (f i)) {p : Euc n} {r : ℝ}
    {W : Euc n → Euc n} (hW : ContinuousOn W (Metric.closedBall p r))
    (hgrad : TendstoUniformlyOn (fun i ↦ gradient (f i)) W atTop (Metric.closedBall p r))
    (hlim : ∀ x∈Metric.ball p r, Tendsto (fun i ↦ f i x) atTop (𝓝 (g x))) :
    ContDiffOn ℝ 1 g (Metric.ball p r) ∧ ∀ x∈Metric.ball p r, gradient g x=W x := by
  let D : Euc n → Euc n →L[ℝ] ℝ := fun x ↦ InnerProductSpace.toDual ℝ (Euc n) (W x)
  have hDlim : TendstoUniformlyOn (fun i ↦ fderiv ℝ (f i)) D atTop (Metric.ball p r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hgrad) ε hε] with i hi x hx
    have hh := hi x (Metric.ball_subset_closedBall hx)
    change dist (InnerProductSpace.toDual ℝ (Euc n) (W x)) (fderiv ℝ (f i) x)<ε
    rw [show fderiv ℝ (f i) x=InnerProductSpace.toDual ℝ (Euc n) (gradient (f i) x) from
      (LinearIsometryEquiv.apply_symm_apply _ _).symm,
      (InnerProductSpace.toDual ℝ (Euc n)).isometry.dist_eq]
    exact hh
  have hD (x : Euc n) (hx : x∈Metric.ball p r) : HasFDerivAt g (D x) x :=
    hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hDlim
      (fun i x _ ↦ (hf i).differentiable (by simp) x |>.hasFDerivAt) hlim hx
  constructor
  · change ContDiffOn ℝ (0+1) g (Metric.ball p r)
    rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn Metric.isOpen_ball.uniqueDiffOn]
    refine ⟨by simp,D,?_,fun x hx ↦ (hD x hx).hasFDerivWithinAt⟩
    apply contDiffOn_zero.mpr
    exact (InnerProductSpace.toDual ℝ (Euc n)).continuous.comp_continuousOn
      (hW.mono Metric.ball_subset_closedBall)
  · intro x hx
    rw [gradient,(hD x hx).fderiv]
    exact LinearIsometryEquiv.symm_apply_apply _ _

 theorem C1_limit_of_geometric_gradient_estimates {f : ℕ → Euc n → ℝ} {g : Euc n → ℝ}
    (hf : ∀ i, ContDiff ℝ 1 (f i)) {p : Euc n} {r θ R C B : ℝ}
    (hθ : 0<θ) (hR : 0<R)
    (hb : ∀ i x, x∈Metric.closedBall p r → ‖gradient (f i) x‖≤B)
    (hmod : ∀ i j x, x∈Metric.closedBall p r → ∀ y, y∈Metric.closedBall p r →
      dist x y≤θ^j*R → ‖gradient (f i) x-gradient (f i) y‖≤C*(1/2)^j)
    (hlim : ∀ x∈Metric.ball p r, Tendsto (fun i ↦ f i x) atTop (𝓝 (g x))) :
    ContDiffOn ℝ 1 g (Metric.ball p r) ∧
      ∀ j x, x∈Metric.ball p r → ∀ y, y∈Metric.ball p r → dist x y≤θ^j*R →
        ‖gradient g x-gradient g y‖≤C*(1/2)^j := by
  obtain ⟨W,hW,σ,hσ,hconv⟩ := compact_field_subsequence (isCompact_closedBall p r)
    (fun i ↦ (gradient_continuous_C1 (hf i)).continuousOn) hθ hR hb hmod
  obtain ⟨hg,hgW⟩ := C1_limit_of_uniform_gradients (fun i ↦ hf (σ i)) hW hconv
    (fun x hx ↦ (hlim x hx).comp hσ.tendsto_atTop)
  refine ⟨hg,fun j x hx y hy hxy ↦ ?_⟩
  rw [hgW x hx,hgW y hy]
  have ht := ((hconv.tendsto_at (Metric.ball_subset_closedBall hx)).sub
    (hconv.tendsto_at (Metric.ball_subset_closedBall hy))).norm
  exact le_of_tendsto ht (Eventually.of_forall (fun i ↦
    hmod (σ i) j x (Metric.ball_subset_closedBall hx) y (Metric.ball_subset_closedBall hy) hxy))

end RPISingularHarnack

end

end OAI
