import Mathlib
import OAI.Geometry.NearbyLagrangian.HomogeneousFunctions
import OAI.Geometry.NearbyLagrangian.Radialization

namespace OAI

/-! Smooth approximation with uniform first-jet control. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.C1Approx

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma lsmul_precompR :
    (lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).precompR E =
      (lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] F)) := by
  apply ContinuousLinearMap.ext
  intro r
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousLinearMap.ext
  intro x
  rfl

lemma exists_contDiff_jet_dist_lt {f : E → F} (hf : ContDiff ℝ 1 f)
    (hs : HasCompactSupport f) {K : Set E} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ x ∈ K,
      dist (g x) (f x) < ε ∧ dist (fderiv ℝ g x) (fderiv ℝ f x) < ε := by
  borelize E
  let μ : Measure E := MeasureTheory.Measure.addHaar
  have hc : Continuous (fun x => (f x, fderiv ℝ f x)) :=
    hf.continuous.prodMk (hf.continuous_fderiv (by simp))
  have hu : UniformContinuousOn (fun x => (f x, fderiv ℝ f x)) (cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp hu (ε/2) (half_pos hε)
  let r := min 1 δ
  have hr : 0 < r := lt_min one_pos hδ
  let φ : ContDiffBump (0 : E) := ⟨r/2, r, half_pos hr, half_lt_self hr⟩
  let g : E → F := φ.normed μ ⋆[lsmul ℝ ℝ, μ] f
  have hgs : ContDiff ℝ ∞ g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      (hf.continuous.locallyIntegrable (μ := μ))
  have hD : ∀ x, fderiv ℝ g x =
      (φ.normed μ ⋆[lsmul ℝ ℝ, μ] fderiv ℝ f) x := by
    intro x
    have hh := hs.hasFDerivAt_convolution_right (lsmul ℝ ℝ)
      ((φ.contDiff_normed (μ := μ) (n := 0)).continuous.locallyIntegrable (μ := μ)) hf x
    rw [lsmul_precompR] at hh
    exact hh.fderiv
  refine ⟨g, hgs, ?_⟩
  intro x hx
  have hb : ∀ y ∈ ball x r,
      dist (f y) (f x) ≤ ε/2 ∧ dist (fderiv ℝ f y) (fderiv ℝ f x) ≤ ε/2 := by
    intro y hy
    have hyb : dist y x < 1 ∧ dist y x < δ := lt_min_iff.mp hy
    have H := hd y (mem_cthickening_of_dist_le _ x _ _ hx hyb.1.le) x
      (self_subset_cthickening _ hx) hyb.2
    exact (max_le_iff.mp (by simpa only [Prod.dist_eq] using H.le))
  constructor
  · exact (φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
      (fun y hy => (hb y hy).1)).trans_lt (half_lt_self hε)
  · rw [hD]
    exact (φ.dist_normed_convolution_le
      (hf.continuous_fderiv (by simp)).aestronglyMeasurable
      (fun y hy => (hb y hy).2)).trans_lt (half_lt_self hε)

lemma exists_contDiff_jet_dist_lt_on {f : E → F} (hf : ContDiff ℝ 1 f)
    {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ x ∈ K,
      dist (g x) (f x) < ε ∧ dist (fderiv ℝ g x) (fderiv ℝ f x) < ε := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : E)
  let A : ℝ := max R 1
  have hA : 0 < A := zero_lt_one.trans_le (le_max_right _ _)
  let φ : ContDiffBump (0 : E) := ⟨A, A+1, hA, lt_add_one A⟩
  let f₀ : E → F := fun x => φ x • f x
  have hf₀ : ContDiff ℝ 1 f₀ := φ.contDiff.smul hf
  have hs₀ : HasCompactSupport f₀ := φ.hasCompactSupport.smul_right
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_jet_dist_lt hf₀ hs₀ hK hε
  refine ⟨g, hg, fun x hx => ?_⟩
  have hxb : x ∈ ball (0 : E) φ.rIn := by
    exact lt_of_lt_of_le (show dist x 0 < R from hR hx) (le_max_left R 1)
  have he : f₀ =ᶠ[nhds x] f := by
    filter_upwards [φ.eventuallyEq_one_of_mem_ball hxb] with y hy
    simp only [f₀, hy, Pi.one_apply, one_smul]
  simpa only [he.eq_of_nhds, he.fderiv_eq] using hgf x hx

end NearbyLagrangian.C1Approx

namespace NearbyLagrangian.AngularExtension

open scoped ContDiff Topology
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_smooth_homogeneous_approx {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (h0 : f 0 = 0) (hh : ∀ r : ℝ, 0 < r → ∀ x, f (r • x) = r^2 * f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ 1 g ∧ g 0 = 0 ∧
      (∀ r : ℝ, 0 < r → ∀ x, g (r • x) = r^2 * g x) ∧
      (∀ x ≠ 0, ContDiffAt ℝ ∞ g x) ∧
      ∀ x, ‖x‖ = 1 → ‖g x - f x‖ < ε ∧
        ‖fderiv ℝ g x - fderiv ℝ f x‖ < ε := by
  obtain ⟨g₀, hg₀, ha⟩ := C1Approx.exists_contDiff_jet_dist_lt_on hf
    (isCompact_sphere (0 : E) 1) (div_pos hε (by norm_num : (0:ℝ) < 8))
  refine ⟨radialize g₀, contDiff_one_radialize (fun x _ => hg₀.of_le (by simp) |>.contDiffAt),
    radialize_zero g₀, fun r hr x => radialize_homogeneous g₀ hr x,
    fun x hx => contDiffAt_radialize hx hg₀.contDiffAt, fun x hx => ?_⟩
  have H := ha x (by simpa only [Metric.mem_sphere, dist_zero_right] using hx)
  rw [dist_eq_norm] at H
  constructor
  · rw [radialize_on_unit _ hx]
    exact H.1.trans (by linarith)
  · have hd := norm_fderiv_radialize_sub_le hx
      (hf.differentiable one_ne_zero x) (hg₀.differentiable (by simp) x)
    rw [radialize_eq_of_degree_two h0 hh] at hd
    have HD : ‖fderiv ℝ g₀ x - fderiv ℝ f x‖ < ε / 8 := by
      simpa only [dist_eq_norm] using H.2
    linarith [H.1]

end NearbyLagrangian.AngularExtension

end

end OAI
