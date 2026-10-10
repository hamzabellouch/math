import OAI.Geometry.Kahler.HartogsCompletenessSupport

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology Metric
open scoped ContDiff NNReal
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs
private lemma scaled_fibre_lt (s : ℝ) (w : ℂ)
    (hw : Real.exp s * ‖w‖ ^ 2 < 1) : ‖Real.exp (s / 2) • w‖ < 1 := by
  have hsq := exp_half_sq s
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  nlinarith only [hw, hsq, norm_nonneg w, Real.exp_pos (s / 2)]

private lemma unscaled_fibre_lt (s : ℝ) (w : ℂ) (hw : ‖w‖ < 1) :
    Real.exp s * ‖Real.exp (-(s / 2)) • w‖ ^ 2 < 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  have hs : Real.exp s * Real.exp (-(s / 2)) ^ 2 = 1 := by
    rw [pow_two, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1; congr 1; ring
  rw [← mul_assoc, hs, one_mul]
  nlinarith only [hw, norm_nonneg w]

def hartogsHomeomorph (φ : Base → ℝ) (hφ : ContinuousOn φ ball) :
    hartogs φ ≃ₜ ball × Metric.ball (0 : ℂ) 1 where
  toFun p := (⟨p.1.1, p.2.1⟩,
    ⟨Real.exp (φ p.1.1 / 2) • p.1.2, by
      simpa using scaled_fibre_lt (φ p.1.1) p.1.2 p.2.2⟩)
  invFun p := ⟨(p.1.1, Real.exp (-(φ p.1.1 / 2)) • p.2.1),
    p.1.2, unscaled_fibre_lt (φ p.1.1) p.2.1 (by simpa only [Metric.mem_ball, dist_zero_right] using p.2.2)⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp only [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp only [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  continuous_toFun := by
    have hb : Continuous (fun p : hartogs φ ↦ (⟨p.1.1, p.2.1⟩ : ball)) :=
      continuous_subtype_val.fst.subtype_mk _
    have hp : Continuous (fun p : hartogs φ ↦ φ p.1.1) := (continuousOn_iff_continuous_domRestrict.mp hφ).comp hb
    exact hb.prodMk (((hp.div_const 2).rexp.smul continuous_subtype_val.snd).subtype_mk _)
  continuous_invFun := by
    have hp : Continuous (fun p : ball × Metric.ball (0 : ℂ) 1 ↦ φ p.1.1) :=
      (continuousOn_iff_continuous_domRestrict.mp hφ).comp continuous_fst
    exact ((continuous_subtype_val.comp continuous_fst).prodMk
      (((hp.div_const 2).neg.rexp).smul (continuous_subtype_val.comp continuous_snd))).subtype_mk _

theorem hartogs_contractible (φ : Base → ℝ) (hφ : ContinuousOn φ ball) :
    ContractibleSpace (hartogs φ) := by
  let : ContractibleSpace ball := by
    rw [ball_eq]
    exact (convex_ball (0 : Base) 1).contractibleSpace ⟨0, by simp⟩
  let : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, by simp⟩
  exact (hartogsHomeomorph φ hφ).contractibleSpace

theorem hartogs_isOpen (φ : Base → ℝ) (hφ : ContinuousOn φ ball) : IsOpen (hartogs φ) := by
  refine isOpen_iff_mem_nhds.mpr ?_
  intro p hp
  have hz : p.1 ∈ ball := hp.1
  have hc : ContinuousAt φ p.1 := hφ.continuousAt (isOpen_ball.mem_nhds hz)
  have ht : ContinuousAt (fun q : Ambient ↦ Real.exp (φ q.1) * ‖q.2‖ ^ 2) p :=
    (hc.comp continuousAt_fst).rexp.mul (continuousAt_snd.norm.pow 2)
  have hnb : ∀ᶠ q : Ambient in 𝓝 p, q.1 ∈ ball :=
    continuousAt_fst.eventually (isOpen_ball.mem_nhds hz)
  have hnt : ∀ᶠ q : Ambient in 𝓝 p, Real.exp (φ q.1) * ‖q.2‖ ^ 2 < 1 :=
    ht.eventually (gt_mem_nhds hp.2)
  exact hnb.and hnt

theorem hartogs_nonempty (φ : Base → ℝ) : (hartogs φ).Nonempty :=
  ⟨(0, 0), zeroSection_mem φ zero_mem_ball⟩

end PinchedHartogs

namespace PinchedHartogs
private lemma coordinate_symm_single (j : Fin 3) :
    coordinateLinearEquiv.symm (Pi.single j 1) = coordVector j := by
  fin_cases j <;> apply Prod.ext
  all_goals first
    | ext i; fin_cases i <;> simp [coordinateLinearEquiv, coordVector, EuclideanSpace.single]
    | simp [coordinateLinearEquiv, coordVector]

private theorem jacobian_det_ne_of_injective (F : Ambient → Target) (p : Ambient)
    (hf : Function.Injective (fderiv ℂ F p)) : (jacobian F p).det ≠ 0 := by
  let L : Target →ₗ[ℂ] Target := (fderiv ℂ F p).toLinearMap.comp coordinateLinearEquiv.symm.toLinearMap
  have hL : Function.Injective L := hf.comp coordinateLinearEquiv.symm.injective
  have heq : jacobian F p = LinearMap.toMatrix' L := by
    ext i j
    simp only [jacobian, LinearMap.toMatrix'_apply, L, LinearMap.comp_apply,
      LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe, coordinate_symm_single]
  rw [heq, LinearMap.det_toMatrix']
  intro hz
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hL)

theorem no_bounded_realization (M : Set Ambient) (hM : IsOpen M)
    (hN : NoBoundedCoordinates M) : ¬ BiholomorphicToBoundedDomain M := by
  rintro ⟨N, hNo, hNb, F, G, hF, hG, hFN, hGM, hGF, hFG⟩
  let f : Ambient → Target := fun p ↦ coordinateEquiv (F p)
  have hf : AnalyticOnNhd ℂ f M := by
    intro p hp
    exact (coordinateEquiv.toContinuousLinearMap.analyticAt (F p)).comp (hF p hp)
  have hfb : ∃ B : ℝ, ∀ p ∈ M, ∀ i, ‖f p i‖ ≤ B := by
    obtain ⟨B, hB⟩ := hNb.exists_norm_le
    refine ⟨‖coordinateEquiv.toContinuousLinearMap‖ * B, ?_⟩
    intro p hp i
    exact (norm_le_pi_norm (f p) i).trans
      ((coordinateEquiv.toContinuousLinearMap.le_opNorm (F p)).trans
        (mul_le_mul_of_nonneg_left (hB _ (hFN hp)) (norm_nonneg _)))
  apply hN f hf hfb
  intro p hp
  have hFp : DifferentiableAt ℂ F p := (hF p hp).differentiableAt
  have hGp : DifferentiableAt ℂ G (F p) := (hG (F p) (hFN hp)).differentiableAt
  have he : G ∘ F =ᶠ[𝓝 p] id := by
    filter_upwards [hM.mem_nhds hp] with q hq
    exact hGF q hq
  have hd : (fderiv ℂ G (F p)).comp (fderiv ℂ F p) = ContinuousLinearMap.id ℂ Ambient := by
    rw [← fderiv_comp p hGp hFp, he.fderiv_eq, fderiv_id]
  have hi : Function.Injective (fderiv ℂ F p) := by
    intro a b hab
    have ht := congrArg (fderiv ℂ G (F p)) hab
    simpa only [← ContinuousLinearMap.comp_apply, hd, ContinuousLinearMap.id_apply] using ht
  have hdf : fderiv ℂ f p = coordinateEquiv.toContinuousLinearMap.comp (fderiv ℂ F p) := by
    exact coordinateEquiv.toContinuousLinearMap.hasFDerivAt.comp p hFp.hasFDerivAt |>.fderiv
  apply jacobian_det_ne_of_injective
  rw [hdf]
  exact coordinateEquiv.injective.comp hi

end PinchedHartogs

namespace PinchedHartogs

theorem hartogs_obstruction (φ : Base → ℝ) (hφ : ContDiffOn ℝ ∞ φ ball)
    (hminorant : noMinorant φ) :
    IsOpen (hartogs φ) ∧ (hartogs φ).Nonempty ∧ ContractibleSpace (hartogs φ) ∧
      NoBoundedCoordinates (hartogs φ) ∧ ¬ BiholomorphicToBoundedDomain (hartogs φ) := by
  have hOpen := hartogs_isOpen φ hφ.continuousOn
  have hNo : NoBoundedCoordinates (hartogs φ) := by
    intro F hF hbound
    exact map_obstruction φ hφ hminorant F ⟨hF, hbound⟩
  exact ⟨hOpen, hartogs_nonempty φ, hartogs_contractible φ hφ.continuousOn, hNo,
    no_bounded_realization _ hOpen hNo⟩

end PinchedHartogs

end

end OAI
