import OAI.Probability.SLE.Angle.TargetDiskMap

namespace OAI

/-! The prescribed disk chart has the angle-independent initial
conformal radius needed for the centered moment bounds. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma diskMap_hasDerivAt {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    HasDerivAt (diskMap θ)
      ((Complex.exp (θ*Complex.I)-Complex.exp (-θ*Complex.I))/
        (z-Complex.exp (-θ*Complex.I))^2) z := by
  have hh := ((hasDerivAt_id z).sub_const (Complex.exp (θ*Complex.I))).div
    ((hasDerivAt_id z).sub_const (Complex.exp (-θ*Complex.I)))
    (diskMap_denominator_ne hθ hz)
  convert hh using 1 <;> first | rfl | (dsimp; ring)

lemma diskMap_differentiableOn {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    DifferentiableOn ℂ (diskMap θ) upperHalfPlane := by
  intro z hz
  exact (diskMap_hasDerivAt hθ hz).differentiableAt.differentiableWithinAt

lemma diskMap_injOn {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    InjOn (diskMap θ) upperHalfPlane := by
  intro z hz v hv he
  have h := congrArg (diskMapInv θ) he
  simpa only [diskMapInv_diskMap hθ hz,diskMapInv_diskMap hθ hv] using h

lemma diskMap_deriv_norm {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    ‖deriv (diskMap θ) z‖ =
      2*(Complex.exp (θ*Complex.I)).im/‖z-Complex.exp (-θ*Complex.I)‖^2 := by
  rw [(diskMap_hasDerivAt hθ hz).deriv,norm_div,norm_pow,disk_exp_conj,
    norm_sub_conj_of_im_pos (disk_center_height hθ)]

lemma diskMap_initial_radius {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    2*z.im*‖deriv (diskMap θ) z‖ = 1-‖diskMap θ z‖^2 := by
  have hd := norm_ne_zero_iff.mpr (diskMap_denominator_ne hθ hz)
  have hg := diskMap_normSq_gap θ z
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hg
  rw [diskMap_deriv_norm hθ hz,diskMap,norm_div]
  have hd' : ‖z-Complex.exp (-(θ*Complex.I))‖ ≠ 0 := by simpa only [neg_mul] using hd
  field_simp [hd']
  simp only [neg_mul] at hg
  nlinarith

theorem initialRadius_disk {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    {x : ℂ} (hx : x ∈ ball 0 1) : initialRadius θ x = 1-‖x‖^2 := by
  have h := diskMap_initial_radius hθ (diskMapInv_maps hθ hx)
  simpa only [initialRadius,diskMap_diskMapInv hθ hx] using h

lemma initialRadius_zero {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    initialRadius θ 0=1 := by
  simpa only [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),sub_zero] using
    initialRadius_disk hθ (mem_ball_zero_iff.mpr (by norm_num : ‖(0:ℂ)‖<1))

lemma initialRadius_pos {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    {x : ℂ} (hx : x ∈ ball 0 1) : 0 < initialRadius θ x := by
  rw [initialRadius_disk hθ hx]
  have hn := mem_ball_zero_iff.mp hx
  nlinarith [norm_nonneg x]

end SLEExactGauge.Target

end

end OAI
