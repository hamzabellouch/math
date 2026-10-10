import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLE.DiskHalfPlane

namespace OAI

/-! The exact disk chart appearing in the prescribed coefficient formula. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma disk_exp_conj (θ : ℝ) :
    Complex.exp (-θ*Complex.I) = star (Complex.exp (θ*Complex.I)) := by
  rw [Complex.star_def,← Complex.exp_conj]
  congr 1
  simp

lemma disk_center_height {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    0 < (Complex.exp (θ*Complex.I)).im := by
  rw [Complex.exp_ofReal_mul_I_im]
  exact Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2

lemma diskMap_denominator_ne {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    {z : ℂ} (hz : z ∈ upperHalfPlane) : z-Complex.exp (-θ*Complex.I) ≠ 0 := by
  intro he
  have hh := congrArg Complex.im (sub_eq_zero.mp he)
  rw [disk_exp_conj,Complex.star_def,Complex.conj_im] at hh
  have hw := disk_center_height hθ
  change 0 < z.im at hz
  linarith

lemma diskMap_normSq_gap (θ : ℝ) (z : ℂ) :
    Complex.normSq (z-Complex.exp (-θ*Complex.I))-
      Complex.normSq (z-Complex.exp (θ*Complex.I)) =
      4*z.im*(Complex.exp (θ*Complex.I)).im := by
  rw [disk_exp_conj]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma diskMap_maps {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    MapsTo (diskMap θ) upperHalfPlane (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff,diskMap,norm_div]
  have hd := diskMap_denominator_ne hθ hz
  apply (div_lt_one (norm_pos_iff.mpr hd)).mpr
  have hgap := diskMap_normSq_gap θ z
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hgap
  have hp : 0 < 4*z.im*(Complex.exp (θ*Complex.I)).im :=
    mul_pos (mul_pos (by norm_num) hz) (disk_center_height hθ)
  nlinarith [norm_nonneg (z-Complex.exp (-θ*Complex.I)),
    norm_nonneg (z-Complex.exp (θ*Complex.I))]

lemma diskMapInv_eq_diskToHalfPlane (θ : ℝ) (x : ℂ) :
    diskMapInv θ x = diskToHalfPlane (Complex.exp (θ*Complex.I)) x := by
  rw [diskMapInv,diskToHalfPlane,disk_exp_conj]
  congr 2
  ring

lemma diskMapInv_maps {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    MapsTo (diskMapInv θ) (ball 0 1) upperHalfPlane := by
  intro x hx
  rw [diskMapInv_eq_diskToHalfPlane]
  exact diskToHalfPlane_maps (disk_center_height hθ) hx

lemma diskMapInv_diskMap {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    {z : ℂ} (hz : z ∈ upperHalfPlane) : diskMapInv θ (diskMap θ z)=z := by
  have hd := diskMap_denominator_ne hθ hz
  have hx := disk_denominator_ne (diskMap_maps hθ hz)
  dsimp only [diskMapInv]
  apply (div_eq_iff hx).mpr
  dsimp only [diskMap]
  have hd' : z-Complex.exp (-(θ*Complex.I)) ≠ 0 := by simpa only [neg_mul] using hd
  field_simp [hd']
  ring

lemma diskMap_diskMapInv {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    {x : ℂ} (hx : x ∈ ball 0 1) : diskMap θ (diskMapInv θ x)=x := by
  have hd := disk_denominator_ne hx
  have hz := diskMap_denominator_ne hθ (diskMapInv_maps hθ hx)
  dsimp only [diskMap]
  apply (div_eq_iff hz).mpr
  dsimp only [diskMapInv]
  field_simp
  ring

def diskHomeomorph (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    upperHalfPlane ≃ₜ (ball (0:ℂ) 1) where
  toFun z := ⟨diskMap θ z,diskMap_maps hθ z.property⟩
  invFun x := ⟨diskMapInv θ x,diskMapInv_maps hθ x.property⟩
  left_inv z := Subtype.ext (diskMapInv_diskMap hθ z.property)
  right_inv x := Subtype.ext (diskMap_diskMapInv hθ x.property)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.sub continuous_const).div
      (continuous_subtype_val.sub continuous_const) (fun z => diskMap_denominator_ne hθ z.property)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.sub (continuous_subtype_val.mul continuous_const)).div
      (continuous_const.sub continuous_subtype_val) (fun x => disk_denominator_ne x.property)

end SLEExactGauge.Target

end

end OAI
