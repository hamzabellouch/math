import OAI.Geometry.Kahler.BaseOrbitGrowth

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def horizontalArc (q d : Base) (t : ℝ) : Base :=
  (Real.sqrt (1+t^2*‖d‖^2))⁻¹ • (q+t • d)

def horizontalArcVelocity (q d : Base) (t : ℝ) : Base :=
  (-(t*‖d‖^2)/(Real.sqrt (1+t^2*‖d‖^2))^3) • (q+t • d)+
    (Real.sqrt (1+t^2*‖d‖^2))⁻¹ • d

lemma horizontalArc_derivative (q d : Base) (t : ℝ) :
    HasDerivAt (horizontalArc q d) (horizontalArcVelocity q d t) t := by
  have hpos : 0 < 1+t^2*‖d‖^2 := by positivity
  have hh := (((((hasDerivAt_id t).pow 2).mul_const (‖d‖^2)).const_add 1).sqrt hpos.ne').inv (Real.sqrt_ne_zero'.mpr hpos)
  have hv := ((hasDerivAt_id t).smul_const d).const_add q
  convert! hh.smul hv using 1
  simp only [horizontalArcVelocity,Pi.pow_apply,id,one_smul]
  rw [add_comm]
  congr 1
  congr 1
  field_simp
  ring

lemma horizontalArc_norm (q : Sphere) (d : Base) (hd : bracket d (q:Base)=0) (t : ℝ) :
    ‖horizontalArc (q:Base) d t‖=1 := by
  have hpos : 0 < 1+t^2*‖d‖^2 := by positivity
  have hn : ‖(q:Base)+t • d‖^2=1+t^2*‖d‖^2 := by
    rw [norm_add_sq (𝕜 := ℂ),sphere_norm,norm_smul,Real.norm_eq_abs, mul_pow,sq_abs]
    have hinner : inner ℂ (q:Base) (t • d) = 0 := by
      rw [← Complex.coe_smul,inner_smul_right]
      change (t:ℂ)*bracket d (q:Base)=0
      rw [hd,mul_zero]
    rw [hinner]
    simp
  unfold horizontalArc
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (Real.sqrt_nonneg _)]
  have he : ‖(q:Base)+t • d‖=Real.sqrt (1+t^2*‖d‖^2) := by
    rw [← hn,Real.sqrt_sq (norm_nonneg _)]
  rw [he,inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hpos)]

lemma horizontalArc_horizontal (q : Sphere) (d : Base) (hd : bracket d (q:Base)=0) (t : ℝ) :
    bracket (horizontalArcVelocity q d t) (horizontalArc q d t)=0 := by
  have hpos : 0 < 1+t^2*‖d‖^2 := by positivity
  have hroot : Real.sqrt (1+t^2*‖d‖^2) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have hsq := Real.sq_sqrt hpos.le
  have hqd : inner ℂ (q:Base) d=0 := hd
  have hdq : inner ℂ d (q:Base)=0 := by rw [← inner_conj_symm (d) (q:Base),hqd]; simp
  have hqq : inner ℂ (q:Base) (q:Base)=1 := by rw [inner_self_eq_norm_sq_to_K,sphere_norm]; norm_num
  have hdd : inner ℂ d d=(‖d‖^2:ℝ) := by simp [inner_self_eq_norm_sq_to_K]
  simp only [bracket,horizontalArc,horizontalArcVelocity,← Complex.coe_smul,
    inner_smul_left,inner_smul_right,inner_add_left,inner_add_right,hqd,hdq,hqq,hdd]
  push_cast
  simp only [map_inv₀,Complex.conj_ofReal,mul_zero,add_zero,zero_add,mul_one]
  have hrootC : (Real.sqrt (1+t^2*‖d‖^2):ℂ) ≠ 0 := by exact_mod_cast hroot
  have hsqC : (Real.sqrt (1+t^2*‖d‖^2):ℂ)^2=1+(t:ℂ)^2*(‖d‖:ℂ)^2 := by exact_mod_cast hsq
  field_simp [hrootC]
  rw [hsqC]
  ring

lemma horizontalArc_velocity_norm (q : Sphere) (d : Base) (hd : bracket d (q:Base)=0) (t : ℝ) :
    ‖horizontalArcVelocity q d t‖ ≤ ‖d‖ := by
  let r := Real.sqrt (1+t^2*‖d‖^2)
  have hpos : 0 < 1+t^2*‖d‖^2 := by positivity
  have hr : 0 < r := Real.sqrt_pos.mpr hpos
  have hrsq : r^2=1+t^2*‖d‖^2 := Real.sq_sqrt hpos.le
  have he : horizontalArcVelocity q d t = (-t*‖d‖^2/r^3) • (q:Base)+(1/r^3) • d := by
    unfold horizontalArcVelocity
    dsimp only [r] at *
    rw [smul_add,smul_smul,add_assoc,← add_smul]
    congr 1
    · congr 1; ring
    · congr 1
      field_simp
      nlinarith [Real.sq_sqrt hpos.le]
  have hn : ‖horizontalArcVelocity q d t‖^2=‖d‖^2/r^4 := by
    rw [he,norm_add_sq (𝕜 := ℂ),norm_smul,norm_smul,sphere_norm,mul_one,Real.norm_eq_abs,Real.norm_eq_abs,mul_pow,sq_abs,sq_abs]
    have hi : inner ℂ ((-t*‖d‖^2/r^3) • (q:Base)) ((1/r^3) • d)=0 := by
      rw [← Complex.coe_smul,← Complex.coe_smul,inner_smul_left,inner_smul_right]
      change _*(_*bracket d (q:Base))=0
      rw [hd,mul_zero,mul_zero]
    rw [hi]
    simp only [map_zero,mul_zero,add_zero]
    field_simp
    nlinarith [sq_nonneg ‖d‖]
  have hr1 : 1 ≤ r := by nlinarith [sq_nonneg t,sq_nonneg ‖d‖]
  have hh : ‖d‖^2/r^4 ≤ ‖d‖^2 := div_le_self (sq_nonneg _) (one_le_pow₀ hr1)
  have : ‖horizontalArcVelocity q d t‖^2 ≤ ‖d‖^2 := hn.trans_le hh
  nlinarith [norm_nonneg d,norm_nonneg (horizontalArcVelocity q d t)]

end PinchedHartogs.BaseConstruction

end

end OAI
