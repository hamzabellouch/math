import Mathlib
import OAI.Analysis.CoulombRadii.Localization.RadialCut

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

def annularAngle (u : ℝ) (x : Space) : ℝ := cutAngle 0 (2*u) x-cutAngle 0 (u/2) x

def annularCut (u : ℝ) (l : Fin 2) (x : Space) : ℝ :=
  if l=0 then Real.sin (annularAngle u x) else Real.cos (annularAngle u x)

lemma annularAngle_smooth (u : ℝ) : ContDiff ℝ ∞ (annularAngle u) :=
  (cutAngle_smooth 0 (2*u)).sub (cutAngle_smooth 0 (u/2))

lemma annularCut_smooth (u : ℝ) (l : Fin 2) : ContDiff ℝ ∞ (annularCut u l) := by
  unfold annularCut
  split_ifs
  · exact (annularAngle_smooth u).sin
  · exact (annularAngle_smooth u).cos

lemma annularCut_partition (u : ℝ) (x : Space) : ∑ l : Fin 2, annularCut u l x^2=1 := by
  simp [Fin.sum_univ_two,annularCut]

lemma cutAngle_inner (y : Space) {r : ℝ} (hr : 0<r) {x : Space} (hx : ‖x-y‖≤r) :
    cutAngle y r x=Real.pi/2 := by
  have hs : ‖r⁻¹ • (x-y)‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_one₀ hr).2 hx
  simp [cutAngle,cutSeed_one _ hs]

lemma cutAngle_outer (y : Space) {r : ℝ} (hr : 0<r) {x : Space} (hx : 2*r≤‖x-y‖) :
    cutAngle y r x=0 := by
  have hs : 2≤‖r⁻¹ • (x-y)‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (le_inv_mul_iff₀ hr).2 (by simpa only [mul_comm] using hx)
  simp [cutAngle,cutSeed_zero _ hs]

lemma annularCut_core_zero {u : ℝ} (hu : 0<u) {x : Space} (hx : u≤‖x‖ ∧ ‖x‖≤2*u) :
    annularCut u 1 x=0 := by
  have h1 := cutAngle_inner 0 (by positivity : 0<2*u) (x:=x) (by simpa using hx.2)
  have h2 := cutAngle_outer 0 (by positivity : 0<u/2) (x:=x) (by simp only [sub_zero]; linarith [hx.1])
  simp only [annularCut,show (1:Fin 2)≠0 by decide,ite_false,annularAngle,h1,h2,sub_zero,Real.cos_pi_div_two]

lemma annularCut_out_zero {u : ℝ} (hu : 0<u) {x : Space} (hx : ‖x‖≤u/2 ∨ 4*u≤‖x‖) :
    annularCut u 0 x=0 := by
  have hz : annularAngle u x=0 := by
    rcases hx with hx|hx
    · have h1 := cutAngle_inner 0 (by positivity : 0<2*u) (x:=x) (by simpa using (show ‖x‖≤2*u by linarith))
      have h2 := cutAngle_inner 0 (by positivity : 0<u/2) (x:=x) (by simpa using hx)
      simp only [annularAngle,h1,h2,sub_self]
    · have h1 := cutAngle_outer 0 (by positivity : 0<2*u) (x:=x) (by simp only [sub_zero]; linarith)
      have h2 := cutAngle_outer 0 (by positivity : 0<u/2) (x:=x) (by simp only [sub_zero]; linarith)
      simp only [annularAngle,h1,h2,sub_self]
  simp [annularCut,hz]

lemma cutAngle_derivative_bound (y : Space) {r : ℝ} (hr : 0<r) (b : Fin 3) (x : Space) :
    |fderiv ℝ (cutAngle y r) x (EuclideanSpace.single b 1)|≤radialCutCoefficient/r := by
  rw [cutAngle_fderiv,abs_mul,abs_of_pos (mul_pos (by positivity) (inv_pos.mpr hr))]
  have H := ((fderiv ℝ cutSeed (r⁻¹ • (x-y))).le_opNorm (EuclideanSpace.single b 1)).trans
    (mul_le_mul_of_nonneg_right (norm_cutSeed_derivative _) (norm_nonneg _))
  simp only [PiLp.norm_single,norm_one,mul_one,Real.norm_eq_abs] at H
  calc
    _ ≤ (Real.pi/2)*r⁻¹*cutSeedDerivativeBound := mul_le_mul_of_nonneg_left H (by positivity)
    _ = _ := by unfold radialCutCoefficient; ring

lemma annularAngle_derivative_bound {u : ℝ} (hu : 0<u) (b : Fin 3) (x : Space) :
    |fderiv ℝ (annularAngle u) x (EuclideanSpace.single b 1)| ≤ 3*radialCutCoefficient/u := by
  have h1 := cutAngle_derivative_bound 0 (by positivity : 0<2*u) b x
  have h2 := cutAngle_derivative_bound 0 (by positivity : 0<u/2) b x
  have hd1 := (cutAngle_smooth 0 (2*u)).differentiable (by simp) x
  have hd2 := (cutAngle_smooth 0 (u/2)).differentiable (by simp) x
  change |fderiv ℝ (cutAngle 0 (2*u) - cutAngle 0 (u/2)) x _|≤_
  rw [fderiv_sub hd1 hd2,sub_apply]
  have H := (abs_sub _ _).trans (add_le_add h1 h2)
  have he : radialCutCoefficient/(2*u)+radialCutCoefficient/(u/2)=(5/2)*radialCutCoefficient/u := by ring
  rw [he] at H
  simp only [mul_div_assoc] at H ⊢
  nlinarith [div_nonneg radialCutCoefficient_pos.le hu.le]

lemma annularCut_derivative_bound {u : ℝ} (hu : 0<u) (l : Fin 2) (b : Fin 3) (x : Space) :
    |fderiv ℝ (annularCut u l) x (EuclideanSpace.single b 1)| ≤ 3*radialCutCoefficient/u := by
  have hb := annularAngle_derivative_bound hu b x
  unfold annularCut
  split_ifs
  · rw [fderiv_sin ((annularAngle_smooth u).differentiable (by simp) x)]
    simp only [smul_apply,smul_eq_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans (by simpa using hb)
  · rw [fderiv_cos ((annularAngle_smooth u).differentiable (by simp) x)]
    simp only [smul_apply,smul_eq_mul,abs_mul,abs_neg]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans (by simpa using hb)

end Coulomb
end

end

end OAI
