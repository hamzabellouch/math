import OAI.Geometry.Relativity.CKS.ConeSupport

namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

def phi (x : ℝ) : ℝ :=
  (1 - Real.smoothTransition ((x-6)/6)) + Real.smoothTransition ((x-6)/6) * (x⁻¹)^3

def xi (x : ℝ) : ℝ := 1 - Real.smoothTransition (x-1)
def zeta (x : ℝ) : ℝ := Real.smoothTransition (x-4)
def beta (x : ℝ) : ℝ := 1 - Real.smoothTransition (2*x-7)

def bendingV (R r : ℝ) : ℝ := r * phi (r/R) * xi (r/R^2)
def bendingZeta (R r : ℝ) : ℝ := zeta (r/R)
def bendingBeta (R r : ℝ) : ℝ := beta (r/R)

lemma phi_one {x : ℝ} (hx : x ≤ 6) : phi x = 1 := by
  simp [phi,Real.smoothTransition.zero_of_nonpos (show (x-6)/6 ≤ 0 by linarith)]
lemma phi_tail {x : ℝ} (hx : 12 ≤ x) : phi x = (x⁻¹)^3 := by
  simp [phi,Real.smoothTransition.one_of_one_le (show 1 ≤ (x-6)/6 by linarith)]
lemma phi_pos {x : ℝ} (hx : 0 < x) : 0 < phi x := by
  have h0 := Real.smoothTransition.nonneg ((x-6)/6)
  have h1 := Real.smoothTransition.le_one ((x-6)/6)
  have hp : 0 < (x⁻¹)^3 := pow_pos (inv_pos.mpr hx) _
  unfold phi
  by_cases he : Real.smoothTransition ((x-6)/6) = 0
  · simp [he]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr h1) (mul_pos (lt_of_le_of_ne h0 (Ne.symm he)) hp)
lemma phi_le_one {x : ℝ} (hx : 0 < x) : phi x ≤ 1 := by
  by_cases h6 : x ≤ 6
  · rw [phi_one h6]
  · have h1x : 1 ≤ x := by linarith
    have hi : x⁻¹ ≤ 1 := (inv_le_one₀ hx).mpr h1x
    have hp : (x⁻¹)^3 ≤ 1 := by simpa using pow_le_pow_left₀ (inv_nonneg.mpr hx.le) hi 3
    have h0 := Real.smoothTransition.nonneg ((x-6)/6)
    have hprod := mul_le_mul_of_nonneg_left hp h0
    unfold phi
    linarith

lemma phi_smooth : ContDiffOn ℝ ∞ phi (Ioi 0) := by
  unfold phi
  have hc : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition ((x-6)/6)) := by fun_prop
  exact (contDiffOn_const.sub hc.contDiffOn).add
    (hc.contDiffOn.mul ((contDiffOn_id.inv (fun x hx => ne_of_gt hx)).pow 3))
lemma xi_smooth : ContDiff ℝ ∞ xi := by unfold xi; fun_prop
lemma zeta_smooth : ContDiff ℝ ∞ zeta := by unfold zeta; fun_prop
lemma beta_smooth : ContDiff ℝ ∞ beta := by unfold beta; fun_prop

lemma xi_nonneg (x : ℝ) : 0 ≤ xi x := sub_nonneg.mpr (Real.smoothTransition.le_one _)
lemma xi_le_one (x : ℝ) : xi x ≤ 1 := by unfold xi; linarith [Real.smoothTransition.nonneg (x-1)]
lemma xi_one {x : ℝ} (hx : x ≤ 1) : xi x = 1 := by
  simp [xi,Real.smoothTransition.zero_of_nonpos (show x-1 ≤ 0 by linarith)]
lemma xi_zero {x : ℝ} (hx : 2 ≤ x) : xi x = 0 := by
  simp [xi,Real.smoothTransition.one_of_one_le (show 1 ≤ x-1 by linarith)]
lemma zeta_nonneg (x : ℝ) : 0 ≤ zeta x := Real.smoothTransition.nonneg _
lemma zeta_le_one (x : ℝ) : zeta x ≤ 1 := Real.smoothTransition.le_one _
lemma zeta_zero {x : ℝ} (hx : x ≤ 4) : zeta x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
lemma zeta_one {x : ℝ} (hx : 5 ≤ x) : zeta x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
lemma beta_nonneg (x : ℝ) : 0 ≤ beta x := sub_nonneg.mpr (Real.smoothTransition.le_one _)
lemma beta_le_one (x : ℝ) : beta x ≤ 1 := by unfold beta; linarith [Real.smoothTransition.nonneg (2*x-7)]
lemma beta_one {x : ℝ} (hx : x ≤ 3) : beta x = 1 := by
  simp [beta,Real.smoothTransition.zero_of_nonpos (show 2*x-7 ≤ 0 by linarith)]
lemma beta_one_near {x : ℝ} (hx : x ≤ 7/2) : beta x = 1 := by
  simp [beta,Real.smoothTransition.zero_of_nonpos (show 2*x-7 ≤ 0 by linarith)]
lemma beta_zero {x : ℝ} (hx : 4 ≤ x) : beta x = 0 := by
  simp [beta,Real.smoothTransition.one_of_one_le (show 1 ≤ 2*x-7 by linarith)]

lemma bendingV_smooth {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ∞ (bendingV R) (Ioi 0) := by
  unfold bendingV
  have hc : ContDiffOn ℝ ∞ (fun r : ℝ => phi (r/R)) (Ioi 0) :=
    phi_smooth.comp (contDiffOn_id.div_const R) (fun r hr => div_pos hr hR)
  exact (contDiffOn_id.mul hc).mul
    ((xi_smooth.comp (contDiff_id.div_const (R^2))).contDiffOn)
lemma bendingZeta_smooth (R : ℝ) : ContDiff ℝ ∞ (bendingZeta R) :=
  zeta_smooth.comp (contDiff_id.div_const R)
lemma bendingBeta_smooth (R : ℝ) : ContDiff ℝ ∞ (bendingBeta R) :=
  beta_smooth.comp (contDiff_id.div_const R)

lemma bendingV_nonneg {R r : ℝ} (hR : 0 < R) (hr : 0 < r) : 0 ≤ bendingV R r :=
  mul_nonneg (mul_nonneg hr.le (phi_pos (div_pos hr hR)).le) (xi_nonneg _)
lemma bendingV_le_radius {R r : ℝ} (hR : 0 < R) (hr : 0 < r) : bendingV R r ≤ r := by
  calc
    _ ≤ r * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left (phi_le_one (div_pos hr hR)) hr.le)
      (xi_le_one _) (xi_nonneg _) (by positivity)
    _ = r := by ring

lemma bendingV_initial {R r : ℝ} (hR : 12 ≤ R) (hr : r ≤ 6*R) : bendingV R r = r := by
  have hRp : 0 < R := by linarith
  have hp : r/R ≤ 6 := (div_le_iff₀ hRp).mpr hr
  have hx : r/R^2 ≤ 1 := (div_le_iff₀ (sq_pos_of_pos hRp)).mpr (by nlinarith)
  simp [bendingV,phi_one hp,xi_one hx]
lemma bendingV_tail {R r : ℝ} (hR : 0 < R) (hr : 2*R^2 ≤ r) : bendingV R r = 0 := by
  have hx : 2 ≤ r/R^2 := (le_div_iff₀ (sq_pos_of_pos hR)).mpr hr
  simp [bendingV,xi_zero hx]

lemma beta_support {R r : ℝ} (hR : 12 ≤ R) (hb : bendingBeta R r ≠ 0) : bendingV R r = r := by
  apply bendingV_initial hR
  have hRp : 0 < R := by linarith
  have hh : r/R < 4 := by
    by_contra h
    exact hb (beta_zero (le_of_not_gt h))
  have hx := (div_lt_iff₀ hRp).mp hh
  linarith
lemma zeta_support {R r : ℝ} (hR : 12 ≤ R) (hz : bendingZeta R r ≠ 1) : bendingV R r = r := by
  apply bendingV_initial hR
  have hRp : 0 < R := by linarith
  have hh : r/R < 5 := by
    by_contra h
    exact hz (zeta_one (le_of_not_gt h))
  have hx := (div_lt_iff₀ hRp).mp hh
  linarith

end
end CKSBending

end

end OAI
