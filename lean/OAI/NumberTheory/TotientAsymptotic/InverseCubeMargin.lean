import OAI.NumberTheory.TotientAsymptotic.StrictCube

namespace OAI

/-! An explicit polynomial threshold pays for each inverse-cube row margin. -/
noncomputable section
namespace TotientAsymptotic

lemma inverse_cube_margin {h : ℕ} (hh : 1 ≤ h) {u v : ℝ}
    (hu : 100*(h:ℝ)^5 ≤ u) (hdist : |u-v| ≤ 1) :
    0 < v ∧ (h:ℝ)^2+1 ≤
      ((1+1/(10*(h:ℝ)^3))⁻¹-(1+1/(5*(h:ℝ)^3))⁻¹)*v := by
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hp : (0:ℝ) < h := lt_of_lt_of_le zero_lt_one hh'
  have hp3 : 1 ≤ (h:ℝ)^3 := one_le_pow₀ hh'
  have hp5 : 1 ≤ (h:ℝ)^5 := one_le_pow₀ hh'
  have h35 : (h:ℝ)^3 ≤ (h:ℝ)^5 := pow_le_pow_right₀ hh' (by omega)
  have hd := (le_abs_self _).trans hdist
  have hv : 0 < v := by nlinarith only [hu,hd,hp5]
  refine ⟨hv,?_⟩
  have hbase : 30*(h:ℝ)^5+30*(h:ℝ)^3 ≤ v := by
    nlinarith only [hu,hd,hp5,h35]
  have hquot : (h:ℝ)^2+1 ≤ v/(30*(h:ℝ)^3) := by
    apply (le_div_iff₀ (by positivity : 0 < 30*(h:ℝ)^3)).mpr
    convert hbase using 1; ring
  have he : 0 < 1/(5*(h:ℝ)^3) := by positivity
  have he1 : 1/(5*(h:ℝ)^3) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 5*(h:ℝ)^3)).mpr
    linarith only [hp3]
  have hmargin := reciprocal_row_margin he he1
  have heq : 1/(5*(h:ℝ)^3)/2=1/(10*(h:ℝ)^3) := by ring
  rw [heq] at hmargin
  apply hquot.trans
  have hh := mul_le_mul_of_nonneg_right hmargin hv.le
  convert hh using 1; ring

lemma inverse_cube_top_margin {m n : ℕ} (hn : n ≤ m) {B : ℝ}
    (hB : 100*(m+1:ℝ)^5 ≤ B) :
    B/(1+1/(5*(m+1:ℝ)^3))+(n:ℝ)^2 ≤ B/(1+1/(10*(m+1:ℝ)^3)) := by
  have he := (inverse_cube_margin (h:=m+1) (by omega)
    (by simpa only [Nat.cast_add,Nat.cast_one] using hB) (by simp : |B-B| ≤ 1)).2
  have hn' : (n:ℝ) ≤ m+1 := by exact_mod_cast (show n ≤ m+1 by omega)
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg n) hn' 2
  simp only [Nat.cast_add,Nat.cast_one] at he
  have hid : ((1+1/(10*(m+1:ℝ)^3))⁻¹-(1+1/(5*(m+1:ℝ)^3))⁻¹)*B=
      B/(1+1/(10*(m+1:ℝ)^3))-B/(1+1/(5*(m+1:ℝ)^3)) := by ring
  rw [hid] at he
  linarith only [he,hs]

end TotientAsymptotic

end

end OAI
