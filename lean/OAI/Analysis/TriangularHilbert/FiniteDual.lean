import OAI.Analysis.TriangularHilbert.SampledMoment

namespace OAI

universe uι

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

def dualRoot (z : ℂ) : ℂ := (Real.sqrt ‖z‖:ℂ)*star z/(‖z‖:ℂ)

lemma dualRoot_mul (z : ℂ) : dualRoot z*z = (‖z‖*Real.sqrt ‖z‖:ℝ) := by
  by_cases hz : z = 0
  · subst z
    simp [dualRoot]
  have hn : (‖z‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  unfold dualRoot
  rw [div_mul_eq_mul_div, mul_assoc, RCLike.star_def,Complex.conj_mul']
  push_cast
  field_simp

lemma norm_dualRoot (z : ℂ) : ‖dualRoot z‖ = Real.sqrt ‖z‖ := by
  by_cases hz : z = 0
  · subst z
    simp [dualRoot]
  unfold dualRoot
  rw [norm_div,norm_mul,norm_star,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hz)]

lemma cube_norm_dualRoot (z : ℂ) : ‖dualRoot z‖^3 = ‖z‖*Real.sqrt ‖z‖ := by
  rw [norm_dualRoot,pow_succ,Real.sq_sqrt (norm_nonneg _)]

lemma finite_cubic_dual {ι : Type uι} [Fintype ι] (u : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {K b : ℝ} (hK : 0 < K)
    (H : ∀ f : ι → ℂ, ‖∑ i, (w i:ℂ)*f i*u i‖ ≤ K*((∑ i, w i*‖f i‖^3)+b)) :
    (∑ i, w i*(‖u i‖*Real.sqrt ‖u i‖)) ≤ 4*K*(K+1)*b := by
  let d : ℝ := 1/(2*(K+1))
  let m : ℝ := ∑ i, w i*(‖u i‖*Real.sqrt ‖u i‖)
  have hd : 0 < d := by dsimp [d]; positivity
  have hm : 0 ≤ m := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (by positivity))
  have hd1 : d ≤ 1 := by
    dsimp [d]
    rw [div_le_one (by positivity)]
    linarith
  have hk1 : K*d ≤ 1/2 := by
    dsimp [d]
    rw [← mul_div_assoc, mul_one,div_le_iff₀ (by positivity)]
    linarith
  have hk2 : K*d^3 ≤ d/2 := by
    have ha := mul_le_mul_of_nonneg_right hk1 (sq_nonneg d)
    nlinarith [mul_le_mul_of_nonneg_left hd1 hd.le]
  let f : ι → ℂ := fun i => (d:ℂ)*dualRoot (u i)
  have hprod (i : ι) : (w i:ℂ)*f i*u i = (d*(w i*(‖u i‖*Real.sqrt ‖u i‖)):ℝ) := by
    dsimp [f]
    rw [mul_assoc,mul_assoc,dualRoot_mul]
    push_cast
    ring
  have hnorm (i : ι) : w i*‖f i‖^3 = d^3*(w i*(‖u i‖*Real.sqrt ‖u i‖)) := by
    dsimp [f]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hd.le,mul_pow,cube_norm_dualRoot]
    ring
  have hp : (∑ i, (w i:ℂ)*f i*u i) = (d*m:ℝ) := by
    simp_rw [hprod]
    rw [← Complex.ofReal_sum,← Finset.mul_sum]
  have ha := H f
  rw [hp,Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hd.le hm)] at ha
  simp_rw [hnorm] at ha
  rw [← Finset.mul_sum] at ha
  change d*m ≤ K*(d^3*m+b) at ha
  have hb : m ≤ (2*K/d)*b := by
    rw [div_mul_eq_mul_div,le_div_iff₀ hd]
    nlinarith [mul_le_mul_of_nonneg_right hk2 hm]
  apply hb.trans_eq
  dsimp [d]
  field_simp
  ring
end
end TriangularHilbert
end

end OAI
