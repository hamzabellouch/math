import OAI.Analysis.BernoulliCone.LipschitzProduct

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli.Halfspace
variable {d : ℕ}

/-- The perspective of the square, with its zero trace value. -/
def squareQuotient (u : Space d → ℝ) (e : Space d) (x : Space d) : ℝ :=
  if 0 < inner ℝ x e then u x ^ 2 / inner ℝ x e else 0

lemma height_bound {u : Space d → ℝ} {L : ℝ≥0} (hL : LipschitzWith L u)
    {e : Space d} (he : ‖e‖=1) (hz : ∀ x, inner ℝ x e ≤ 0 → u x=0) (x : Space d) :
    |u x| ≤ (L:ℝ)*max (inner ℝ x e) 0 := by
  by_cases ht : 0 ≤ inner ℝ x e
  · let y := x-(inner ℝ x e) • e
    have hy : inner ℝ y e=0 := by simp [y,inner_sub_left,real_inner_smul_left,he]
    have hh := hL.norm_sub_le x y
    rw [hz y hy.le, sub_zero, Real.norm_eq_abs] at hh
    have hd : dist x y=inner ℝ x e := by
      rw [dist_eq_norm]
      simp only [y,sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht,he,mul_one]
    rw [← dist_eq_norm,hd] at hh
    simpa only [max_eq_left ht] using hh
  · rw [hz x (le_of_not_ge ht),abs_zero,max_eq_right (le_of_not_ge ht),mul_zero]

lemma perspective_estimate {a b t s C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (ht : 0 < t) (hs : 0 < s) (hst : s ≤ t)
    (ha : |a| ≤ C*t) (hb : |b| ≤ C*s)
    (hab : |a-b| ≤ C*ρ) (hts : t-s ≤ ρ) :
    |a^2/t-b^2/s| ≤ 3*C^2*ρ := by
  have hst0 : 0 ≤ t-s := sub_nonneg.mpr hst
  have hsq : |a^2-b^2| ≤ 2*C*t*(C*ρ) := by
    calc
      _ = |a+b| * |a-b| := by rw [← abs_mul]; congr 1; ring
      _ ≤ (|a|+|b|)*(C*ρ) := mul_le_mul (abs_add_le _ _) hab (abs_nonneg _) (by positivity)
      _ ≤ (C*t+C*t)*(C*ρ) := by gcongr; exact hb.trans (mul_le_mul_of_nonneg_left hst hC)
      _ = _ := by ring
  have hb2 : b^2 ≤ C^2*s^2 := by
    simpa only [sq_abs,mul_pow] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hsecond : b^2*(t-s)/(t*s) ≤ C^2*ρ := by
    apply (div_le_iff₀ (mul_pos ht hs)).mpr
    have ha1 := mul_le_mul_of_nonneg_right hb2 hst0
    have ha2 := mul_le_mul_of_nonneg_left hts (mul_nonneg (sq_nonneg C) (sq_nonneg s))
    have ha3 : C^2*s^2*ρ ≤ C^2*ρ*(t*s) := by
      have hh : s^2 ≤ t*s := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg C) hρ)]
    nlinarith
  calc
    _ = |(a^2-b^2)/t-b^2*(t-s)/(t*s)| := by congr 1; field_simp; ring
    _ ≤ |(a^2-b^2)/t|+|b^2*(t-s)/(t*s)| := abs_sub _ _
    _ = |a^2-b^2|/t+b^2*(t-s)/(t*s) := by
      rw [abs_div,abs_of_pos ht,abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hst0) (mul_pos ht hs).le)]
    _ ≤ 2*C^2*ρ + C^2*ρ := by
      apply add_le_add _ hsecond
      apply (div_le_iff₀ ht).mpr
      nlinarith [hsq]
    _ = _ := by ring

lemma squareQuotient_lipschitz {u : Space d → ℝ} {L : ℝ≥0} (hL : LipschitzWith L u)
    {e : Space d} (he : ‖e‖=1) (hz : ∀ x, inner ℝ x e ≤ 0 → u x=0) :
    LipschitzWith (3*L^2) (squareQuotient u e) := by
  have ht (x y : Space d) : |inner ℝ x e-inner ℝ y e| ≤ dist x y := by
    rw [← inner_sub_left]
    exact (abs_real_inner_le_norm _ _).trans_eq (by rw [he,mul_one,dist_eq_norm])
  have hmain (x y : Space d) (hxy : inner ℝ y e ≤ inner ℝ x e) :
      |squareQuotient u e x-squareQuotient u e y| ≤ (3*(L:ℝ)^2)*dist x y := by
    by_cases hx : 0 < inner ℝ x e
    · by_cases hy : 0 < inner ℝ y e
      · simp only [squareQuotient,ite_eq_left hx,ite_eq_left hy]
        apply perspective_estimate L.coe_nonneg dist_nonneg hx hy hxy
        · simpa only [max_eq_left hx.le] using height_bound hL he hz x
        · simpa only [max_eq_left hy.le] using height_bound hL he hz y
        · simpa only [Real.norm_eq_abs,dist_eq_norm] using hL.norm_sub_le x y
        · exact (le_abs_self _).trans (ht x y)
      · simp only [squareQuotient,ite_eq_left hx,ite_eq_right hy,sub_zero,
          abs_of_nonneg (div_nonneg (sq_nonneg _) hx.le)]
        apply (div_le_iff₀ hx).mpr
        have hb := height_bound hL he hz x
        rw [max_eq_left hx.le] at hb
        have hu2 : u x^2 ≤ (L:ℝ)^2*(inner ℝ x e)^2 := by
          simpa only [sq_abs,mul_pow] using pow_le_pow_left₀ (abs_nonneg (u x)) hb 2
        have hh : inner ℝ x e ≤ dist x y := by
          have hh := (le_abs_self (inner ℝ x e-inner ℝ y e)).trans (ht x y)
          linarith [not_lt.mp hy]
        have hh2 := mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg (L:ℝ)) hx.le)
        nlinarith [sq_nonneg (L:ℝ),dist_nonneg (x:=x) (y:=y)]
    · have hy : ¬0 < inner ℝ y e := by linarith
      simp only [squareQuotient,ite_eq_right hx,ite_eq_right hy,sub_self,abs_zero]
      positivity
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  change _ ≤ (3*(L:ℝ)^2)*dist x y
  obtain hh|hh := le_total (inner ℝ y e) (inner ℝ x e)
  · exact hmain x y hh
  · simpa only [abs_sub_comm,dist_comm] using hmain y x hh
end Bernoulli.Halfspace

end
end

end OAI
