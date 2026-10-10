import OAI.Geometry.RCD.Transport.PointedHopfLaxUpper

namespace OAI

/-! # Sharp local radius control for approximate Euclidean Hopf--Lax minimizers -/

open Set Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates

theorem approximate_hopf_minimizer_radius {n : ℕ} {ψ : Euclidean n → ℝ}
    {M L : ℝ≥0} (hψ : LipschitzWith M ψ) {t E : ℝ} (ht : 0<t) (hE : 0≤E)
    (x z : Euclidean n)
    (hlocal : LipschitzOnWith L ψ (closedBall x (dist z x)))
    (hmin : ψ z+dist x z^2/(2*t)≤hopfLax ψ t x+E) :
    dist z x≤t*(L:ℝ)+Real.sqrt (2*t*E) := by
  by_cases hd : dist z x≤t*(L:ℝ)
  · exact hd.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hd' : t*(L:ℝ)<dist z x := lt_of_not_ge hd
  have hD : 0<dist z x := lt_of_le_of_lt (mul_nonneg ht.le L.coe_nonneg) hd'
  let c := t*(L:ℝ)/dist z x
  have hc0 : 0≤c := div_nonneg (mul_nonneg ht.le L.coe_nonneg) hD.le
  have hc1 : c<1 := (div_lt_one hD).mpr hd'
  let y := x+c • (z-x)
  have hy : dist y x=t*(L:ℝ) := by
    have he : y-x=c • (z-x) := by dsimp only [y]; abel
    rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc0]
    change c*dist z x=t*(L:ℝ)
    exact div_mul_cancel₀ _ hD.ne'
  have hzy : dist z y=dist z x-t*(L:ℝ) := by
    have he : z-y=(1-c) • (z-x) := by dsimp only [y]; module
    rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hc1)]
    change (1-c)*dist z x=dist z x-t*(L:ℝ)
    dsimp only [c]
    field_simp
  have hzmem : z∈closedBall x (dist z x) := mem_closedBall.mpr le_rfl
  have hymem : y∈closedBall x (dist z x) := mem_closedBall.mpr (hy.trans_le hd'.le)
  have hl : ψ y-ψ z≤(L:ℝ)*(dist z x-t*(L:ℝ)) := by
    have hh := (le_abs_self (ψ y-ψ z)).trans (hlocal.dist_le_mul y hymem z hzmem)
    rw [dist_comm y z,hzy] at hh
    exact hh
  have hup := hopfLax_le_cost hψ ht x y
  rw [dist_comm x y,hy] at hup
  rw [dist_comm x z] at hmin
  have hgap : (dist z x-t*(L:ℝ))^2≤2*t*E := by
    have hh : dist z x^2/(2*t)-(t*(L:ℝ))^2/(2*t)≤
        (L:ℝ)*(dist z x-t*(L:ℝ))+E := by linarith
    have hmul := (mul_le_mul_of_nonneg_right hh (show 0≤2*t by positivity))
    field_simp at hmul
    nlinarith
  have hs := Real.sq_sqrt (show 0≤2*t*E by positivity)
  nlinarith [Real.sqrt_nonneg (2*t*E)]

end RegularPointCoordinates

end

end OAI
