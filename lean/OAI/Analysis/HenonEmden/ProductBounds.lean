import OAI.Analysis.HenonEmden.SourceMass

namespace OAI

section ProductBounds

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
open Set Filter Topology
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section


namespace HenonLaneEmden
lemma coupled_power_lower {U V c d R a b p q : ℝ}
    (hU : 0 < U) (_hV : 0 < V) (hc : 0 < c) (hd : 0 < d) (hR : 0 < R)
    (hp : 0 < p) (h1 : c*R^a*V^p ≤ U) (h2 : d*R^b*U^q ≤ V) :
    c*d^p*R^(a+p*b) ≤ U^(1-p*q) := by
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ d*R^b*U^q) h2 hp.le
  have hh' := (mul_le_mul_of_nonneg_left hh (mul_nonneg hc.le (Real.rpow_nonneg hR.le a))).trans h1
  have he : c*R^a*(d*R^b*U^q)^p = c*d^p*R^(a+p*b)*U^(p*q) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hU.le q),
      Real.mul_rpow hd.le (Real.rpow_nonneg hR.le b),
      ← Real.rpow_mul hR.le,← Real.rpow_mul hU.le,Real.rpow_add hR]
    simp only [mul_comm b p,mul_comm q p]
    ring
  rw [he] at hh'
  rw [Real.rpow_sub hU,Real.rpow_one]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hU (p*q))).mpr hh'

lemma no_small_product_coupled {U V : ℝ → ℝ} {c d a b p q M : ℝ}
    (hc : 0 < c) (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (hU : ∀ R > 0, 0 < U R) (hV : ∀ R > 0, 0 < V R)
    (h1 : ∀ R > 0, c*R^a*(V R)^p ≤ U R)
    (h2 : ∀ R > 0, d*R^b*(U R)^q ≤ V R)
    (hbound : ∀ R > 0, U R ≤ M) : 1 < p*q := by
  by_contra hh
  have hpq : p*q ≤ 1 := le_of_not_gt hh
  have hK : 0 < c*d^p := mul_pos hc (Real.rpow_pos_of_pos hd p)
  have hB : ∀ R > 0, c*d^p*R^(a+p*b) ≤ M^(1-p*q) := by
    intro R hR
    exact (coupled_power_lower (hU R hR) (hV R hR) hc hd hR hp (h1 R hR) (h2 R hR)).trans
      (Real.rpow_le_rpow (hU R hR).le (hbound R hR) (by linarith))
  have ht : Tendsto (fun R : ℝ => c*d^p*R^(a+p*b)) atTop atTop :=
    (tendsto_rpow_atTop (add_pos ha (mul_pos hp hb))).const_mul_atTop hK
  obtain ⟨R,hR,hgt⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (ht.eventually (eventually_gt_atTop (M^(1-p*q))))).exists
  exact (not_lt_of_ge (hB R hR)) hgt

lemma coupled_upper_one {U V c d p q : ℝ}
    (hU : 0 < U) (hV : 0 < V) (hc : 0 < c) (hd : 0 < d)
    (hp : 0 < p) (hpq : 1 < p*q) (h1 : c*V^p ≤ U) (h2 : d*U^q ≤ V) :
    U ≤ (c*d^p)^(1/(1-p*q)) := by
  have hh := coupled_power_lower (a := 0) (b := 0) (R := 1) hU hV hc hd zero_lt_one hp
    (by simpa using h1) (by simpa using h2)
  simp only [Real.one_rpow,mul_one] at hh
  have hK : 0 < c*d^p := mul_pos hc (Real.rpow_pos_of_pos hd p)
  simpa only [one_div] using (Real.le_rpow_inv_iff_of_neg hU hK (show 1-p*q < 0 by linarith)).mpr hh
end HenonLaneEmden

namespace HenonLaneEmden
open WeakPDE
lemma IsSolution.product_gt_one {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) : 1 < p*q := by
  have hn3 := h.dimension_ge_three hn
  have hA := h.first_weight_gt_neg_two hn
  have hB := h.swap.first_weight_gt_neg_two hn
  apply no_small_product_coupled (U := lowerMass v p A) (V := lowerMass u q B)
    (M := u 0) (mul_pos (ballConstant_pos hn3) (weightMass_pos hn3 hA))
    (mul_pos (ballConstant_pos hn3) (weightMass_pos hn3 hB))
    (show 0 < 2+A by linarith) (show 0 < 2+B by linarith) hp
    (fun _ hR => h.lowerMass_g_pos hn hR) (fun _ hR => h.swap.lowerMass_g_pos hn hR)
    (fun _ hR => h.lowerMass_g_coupling hn hp hR)
  · exact fun R hR => h.swap.lowerMass_g_coupling hn hq hR
  · intro R hR
    exact h.lowerMass_g_le hn hR (by simpa using hR.le)
end HenonLaneEmden

namespace HenonLaneEmden
open WeakPDE
lemma IsSolution.no_positive_lower_bound_u {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    {M : ℝ} (hM : 0 < M) (hbound : ∀ x, M ≤ u x) : False := by
  have hn3 := h.dimension_ge_three hn
  have hB := h.swap.first_weight_gt_neg_two hn
  have hc := ballConstant_pos hn3
  have hw := weightMass_pos hn3 hB
  have hb (R : ℝ) (hR : 0 < R) :
      ballConstant n*weightMass n B*M^q*R^(2+B) ≤ v 0 := by
    have hh := integral_source_ge_lower hn3 h.continuous_u h.positive_u hq.le hB hR hM.le
      (fun x _ => hbound x)
    have hh' := mul_le_mul_of_nonneg_left hh
      (mul_nonneg hc.le (Real.rpow_nonneg hR.le (2-(n:ℝ))))
    have he : R^(2+B) = R^(2-(n:ℝ))*R^((n:ℝ)+B) := by
      rw [← Real.rpow_add hR]; congr 1; ring
    have hl : ballConstant n*weightMass n B*M^q*R^(2+B) ≤ lowerMass u q B R := by
      rw [lowerMass_eq _ _ _ hR,he]
      nlinarith only [hh']
    exact hl.trans (h.swap.lowerMass_g_le hn hR (by simpa using hR.le))
  have ht : Tendsto (fun R : ℝ => ballConstant n*weightMass n B*M^q*R^(2+B)) atTop atTop :=
    (tendsto_rpow_atTop (show 0 < 2+B by linarith)).const_mul_atTop
      (mul_pos (mul_pos hc hw) (Real.rpow_pos_of_pos hM q))
  obtain ⟨R,hR,hgt⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (ht.eventually (eventually_gt_atTop (v 0)))).exists
  exact (not_lt_of_ge (hb R hR)) hgt

lemma IsSolution.potential_u_ae {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q) :
    ∀ᵐ x, newtonDenom n*u x = rawPotential (source v p A) x := by
  obtain ⟨c,hc,hceq⟩ := h.potential_constant_u hn
  have hc0 : c = 0 := by
    by_contra hh
    have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hh)
    have hD := newtonDenom_pos (h.dimension_ge_three hn)
    have hb : ∀ᵐ x, c/newtonDenom n ≤ u x := by
      filter_upwards [hceq] with x hx
      apply (div_le_iff₀ hD).mpr
      have hp := rawPotential_nonneg (source_nonneg (fun y => (h.positive_v y).le) p A) x
      nlinarith only [hx,hp]
    have heq : (fun x => max (c/newtonDenom n) (u x)) = u :=
      Measure.eq_of_ae_eq (hb.mono fun _ hx => max_eq_right hx)
        (continuous_const.max h.continuous_u) h.continuous_u
    exact h.no_positive_lower_bound_u hn hq (div_pos hcp hD)
      (fun x => max_eq_right_iff.mp (congrFun heq x))
  simpa only [hc0,add_zero] using hceq
end HenonLaneEmden

end
end ProductBounds

end OAI
