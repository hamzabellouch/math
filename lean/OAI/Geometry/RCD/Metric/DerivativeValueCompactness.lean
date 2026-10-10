import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Derivative convergence from values and a common second-order bound -/

open Set Filter
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem deriv_forward_slope_bound {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (L : ℝ≥0)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hL : LipschitzOnWith L (deriv f) (Icc a b)) :
    |deriv f a-(f b-f a)/(b-a)| ≤ L*(b-a) := by
  obtain ⟨c,hc,he⟩ := exists_deriv_eq_slope f hab
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x ⟨hx.1.le,hx.2.le⟩).differentiableWithinAt)
  have hh := hL.dist_le_mul a ⟨le_rfl,hab.le⟩ c ⟨hc.1.le,hc.2.le⟩
  rw [Real.dist_eq,he,Real.dist_eq,abs_of_nonpos (by linarith [hc.1] : a-c ≤ 0)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hc.2] : -(a-c) ≤ b-a) L.coe_nonneg)

theorem exists_derivative_limit_of_values (F : ℕ → ℝ → ℝ) (L : ℝ≥0)
    {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hF : ∀ k x, x ∈ Icc a b → DifferentiableAt ℝ (F k) x)
    (hL : ∀ k, LipschitzOnWith L (deriv (F k)) (Icc a b))
    (hval : ∀ x ∈ Icc a b, ∃ y : ℝ, Tendsto (fun k => F k x) atTop (𝓝 y)) :
    ∃ y : ℝ, Tendsto (fun k => deriv (F k) t) atTop (𝓝 y) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro e he
  let h := min ((b-t)/2) (e/(8*(L+1)))
  have hh : 0 < h := lt_min (by linarith [ht.2]) (by positivity)
  have hhb : h ≤ (b-t)/2 := min_le_left _ _
  have hhe : h ≤ e/(8*(L+1)) := min_le_right _ _
  have hhsmall : 8*((L:ℝ)+1)*h ≤ e := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 8*((L:ℝ)+1))).mp hhe
    nlinarith only [hmul]
  have hts : t+h ∈ Icc a b := ⟨by linarith [ht.1],by linarith⟩
  obtain ⟨u,hu⟩ := hval t ⟨ht.1.le,ht.2.le⟩
  obtain ⟨v,hv⟩ := hval (t+h) hts
  let slope k := (F k (t+h)-F k t)/h
  have hslope : Tendsto slope atTop (𝓝 ((v-u)/h)) := (hv.sub hu).div_const h
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hslope.cauchySeq (e/2) (by positivity)
  have herr (k : ℕ) : |deriv (F k) t-slope k| ≤ L*h := by
    have hsub : Icc t (t+h) ⊆ Icc a b := Icc_subset_Icc ht.1.le hts.2
    have hd := deriv_forward_slope_bound (by linarith : t < t+h) L
      (fun x hx => hF k x (hsub hx)) ((hL k).mono hsub)
    simpa only [add_sub_cancel_left,slope] using hd
  refine ⟨N,?_⟩
  intro i hi j hj
  have hd := hN i hi j hj
  rw [Real.dist_eq] at hd ⊢
  have hi' := herr i
  have hj' := herr j
  have ha := abs_sub_le (deriv (F i) t) (slope i) (slope j)
  have hb := abs_sub_le (deriv (F i) t) (slope j) (deriv (F j) t)
  rw [abs_sub_comm (slope j) (deriv (F j) t)] at hb
  have hLp : 0 ≤ (L:ℝ)*h := mul_nonneg L.coe_nonneg hh.le
  nlinarith

end RegularPointCoordinates

end

end OAI
