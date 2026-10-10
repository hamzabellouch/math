import Mathlib
import OAI.Geometry.CAT0Fillings.Chord.AverageProfile

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.Conformal
lemma averageProfile_bound {n : ℕ} {d : ℝ → ℝ} {B : ℝ}
    (hdB : ∀ x, |d x| ≤ B) (t : ℝ) : |averageProfile n d t| ≤ B^2 := by
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Icc (0:ℝ) 1))
    (f := fun τ => τ^(n-1)*(d (τ*t))^2) (C := B^2) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact avg_integrand_bound hτ hdB n)
  simpa [averageProfile,Measure.real,Real.norm_eq_abs] using h
lemma averageProfile_deriv_bound {n : ℕ} (hn : 0 < n) {d : ℝ → ℝ} {B : ℝ}
    (hd : ContDiff ℝ 1 d) (hB : 0 ≤ B) (hdB : ∀ x, |d x| ≤ B ∧ |deriv d x| ≤ B) (t : ℝ) :
    |deriv (averageProfile n d) t| ≤ 2*B^2 := by
  rw [(averageProfile_hasDerivAt hn hd hB hdB t).deriv]
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Icc (0:ℝ) 1))
    (f := fun τ => 2*τ^n*d (τ*t)*deriv d (τ*t)) (C := 2*B^2) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact avg_deriv_bound hB hτ hdB n)
  simpa [averageProfileDeriv,Measure.real,Real.norm_eq_abs] using h
lemma averageProfile_identity {n : ℕ} (hn : 0 < n) {d : ℝ → ℝ} {B : ℝ}
    (hd : ContDiff ℝ 1 d) (hB : 0 ≤ B) (hdB : ∀ x, |d x| ≤ B ∧ |deriv d x| ≤ B) (t : ℝ) :
    (n:ℝ)*averageProfile n d t+t*deriv (averageProfile n d) t = (d t)^2 := by
  have hdc := hd.continuous_deriv_one
  have hder (τ : ℝ) : HasDerivAt (fun τ => τ^n*(d (τ*t))^2)
      ((n:ℝ)*τ^(n-1)*(d (τ*t))^2+t*(2*τ^n*d (τ*t)*deriv d (τ*t))) τ := by
    have h := ((hasDerivAt_id τ).pow n).mul
      (((hd.differentiable (by norm_num) (τ*t)).hasDerivAt.comp τ ((hasDerivAt_id τ).mul_const t)).pow 2)
    convert h using 1 <;> try rfl
    simp only [Function.comp_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat,mul_one,one_mul]
    ring
  have hint : IntervalIntegrable (fun τ : ℝ => (n:ℝ)*τ^(n-1)*(d (τ*t))^2+
      t*(2*τ^n*d (τ*t)*deriv d (τ*t))) volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hder τ) hint
  simp only [one_pow,zero_pow hn.ne',one_mul,zero_mul,sub_zero] at hFTC
  rw [(averageProfile_hasDerivAt hn hd hB hdB t).deriv]
  unfold averageProfile averageProfileDeriv
  rw [←integral_const_mul,←integral_const_mul,←integral_add]
  · rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
    convert hFTC using 1
    congr 1
    funext τ
    ring
  · exact ((by fun_prop : Continuous (fun τ : ℝ => (n:ℝ)*(τ^(n-1)*(d (τ*t))^2)))).integrableOn_Icc
  · exact ((by fun_prop : Continuous (fun τ : ℝ => t*(2*τ^n*d (τ*t)*deriv d (τ*t))))).integrableOn_Icc
end CAT0Fillings.Conformal
end

section
open Set Filter MeasureTheory

namespace CAT0Fillings.Conformal
noncomputable def chordBubble (q a t : ℝ) : ℝ := (1+a*t^2)^(-q)
noncomputable def chordBubbleD (q a t : ℝ) : ℝ := -2*q*a*t*(1+a*t^2)^(-q-1)
noncomputable def chordBubbleDD (q a t : ℝ) : ℝ :=
  -2*q*a*(1+a*t^2)^(-q-1)+4*q*(q+1)*a^2*t^2*(1+a*t^2)^(-q-2)
lemma chordBubble_contDiff {a : ℝ} (ha : 0 ≤ a) (q : ℝ) (m : ℕ∞) :
    ContDiff ℝ m (chordBubble q a) := by
  exact (by fun_prop : ContDiff ℝ m (fun t : ℝ => 1+a*t^2)).rpow_const_of_ne
    (fun t => ne_of_gt (by positivity))
lemma chordBubbleD_contDiff {a : ℝ} (ha : 0 ≤ a) (q : ℝ) (m : ℕ∞) :
    ContDiff ℝ m (chordBubbleD q a) := by
  have h := (by fun_prop : ContDiff ℝ m (fun t : ℝ => 1+a*t^2)).rpow_const_of_ne
    (p := -q-1) (fun t => ne_of_gt (by positivity))
  exact (by fun_prop : ContDiff ℝ m (fun t : ℝ => -2*q*a*t)).mul h
lemma chordBubble_hasDerivAt {a : ℝ} (ha : 0 ≤ a) (q t : ℝ) :
    HasDerivAt (chordBubble q a) (chordBubbleD q a t) t := by
  have hb := (((hasDerivAt_id t).pow 2).const_mul a).const_add 1
  simp only [Pi.pow_apply,id_eq] at hb
  have hh := hb.rpow_const (p := -q) (Or.inl (ne_of_gt (by positivity)))
  convert hh using 1 <;> try rfl
  simp only [chordBubbleD,Nat.cast_ofNat,mul_one]
  ring
lemma chordBubbleD_hasDerivAt {a : ℝ} (ha : 0 ≤ a) (q t : ℝ) :
    HasDerivAt (chordBubbleD q a) (chordBubbleDD q a t) t := by
  have hb := (((hasDerivAt_id t).pow 2).const_mul a).const_add 1
  simp only [Pi.pow_apply,id_eq] at hb
  have hh := hb.rpow_const (p := -q-1) (Or.inl (ne_of_gt (by positivity)))
  have h := ((hasDerivAt_id t).const_mul (-2*q*a)).mul hh
  convert h using 1 <;> try rfl
  simp only [chordBubbleDD,id_eq,Nat.cast_ofNat,mul_one]
  rw [show -q-1-1 = -q-2 by ring]
  ring
lemma chordBubble_pos {a : ℝ} (ha : 0 ≤ a) (q t : ℝ) : 0 < chordBubble q a t :=
  Real.rpow_pos_of_pos (by positivity) _
lemma chordBubble_le_one {a q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (t : ℝ) : chordBubble q a t ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · nlinarith [mul_nonneg ha (sq_nonneg t)]
  · linarith
end CAT0Fillings.Conformal
end

end OAI
