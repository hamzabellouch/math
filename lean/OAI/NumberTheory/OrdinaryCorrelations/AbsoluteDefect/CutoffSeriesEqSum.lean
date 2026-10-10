import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Vertical

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex

namespace OrdinaryRieszPerron
open MeasureTheory Set Complex

lemma cutoffSeries_eq_sum (a : ℕ → ℂ) {X : ℝ} (hX : 0<X) :
    cutoffSeries a X = ∑n ∈ Finset.Icc 1 ⌊X⌋₊, a n*(1-(n:ℂ)/(X:ℂ)) := by
  unfold cutoffSeries
  rw [tsum_eq_sum (s:=Finset.Icc 1 ⌊X⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n≠0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
    have hx : (n:ℝ)/X∈Ioc (0:ℝ) 1 :=
      ⟨div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)) hX,
        (div_le_one hX).2 ((Nat.le_floor_iff hX.le).1 (Finset.mem_Icc.mp hn).2)⟩
    simp [hn0,riesz,hx]
  · intro n hn
    by_cases hn0 : n=0
    · simp [hn0]
    · have hnX : X<(n:ℝ) := by
        have hh : ¬n≤⌊X⌋₊ := fun hh => hn (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hn0,hh⟩)
        exact lt_of_not_ge (fun hh' => hh ((Nat.le_floor_iff hX.le).2 hh'))
      have hx : (n:ℝ)/X∉Ioc (0:ℝ) 1 := by
        intro hh
        have := (div_le_one hX).1 hh.2
        linarith
      simp [hn0,riesz,hx]

lemma LSeries_vertical_bound (a : ℕ → ℂ) {σ : ℝ} (ha : LSeriesSummable a (σ:ℂ)) (t : ℝ) :
    ‖LSeries a (vertical σ t)‖ ≤ ∑'n, ‖LSeries.term a (σ:ℂ) n‖ := by
  have hsum : Summable (fun n => ‖LSeries.term a (vertical σ t) n‖) :=
    ha.norm.congr (fun n => (term_norm_vertical a σ t n).symm)
  exact (norm_tsum_le_tsum_norm hsum).trans_eq (tsum_congr (term_norm_vertical a σ t))

lemma LSeries_vertical_continuous (a : ℕ → ℂ) {σ : ℝ}
    (ha : LSeries.abscissaOfAbsConv a<(σ:ℝ)) : Continuous (fun t : ℝ => LSeries a (vertical σ t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (LSeries_hasDerivAt (by simpa only [vertical_re] using ha)).continuousAt.comp
    (x:=t) (by unfold vertical; fun_prop)

lemma cauchy_LSeries_integrable (a : ℕ → ℂ) {σ : ℝ}
    (ha : LSeries.abscissaOfAbsConv a<(σ:ℝ)) :
    Integrable (fun t : ℝ => (1+t^2)⁻¹*‖LSeries a (vertical σ t)‖) := by
  have hs : LSeriesSummable a (σ:ℂ) := LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using ha)
  apply Integrable.mono' (integrable_inv_one_add_sq.mul_const (∑'n, ‖LSeries.term a (σ:ℂ) n‖))
  · apply Continuous.aestronglyMeasurable
    exact ((continuous_const.add (continuous_id.pow 2)).inv₀ (fun t => by dsimp; positivity) : Continuous (fun t : ℝ => (1+t^2)⁻¹)).mul (LSeries_vertical_continuous a ha).norm
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (LSeries_vertical_bound a hs t) (by positivity))

lemma scaled_LSeries_integrable (a : ℕ → ℂ) {X σ : ℝ} (hX : 0<X) (hσ : 1≤σ)
    (ha : LSeries.abscissaOfAbsConv a<(σ:ℝ)) :
    Integrable (fun t : ℝ => (X:ℂ)^(vertical σ t)*LSeries a (vertical σ t)*kernel (vertical σ t)) := by
  apply Integrable.mono' ((cauchy_LSeries_integrable a ha).const_mul (X^σ))
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul _ (continuous_vertical_kernel hσ)
    apply Continuous.mul _ (LSeries_vertical_continuous a ha)
    apply Continuous.const_cpow
    · unfold vertical
      fun_prop
    · exact Or.inl (Complex.ofReal_ne_zero.mpr hX.ne')
  · exact Filter.Eventually.of_forall (fun t => by
      rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,vertical_re]
      calc
        X^σ*‖LSeries a (vertical σ t)‖*‖kernel (vertical σ t)‖ ≤
          X^σ*‖LSeries a (vertical σ t)‖*(1+t^2)⁻¹ :=
            mul_le_mul_of_nonneg_left (kernel_norm_le hσ t) (by positivity)
        _ = _ := by ring)

theorem cutoffSeries_norm_le (a : ℕ → ℂ) {X σ : ℝ} (hX : 0<X) (hσ : 1≤σ)
    (ha : LSeries.abscissaOfAbsConv a<(σ:ℝ)) :
    ‖cutoffSeries a X‖ ≤ (1/(2*Real.pi))*X^σ*
      (∫t : ℝ, (1+t^2)⁻¹*‖LSeries a (vertical σ t)‖) := by
  have hs : LSeriesSummable a (σ:ℂ) := LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using ha)
  rw [cutoffSeries_perron a hX hσ hs,norm_mul]
  have hc : ‖perronConstant‖=1/(2*Real.pi) := by
    unfold perronConstant
    rw [Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  rw [hc,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (MeasureTheory.norm_integral_le_integral_norm _).trans
  rw [←MeasureTheory.integral_const_mul]
  apply integral_mono (scaled_LSeries_integrable a hX hσ ha).norm ((cauchy_LSeries_integrable a ha).const_mul (X^σ))
  intro t
  dsimp only
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,vertical_re]
  calc
    X^σ*‖LSeries a (vertical σ t)‖*‖kernel (vertical σ t)‖ ≤
      X^σ*‖LSeries a (vertical σ t)‖*(1+t^2)⁻¹ :=
        mul_le_mul_of_nonneg_left (kernel_norm_le hσ t) (by positivity)
    _ = _ := by ring

end OrdinaryRieszPerron

end

end OAI
