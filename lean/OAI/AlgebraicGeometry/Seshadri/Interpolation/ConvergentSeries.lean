import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Analytic.ConvergentSeries

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set
abbrev Exponent := ℕ × ℕ

noncomputable def monomialDeriv (n a : ℕ) (x : ℂ) : ℂ :=
  (n.descFactorial a : ℂ) * x ^ (n - a)

lemma monomialDeriv_eq (n a : ℕ) :
    monomialDeriv n a = iteratedDeriv a (fun x : ℂ => x ^ n) := by
  ext x
  simp only [monomialDeriv, iteratedDeriv_pow]

lemma deriv_monomialDeriv (n a : ℕ) :
    deriv (monomialDeriv n a) = monomialDeriv n (a + 1) := by
  simp only [monomialDeriv_eq, iteratedDeriv_succ]

lemma differentiable_monomialDeriv (n a : ℕ) :
    Differentiable ℂ (monomialDeriv n a) := by
  unfold monomialDeriv
  fun_prop

noncomputable def seriesPartial (c : Exponent → ℂ) (a b : ℕ) (x z : ℂ) : ℂ :=
  ∑' p : Exponent, c p * monomialDeriv p.1 a x * monomialDeriv p.2 b z

noncomputable def seriesEval (c : Exponent → ℂ) (x z : ℂ) : ℂ :=
  ∑' p : Exponent, c p * x ^ p.1 * z ^ p.2

lemma seriesPartial_zero (c : Exponent → ℂ) : seriesPartial c 0 0 = seriesEval c := by
  ext x z
  simp [seriesPartial, seriesEval, monomialDeriv]

noncomputable def derivativeMajorant (c : Exponent → ℂ) (R : ℝ) (a b : ℕ)
    (p : Exponent) : ℝ :=
  ‖c p‖ * ((p.1.descFactorial a : ℝ) * R ^ (p.1 - a)) *
    ((p.2.descFactorial b : ℝ) * R ^ (p.2 - b))

def DerivativeSummable (c : Exponent → ℂ) (R : ℝ) : Prop :=
  ∀ a b : ℕ, Summable (derivativeMajorant c R a b)

lemma norm_monomialDeriv_le (n a : ℕ) (x : ℂ) (R : ℝ) (hx : ‖x‖ ≤ R) :
    ‖monomialDeriv n a x‖ ≤ (n.descFactorial a : ℝ) * R ^ (n - a) := by
  simp only [monomialDeriv, norm_mul, norm_natCast, norm_pow]
  gcongr

lemma norm_seriesTerm_le (c : Exponent → ℂ) (R : ℝ) (a b : ℕ) (p : Exponent)
    (x z : ℂ) (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    ‖c p * monomialDeriv p.1 a x * monomialDeriv p.2 b z‖ ≤
      derivativeMajorant c R a b p := by
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_monomialDeriv_le _ _ _ _ hx)
    (norm_nonneg _)) (norm_monomialDeriv_le _ _ _ _ hz) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg
      ((norm_nonneg x).trans hx) _)))

lemma summable_seriesPartial (c : Exponent → ℂ) (R : ℝ) (hs : DerivativeSummable c R)
    (a b : ℕ) (x z : ℂ) (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    Summable (fun p : Exponent => c p * monomialDeriv p.1 a x * monomialDeriv p.2 b z) :=
  (hs a b).of_norm_bounded (fun p => norm_seriesTerm_le c R a b p x z hx hz)

lemma deriv_seriesPartial_left (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ ≤ R) :
    deriv (fun w => seriesPartial c a b w z) x = seriesPartial c (a + 1) b x z := by
  have hsum := Complex.hasSum_deriv_of_summable_norm (hs a b)
    (U := Metric.ball (0 : ℂ) R)
    (F := fun p : Exponent => fun w : ℂ => c p * monomialDeriv p.1 a w *
      monomialDeriv p.2 b z)
    (fun p => ((differentiable_monomialDeriv p.1 a).const_mul (c p)).mul_const
      (monomialDeriv p.2 b z) |>.differentiableOn)
    Metric.isOpen_ball
    (fun p w hw => norm_seriesTerm_le c R a b p w z
      (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hw).le) hz)
    (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
  have he (p : Exponent) :
      deriv (fun w : ℂ => c p * monomialDeriv p.1 a w * monomialDeriv p.2 b z) x =
        c p * monomialDeriv p.1 (a + 1) x * monomialDeriv p.2 b z := by
    rw [deriv_mul_const_field, deriv_const_mul_field, deriv_monomialDeriv]
  simpa only [seriesPartial, he] using hsum.tsum_eq.symm

lemma deriv_seriesPartial_right (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ ≤ R) (hz : ‖z‖ < R) :
    deriv (fun w => seriesPartial c a b x w) z = seriesPartial c a (b + 1) x z := by
  have hsum := Complex.hasSum_deriv_of_summable_norm (hs a b)
    (U := Metric.ball (0 : ℂ) R)
    (F := fun p : Exponent => fun w : ℂ => c p * monomialDeriv p.1 a x *
      monomialDeriv p.2 b w)
    (fun p => ((differentiable_monomialDeriv p.2 b).const_mul
      (c p * monomialDeriv p.1 a x)).differentiableOn)
    Metric.isOpen_ball
    (fun p w hw => norm_seriesTerm_le c R a b p x w hx
      (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hw).le))
    (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have he (p : Exponent) :
      deriv (fun w : ℂ => c p * monomialDeriv p.1 a x * monomialDeriv p.2 b w) z =
        c p * monomialDeriv p.1 a x * monomialDeriv p.2 (b + 1) z := by
    rw [deriv_const_mul_field, deriv_monomialDeriv]
  simpa only [seriesPartial, he] using hsum.tsum_eq.symm

lemma iteratedDeriv_series_left (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ < R) :
    iteratedDeriv a (fun w => seriesEval c w z) x = seriesPartial c a 0 x z := by
  induction a generalizing x with
  | zero => simp [← seriesPartial_zero]
  | succ a ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv a (fun w => seriesEval c w z) =ᶠ[𝓝 x]
        (fun w => seriesPartial c a 0 w z) := by
      filter_upwards [((continuous_norm.tendsto x).eventually (gt_mem_nhds hx))] with w hw
      exact ih w hw
    rw [he.deriv_eq]
    exact deriv_seriesPartial_left c R hs a 0 x z hx hz.le

lemma iteratedDeriv_series_right (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ < R) :
    iteratedDeriv b (fun w => seriesPartial c a 0 x w) z = seriesPartial c a b x z := by
  induction b generalizing z with
  | zero => rfl
  | succ b ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv b (fun w => seriesPartial c a 0 x w) =ᶠ[𝓝 z]
        (fun w => seriesPartial c a b x w) := by
      filter_upwards [((continuous_norm.tendsto z).eventually (gt_mem_nhds hz))] with w hw
      exact ih w hw
    rw [he.deriv_eq]
    exact deriv_seriesPartial_right c R hs a b x z hx.le hz

theorem mixedDeriv_seriesEval (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ < R) :
    iteratedDeriv b (fun v => iteratedDeriv a (fun u => seriesEval c u v) x) z =
      seriesPartial c a b x z := by
  have he : (fun v => iteratedDeriv a (fun u => seriesEval c u v) x) =ᶠ[𝓝 z]
      (fun v => seriesPartial c a 0 x v) := by
    filter_upwards [((continuous_norm.tendsto z).eventually (gt_mem_nhds hz))] with v hv
    exact iteratedDeriv_series_left c R hs a x v hx hv
  rw [he.iteratedDeriv_eq b]
  exact iteratedDeriv_series_right c R hs a b x z hx hz

def AbsolutelyConvergentAt (c : Exponent → ℂ) (R : ℝ) : Prop :=
  Summable (fun p : Exponent => ‖c p‖ * R ^ (p.1 + p.2))

def ConvergentSeries (c : Exponent → ℂ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ AbsolutelyConvergentAt c R

lemma descFactorial_radius_le (n a : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    (n.descFactorial a : ℝ) * ρ ^ (n - a) ≤
      (n : ℝ) ^ a * (ρ ^ n / ρ ^ a) := by
  by_cases h : a ≤ n
  · have he : ρ ^ (n - a) = ρ ^ n / ρ ^ a := by
      apply (eq_div_iff (pow_ne_zero _ hρ.ne')).2
      rw [← pow_add, Nat.sub_add_cancel h]
    rw [← he]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.descFactorial_le_pow n a)
      (pow_nonneg hρ.le _)
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero, zero_mul]
    positivity

theorem derivativeSummable_of_absolute (c : Exponent → ℂ) (R ρ : ℝ)
    (hR : 0 < R) (hρ : 0 < ρ) (hsmall : ρ < R)
    (hc : AbsolutelyConvergentAt c R) : DerivativeSummable c ρ := by
  let C : ℝ := ∑' p : Exponent, ‖c p‖ * R ^ (p.1 + p.2)
  have hC : 0 ≤ C := tsum_nonneg (fun p => by positivity)
  have hb (p : Exponent) : ‖c p‖ ≤ C / R ^ (p.1 + p.2) := by
    apply (le_div_iff₀ (pow_pos hR _)).2
    exact hc.le_tsum p (fun p _ => by positivity)
  have ht0 : 0 ≤ ρ / R := div_nonneg hρ.le hR.le
  have ht : ‖ρ / R‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht0]
    exact (div_lt_one hR).2 hsmall
  intro a b
  have hsum := ((summable_pow_mul_geometric_of_norm_lt_one a ht).mul_of_nonneg
    (summable_pow_mul_geometric_of_norm_lt_one b ht)
    (fun n => by positivity) (fun n => by positivity)).mul_left (C / (ρ ^ a * ρ ^ b))
  refine Summable.of_nonneg_of_le (fun p => by unfold derivativeMajorant; positivity)
    (fun p => ?_) hsum
  unfold derivativeMajorant
  calc
    _ ≤ (C / R ^ (p.1 + p.2)) *
        ((p.1 : ℝ) ^ a * (ρ ^ p.1 / ρ ^ a)) *
        ((p.2 : ℝ) ^ b * (ρ ^ p.2 / ρ ^ b)) := by
      apply mul_le_mul _ (descFactorial_radius_le p.2 b ρ hρ) (by positivity) (by positivity)
      exact mul_le_mul (hb p) (descFactorial_radius_le p.1 a ρ hρ)
        (by positivity) (by positivity)
    _ = C / (ρ ^ a * ρ ^ b) *
        ((p.1 : ℝ) ^ a * (ρ / R) ^ p.1 * ((p.2 : ℝ) ^ b * (ρ / R) ^ p.2)) := by
      rw [pow_add, div_pow, div_pow]
      ring

lemma derivativeSummable_of_norm_le (c d : Exponent → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hd : DerivativeSummable d R) (hcd : ∀ p, ‖c p‖ ≤ ‖d p‖) : DerivativeSummable c R := by
  intro a b
  refine Summable.of_nonneg_of_le (fun p => by unfold derivativeMajorant; positivity)
    (fun p => ?_) (hd a b)
  unfold derivativeMajorant
  gcongr
  exact hcd p

theorem mixedDeriv_limit_of_coefficients {α : Type*} (l : Filter α)
    (c : α → Exponent → ℂ) (c₀ d : Exponent → ℂ) (R : ℝ) (hR : 0 < R)
    (hd : DerivativeSummable d R)
    (hlim : ∀ p, Tendsto (fun v => c v p) l (𝓝 (c₀ p)))
    (hb : ∀ᶠ v in l, ∀ p, ‖c v p‖ ≤ ‖d p‖)
    (a b : ℕ) (x z : ℂ) (hx : ‖x‖ < R) (hz : ‖z‖ < R) :
    Tendsto (fun v => iteratedDeriv b (fun y => iteratedDeriv a
      (fun w => seriesEval (c v) w y) x) z) l (𝓝 (seriesPartial c₀ a b x z)) := by
  have hsum := tendsto_tsum_of_dominated_convergence (hd a b)
    (fun p => ((hlim p).mul_const (monomialDeriv p.1 a x)).mul_const
      (monomialDeriv p.2 b z))
    (hb.mono (fun v hv p => (norm_seriesTerm_le (c v) R a b p x z hx.le hz.le).trans (by
      unfold derivativeMajorant
      gcongr
      exact hv p)))
  apply hsum.congr'
  filter_upwards [hb] with v hv
  exact (mixedDeriv_seriesEval (c v) R (derivativeSummable_of_norm_le _ _ _ hR.le hd hv)
    a b x z hx hz).symm


end MaximalSeshadri.Interpolation
end

end OAI
