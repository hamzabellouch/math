import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightArchimedean
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightProductDeriv

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open Characters.RationalHistory
open scoped ContDiff

theorem counterpartNormalization_hasDerivAt {κ : Type*} [DecidableEq κ]
    (H u : Expr κ) (x : κ → ℝ) (j : κ) (T U K : ℝ)
    (hH : H.RelativeControl x K) (hu : u.RelativeControl x K) :
    HasDerivAt (fun t => (Real.exp T / H.realEval (Expr.logCurve x j t)) *
      (u.realEval (Expr.logCurve x j t) / Real.exp U))
      ((Real.exp T / H.realEval x) * (u.realEval x / Real.exp U) *
        (u.logSlope x j - H.logSlope x j)) 0 := by
  have hdH := H.hasDerivAt_logCurve x j (Expr.RelativeControl.regular H x K hH)
  have hdu := u.hasDerivAt_logCurve x j (Expr.RelativeControl.regular u x K hu)
  have hH0 := Expr.RelativeControl.value_ne_zero H x K hH
  have hu0 := Expr.RelativeControl.value_ne_zero u x K hu
  have heU := (Real.exp_pos U).ne'
  convert ((hasDerivAt_const (0 : ℝ) (Real.exp T)).fun_div hdH
    (by simpa only [Expr.logCurve_zero] using hH0)).fun_mul (hdu.div_const (Real.exp U)) using 1
  simp only [Expr.logCurve_zero, Expr.logSlope]
  field_simp
  ring

theorem counterpartArchimedean_logCurve_deriv_bound : ∃ D : ℝ, 0 < D ∧
    ∀ {κ ι : Type} [DecidableEq κ] (H u : Expr κ) (p : ι → Expr κ)
      (x : κ → ℝ) (j : κ) (S : Finset ι) (center : ι → ℝ) (T U WH Wu K : ℝ),
      1 ≤ K → H.RelativeControl x K → u.RelativeControl x K →
      (∀ i ∈ S, (p i).RelativeControl x K) →
      0 < H.realEval x → 0 < u.realEval x →
      T - WH ≤ Real.log (H.realEval x) → Real.log (u.realEval x) ≤ U + Wu →
      |deriv (fun t => counterpartArchimedean T U
        (H.realEval (Expr.logCurve x j t)) (u.realEval (Expr.logCurve x j t))
        S center (fun i => (p i).realEval (Expr.logCurve x j t))) 0| ≤
        Real.exp (WH + Wu) *
          (H.logBudget K + u.logBudget K + D * ∑ i ∈ S, (p i).logBudget K) := by
  obtain ⟨D,hD,hDb⟩ := giantCell_logCurve_deriv_bound
  refine ⟨D,hD,?_⟩
  intro κ ι _ H u p x j S center T U WH Wu K hK hH hu hp hHpos hupos hlogH hlogu
  classical
  let A : ℝ → ℝ := fun t => (Real.exp T / H.realEval (Expr.logCurve x j t)) *
    (u.realEval (Expr.logCurve x j t) / Real.exp U)
  let f : ι → ℝ → ℝ := fun i t => giantCell (center i) ((p i).realEval (Expr.logCurve x j t))
  let P : ℝ → ℝ := fun t => ∏ i ∈ S, f i t
  have hA : HasDerivAt A (A 0 * (u.logSlope x j - H.logSlope x j)) 0 := by
    simpa only [A,Expr.logCurve_zero] using counterpartNormalization_hasDerivAt H u x j T U K hH hu
  have hApos : 0 < A 0 := by
    dsimp only [A]
    rw [Expr.logCurve_zero]
    exact mul_pos (div_pos (Real.exp_pos _) hHpos) (div_pos hupos (Real.exp_pos _))
  have hAb : A 0 ≤ Real.exp (WH + Wu) := by
    simpa only [counterpartArchimedean,Finset.prod_empty,mul_one,A,Expr.logCurve_zero] using
      counterpartArchimedean_le T U (H.realEval x) (u.realEval x) WH Wu
        (∅ : Finset ι) center (fun i => (p i).realEval x) hHpos hupos hlogH hlogu
  have hf (i : ι) (hi : i ∈ S) : HasDerivAt (f i) (deriv (f i) 0) 0 := by
    have he := (p i).hasDerivAt_logCurve x j (Expr.RelativeControl.regular (p i) x K (hp i hi))
    have hg := (((giantCell_contDiff (center i)).differentiable (by simp)) ((p i).realEval x)).hasDerivAt
    exact (hg.comp_of_eq 0 he (by rw [Expr.logCurve_zero])).differentiableAt.hasDerivAt
  have hfn (i : ι) : ‖f i 0‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (giantCell_bounds _ _).1]
    exact (giantCell_bounds _ _).2
  have hfd (i : ι) (hi : i ∈ S) : ‖deriv (f i) 0‖ ≤ D * (p i).logBudget K := by
    exact hDb (p i) x j (center i) K hK (hp i hi)
  have hPd : |deriv P 0| ≤ D * ∑ i ∈ S, (p i).logBudget K := by
    simpa only [Real.norm_eq_abs,← Finset.mul_sum,P] using
      norm_deriv_finsetProd_le S f (fun i => deriv (f i) 0)
        (fun i => D * (p i).logBudget K) 0 hf (fun i _ => hfn i) hfd
  have hP : HasDerivAt P (deriv P 0) 0 :=
    (HasDerivAt.fun_finsetProd hf).differentiableAt.hasDerivAt
  have hPnonneg : 0 ≤ P 0 := Finset.prod_nonneg (fun i _ => (giantCell_bounds _ _).1)
  have hPn : |P 0| ≤ 1 := by
    rw [abs_of_nonneg hPnonneg]
    exact Finset.prod_le_one₀ (fun i _ => (giantCell_bounds _ _).1)
      (fun i _ => (giantCell_bounds _ _).2)
  have hSlope : |u.logSlope x j - H.logSlope x j| ≤ H.logBudget K + u.logBudget K := by
    exact (Expr.abs_sub_le_abs_sum _ _).trans (by
      simpa only [add_comm] using add_le_add (Expr.logSlope_bound u x j hK hu)
        (Expr.logSlope_bound H x j hK hH))
  change |deriv (fun t => A t * P t) 0| ≤ _
  rw [(hA.fun_mul hP).deriv]
  calc
    _ ≤ |A 0 * (u.logSlope x j - H.logSlope x j) * P 0| + |A 0 * deriv P 0| := abs_add_le _ _
    _ = A 0 * |u.logSlope x j - H.logSlope x j| * |P 0| + A 0 * |deriv P 0| := by
      rw [abs_mul (A 0 * _) (P 0), abs_mul (A 0) (u.logSlope x j - H.logSlope x j),
        abs_mul (A 0) (deriv P 0), abs_of_pos hApos]
    _ ≤ A 0 * (H.logBudget K + u.logBudget K) * 1 +
        A 0 * (D * ∑ i ∈ S, (p i).logBudget K) := by
      exact add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left hSlope hApos.le) hPn (abs_nonneg _)
          (mul_nonneg hApos.le (add_nonneg (H.logBudget_nonneg (by linarith))
            (u.logBudget_nonneg (by linarith)))))
        (mul_le_mul_of_nonneg_left hPd hApos.le)
    _ = A 0 * (H.logBudget K + u.logBudget K + D * ∑ i ∈ S, (p i).logBudget K) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hAb (by
      exact add_nonneg (add_nonneg (H.logBudget_nonneg (by linarith))
        (u.logBudget_nonneg (by linarith)))
        (mul_nonneg hD.le (Finset.sum_nonneg (fun i _ => (p i).logBudget_nonneg (by linarith)))))

end Ostmann.Arithmetic

end

end OAI
