import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightLogBins

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open Construction Characters.RationalHistory
variable {κ : Type*} [DecidableEq κ]

theorem realStateBins_logCurve_deriv_bound (b s : ℕ) (tb td : ℝ) (a : State) (outside : List ℕ)
    (q : Fin a.small.length → κ) (x : κ → ℝ) (i : κ) (D : ℝ)
    (hx : ∀ j, 0 < x j) (hD : 0 ≤ D) (hφ : ∀ z, |deriv smoothPartition z| ≤ D) :
    |deriv (fun t => realStateBins b s tb td a outside
      (fun j => Expr.logCurve x i t (q j)) (fun j => (outside.get j:ℝ))) 0| ≤
      2 * D * a.small.length := by
  classical
  let S (h : Bool) : Finset (Fin a.small.length) :=
    Finset.univ.filter (fun j => sourceBulkHalf b h (a.small.get j))
  let C (h : Bool) : ℝ := smoothPartition
    ((∑ j, if sourceSpectatorHalf s h j.val then Real.log (outside.get j:ℝ) else 0) - td)
  let f (h : Bool) (t : ℝ) := logSumCell (S h) q x i tb t * C h
  let df (h : Bool) := deriv (logSumCell (S h) q x i tb) 0 * C h
  have hfun : (fun t => realStateBins b s tb td a outside
      (fun j => Expr.logCurve x i t (q j)) (fun j => (outside.get j:ℝ))) =
      (fun t => ∏ h : Bool, f h t) := by
    funext t
    simp only [realStateBins,f,logSumCell,S,C,Finset.sum_filter]
  have hC (h : Bool) : 0 ≤ C h ∧ C h ≤ 1 :=
    ⟨smoothPartition_nonneg _,smoothPartition_le_one _⟩
  have hf (h : Bool) : HasDerivAt (f h) (df h) 0 :=
    ((logSumCell_hasDerivAt (S h) q x i tb (fun j _ => hx (q j))).differentiableAt.hasDerivAt).mul_const (C h)
  have hn (h : Bool) : ‖f h 0‖ ≤ 1 := by
    change ‖logSumCell (S h) q x i tb 0 * C h‖ ≤ 1
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hC h).1]
    unfold logSumCell
    rw [abs_of_nonneg (smoothPartition_nonneg _)]
    exact (mul_le_mul (smoothPartition_le_one _) (hC h).2 (hC h).1 zero_le_one).trans_eq (one_mul 1)
  have hd (h : Bool) : ‖df h‖ ≤ D * a.small.length := by
    have hb := logSumCell_deriv_bound (S h) q x i tb D (fun j _ => hx (q j)) hD hφ
    have hcard : (S h).card ≤ a.small.length := by
      exact (Finset.card_filter_le _ _).trans_eq (by simp)
    change ‖deriv (logSumCell (S h) q x i tb) 0 * C h‖ ≤ _
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hC h).1]
    calc
      _ ≤ (D * (S h).card) * 1 := mul_le_mul hb (hC h).2 (hC h).1 (by positivity)
      _ ≤ _ := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hD
  rw [hfun,← Real.norm_eq_abs]
  have hh := norm_deriv_finsetProd_le (Finset.univ : Finset Bool) f df
    (fun _ => D*a.small.length) 0 (fun h _ => hf h) (fun h _ => hn h) (fun h _ => hd h)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_bool,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using hh

theorem source_bins_uniform_log_deriv : ∃ D : ℝ, 0 < D ∧
    ∀ {κ : Type} [DecidableEq κ] (b s : ℕ) (tb td : ℝ) (a : State) (outside : List ℕ)
      (q : Fin a.small.length → κ) (x : κ → ℝ) (i : κ),
      (∀ j, 0 < x j) →
      |deriv (fun t => realStateBins b s tb td a outside
        (fun j => Expr.logCurve x i t (q j)) (fun j => (outside.get j:ℝ))) 0| ≤ D*a.small.length := by
  obtain ⟨D,hD,hφ⟩ := smoothPartition_deriv_uniform
  refine ⟨2*D,by positivity,?_⟩
  intro κ _ b s tb td a outside q x i hx
  exact realStateBins_logCurve_deriv_bound b s tb td a outside q x i D hx hD.le hφ

end Ostmann.Arithmetic

end

end OAI
