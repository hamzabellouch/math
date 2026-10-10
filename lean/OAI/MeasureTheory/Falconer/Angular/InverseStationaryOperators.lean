import OAI.MeasureTheory.Falconer.Angular.StationaryDifferentialExpr
import OAI.MeasureTheory.Falconer.Angular.AngularDifferentialBounds

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

noncomputable def inverseStationaryExpr : ℕ → AngularDifferentialExpr
  | 0 => .term stationaryLeadingConstant⁻¹ 0
  | n+1 => .comp (.term (-stationaryLeadingConstant⁻¹) 0)
      (angularFiniteSum (Finset.range (n+1)) (fun k =>
        .comp (directStationaryExpr (k+1)) (inverseStationaryExpr (n-k))))
termination_by n => n
decreasing_by omega

noncomputable def inverseStationaryOperator (j : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (inverseStationaryExpr j).apply f

theorem inverseStationaryExpr_order (n : ℕ) : (inverseStationaryExpr n).order ≤ 2*n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [inverseStationaryExpr, AngularDifferentialExpr.order]
    | succ n =>
      simp only [inverseStationaryExpr, AngularDifferentialExpr.order, zero_add]
      apply angularFiniteSum_order
      intro k hk
      have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
      have hi := ih (n-k) (by omega)
      have hd := directStationaryExpr_order (k+1)
      change (directStationaryExpr (k+1)).order + (inverseStationaryExpr (n-k)).order ≤ _
      omega

theorem inverseStationaryOperator_contDiff (n : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (inverseStationaryOperator n f) :=
  (inverseStationaryExpr n).apply_contDiff hf

theorem inverseStationaryOperator_zero (f : ℝ → ℂ) (x : ℝ) :
    inverseStationaryOperator 0 f x = stationaryLeadingConstant⁻¹ * f x := by
  simp [inverseStationaryOperator, inverseStationaryExpr, AngularDifferentialExpr.apply]

theorem inverseStationaryOperator_succ (n : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    inverseStationaryOperator (n+1) f x = -stationaryLeadingConstant⁻¹ *
      ∑ k ∈ Finset.range (n+1),
        directStationaryOperator (k+1) (inverseStationaryOperator (n-k) f) x := by
  simp only [inverseStationaryOperator, inverseStationaryExpr, AngularDifferentialExpr.apply,
    iteratedDeriv_zero, angularFiniteSum_apply, directStationaryExpr_apply]

theorem inverseStationaryOperator_derivative_bound (n m : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (x : ℝ)
    (hb : ∀ k ≤ m+2*n, ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ‖iteratedDeriv m (inverseStationaryOperator n f) x‖ ≤
      (inverseStationaryExpr n).cost * (C*D^(m+2*n)) :=
  (inverseStationaryExpr n).derivative_bound_of_order_le
    (inverseStationaryExpr_order n) hf hC hD m x hb

theorem inverseStationaryOperator_tsupport (n : ℕ) (f : ℝ → ℂ) :
    tsupport (inverseStationaryOperator n f) ⊆ tsupport f :=
  (inverseStationaryExpr n).apply_tsupport f

theorem inverseStationaryOperator_cancellation_zero {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    directStationaryOperator 0 (inverseStationaryOperator 0 f) x = f x := by
  rw [directStationaryOperator_zero (inverseStationaryOperator_contDiff 0 hf),
    inverseStationaryOperator_zero]
  change stationaryLeadingConstant * (stationaryLeadingConstant⁻¹ * f x) = f x
  rw [← mul_assoc, mul_inv_cancel₀ stationaryLeadingConstant_ne_zero, one_mul]

theorem inverseStationaryOperator_cancellation_succ (n : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    directStationaryOperator 0 (inverseStationaryOperator (n+1) f) x +
      (∑ k ∈ Finset.range (n+1),
        directStationaryOperator (k+1) (inverseStationaryOperator (n-k) f) x) = 0 := by
  rw [directStationaryOperator_zero (inverseStationaryOperator_contDiff (n+1) hf),
    inverseStationaryOperator_succ]
  change stationaryLeadingConstant * (-stationaryLeadingConstant⁻¹ * _) + _ = 0
  rw [← mul_assoc, mul_neg, mul_inv_cancel₀ stationaryLeadingConstant_ne_zero]
  ring

theorem inverseStationaryOperator_cancellation (n : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    (∑ h ∈ Finset.range (n+1),
      directStationaryOperator h (inverseStationaryOperator (n-h) f) x) =
        if n = 0 then f x else 0 := by
  cases n with
  | zero => simpa using inverseStationaryOperator_cancellation_zero hf x
  | succ n =>
    rw [Finset.sum_range_succ']
    simpa [Nat.succ_sub_succ_eq_sub, add_comm] using
      inverseStationaryOperator_cancellation_succ n hf x

end PlanarFalconer

end OAI
