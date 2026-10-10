import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ConstructionFamily

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldOrderedLimits

open AllFieldHistory AllFieldNativeCapacity AllFieldScheduledYield
open AllFieldConstructionRates Filter
open scoped Topology

variable (F : Type*) [Field F]

theorem fixed_lot_constraint (K : ℕ) (hK : 2 ≤ K)
    (hgap : nativeB < nativeHigh)
    (hfeas : ∀ i, nativeCstar - (nativeLA i + nativeLB i) < nativeHigh)
    (ha : ∀ i, 0 < nativeLA i) (hb : ∀ i, 0 < nativeLB i)
    (hc : ∀ i, 0 < nativeLC nativeLambda i) :
    AllFieldInitialEntropy.nativeH0 + nativeCstar - nativeBeta / (K : ℝ) +
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
  obtain ⟨allocation, halloc⟩ := exists_balanced_allocation_sequence hgap hfeas
  have hcap := eventually_capacity_pos hK allocation halloc ha hb hc
  have hy := (physicalYield_tendsto_balanced K hK hgap allocation halloc).div_const (K : ℝ)
  have hH0 : Tendsto (fun _ : ℕ => AllFieldInitialEntropy.nativeH0) atTop
      (𝓝 AllFieldInitialEntropy.nativeH0) := tendsto_const_nhds
  have hlimit := (hH0.add hy).add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S) atTop (𝓝 _))
  have hineq : AllFieldInitialEntropy.nativeH0 +
      ((K : ℝ) * nativeCstar - nativeBeta) / (K : ℝ) +
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
    apply le_of_tendsto_of_tendsto hlimit tendsto_const_nhds
    filter_upwards [hcap] with j hj
    exact AllFieldConstructionFamily.fixed_allocation_constraint F (by omega)
      (allocation j) hj
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have heq : ((K : ℝ) * nativeCstar - nativeBeta) / (K : ℝ) =
      nativeCstar - nativeBeta / (K : ℝ) := by
    rw [sub_div, mul_div_cancel_left₀ _ hk]
  rw [heq] at hineq
  simpa only [← add_sub_assoc] using hineq

theorem native_rank_constraint
    (hgap : nativeB < nativeHigh)
    (hfeas : ∀ i, nativeCstar - (nativeLA i + nativeLB i) < nativeHigh)
    (ha : ∀ i, 0 < nativeLA i) (hb : ∀ i, 0 < nativeLB i)
    (hc : ∀ i, 0 < nativeLC nativeLambda i) :
    AllFieldInitialEntropy.nativeH0 + nativeCstar +
      (Arithmetic.omega F / 3) * AllFieldTerminalRates.S ≤ 8 * Real.log 7 := by
  have hfixed (K : ℕ) (hK : 2 ≤ K) :
      (AllFieldInitialEntropy.nativeH0 + nativeCstar) - nativeBeta / (K : ℝ) +
        Arithmetic.omega F * AllFieldTerminalRates.S / 3 ≤ 8 * Real.log 7 := by
    have h := fixed_lot_constraint F K hK hgap hfeas ha hb hc
    nlinarith
  have h := FiniteSchedule.fixed_lot_boundary_limit hfixed
  nlinarith

theorem omega_le_native_ratio
    (hgap : nativeB < nativeHigh)
    (hfeas : ∀ i, nativeCstar - (nativeLA i + nativeLB i) < nativeHigh)
    (ha : ∀ i, 0 < nativeLA i) (hb : ∀ i, 0 < nativeLB i)
    (hc : ∀ i, 0 < nativeLC nativeLambda i)
    (hS : 0 < AllFieldTerminalRates.S) :
    Arithmetic.omega F ≤
      3 * (8 * Real.log 7 -
        (AllFieldInitialEntropy.nativeH0 + nativeCstar)) / AllFieldTerminalRates.S := by
  apply (le_div_iff₀ hS).mpr
  have h := native_rank_constraint F hgap hfeas ha hb hc
  nlinarith

end MatrixMultiplication.AllFieldOrderedLimits

end

end OAI
