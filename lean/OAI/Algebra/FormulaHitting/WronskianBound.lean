import OAI.Algebra.FormulaHitting.OrderBasis
import OAI.Algebra.FormulaHitting.Minors

namespace OAI

noncomputable section

namespace NCHitting

open PowerSeries Matrix Submodule

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem derivativeIter_X_dvd (f : PowerSeries F) {a j : ℕ}
    (h : a+j ≤ f.order.toNat) :
    PowerSeries.X^a ∣ derivativeIter j f := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro r hr
  rw [coeff_derivativeIter, PowerSeries.coeff_of_lt_order_toNat _ (by omega), zero_mul]

omit [CharZero F] in
theorem derivativeIter_column_X_dvd (f : PowerSeries F) {k : ℕ}
    (j : Fin k) :
    PowerSeries.X^(f.order.toNat+1-k) ∣ derivativeIter j.val f := by
  by_cases hk : k ≤ f.order.toNat+1
  · apply derivativeIter_X_dvd
    have hj := j.isLt
    omega
  · have ha : f.order.toNat+1-k = 0 := by omega
    simp [ha]

omit [CharZero F] in
theorem order_le_wronskian_add {k : ℕ} (b : Fin k → PowerSeries F)
    (hb : wronskian b ≠ 0) (y : PowerSeries F) (hy : y ≠ 0)
    (hspan : y ∈ Submodule.span F (Set.range b)) :
    y.order.toNat ≤ (wronskian b).order.toNat + k - 1 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hspan
  have hex : ∃ l, c l ≠ 0 := by
    by_contra h
    push Not at h
    apply hy
    rw [← hc]
    simp [h]
  obtain ⟨l, hl⟩ := hex
  let W := (wronskianMatrix b).updateCol l (fun j => derivativeIter j.val y)
  have he : W.det = PowerSeries.C (c l) * wronskian b := by
    have hcol : (fun j : Fin k => derivativeIter j.val y) =
        fun j => ∑ i : Fin k, PowerSeries.C (c i) • wronskianMatrix b j i := by
      funext j
      rw [← hc, derivativeIter_sum]
      simp only [derivativeIter_smul]
      simp only [wronskianMatrix, PowerSeries.smul_eq_C_mul, smul_eq_mul]
    change ((wronskianMatrix b).updateCol l _).det = _
    rw [hcol, Matrix.det_updateCol_sum]
    rfl
  have hd : PowerSeries.X^(y.order.toNat+1-k) ∣ W.det := by
    apply dvd_det_of_column_dvd W l
    intro j
    simpa [W] using derivativeIter_column_X_dvd y j
  have hco : (PowerSeries.C (c l)).order = 0 := by
    apply PowerSeries.order_eq_nat.mpr
    exact ⟨by simpa using hl, fun r hr => (Nat.not_lt_zero r hr).elim⟩
  have hlow : ((y.order.toNat+1-k : ℕ) : ℕ∞) ≤ (wronskian b).order := by
    have hx := PowerSeries.nat_le_order W.det (y.order.toNat+1-k)
      (PowerSeries.X_pow_dvd_iff.mp hd)
    rwa [he, PowerSeries.order_mul, hco, zero_add] at hx
  rw [← PowerSeries.coe_toNat_order hb] at hlow
  have hn : y.order.toNat+1-k ≤ (wronskian b).order.toNat := by exact_mod_cast hlow
  have hk := l.isLt
  omega

end NCHitting

end

end OAI
