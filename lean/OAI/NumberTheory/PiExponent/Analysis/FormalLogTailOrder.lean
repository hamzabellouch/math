import OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation
import OAI.NumberTheory.PiExponent.Jets.BranchContact

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchContact

open FormalLogTruncation

theorem logTail_order_ge (T : ℕ) : (T : ℕ∞) ≤ (logTail T).order :=
  PowerSeries.nat_le_order (logTail T) T (coeff_logTail_eq_zero T)

theorem composed_logTail_order_ge (T : ℕ) (t : PowerSeries ℂ)
    (ht : PowerSeries.constantCoeff t = 0) :
    (T : ℕ∞) * t.order ≤ PowerSeries.order (PowerSeries.subst t (logTail T)) := by
  calc
    (T : ℕ∞) * t.order = MvPowerSeries.order t * T := by
      rw [PowerSeries.order_eq_order, mul_comm]
    _ ≤ MvPowerSeries.order t * (logTail T).order :=
      mul_le_mul_right (logTail_order_ge T) _
    _ ≤ MvPowerSeries.order (PowerSeries.subst t (logTail T)) :=
      PowerSeries.le_order_subst t (PowerSeries.HasSubst.of_constantCoeff_zero' ht) _
    _ = PowerSeries.order (PowerSeries.subst t (logTail T)) := PowerSeries.order_eq_order.symm

theorem composed_logTail_strict_contact {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (a : Fin (m+1) → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (i : Fin m) (k : ℕ)
    (hk : PowerSeries.order (PowerSeries.subst (a 0) (logTail (T i))) = (k : ℕ∞)) :
    BranchContact.contact v a hne * v i.succ < (k : ℚ) := by
  have hTi : 0 < T i := by
    by_contra h
    have hz : T i = 0 := by omega
    have hh := hT i
    rw [hz, Nat.cast_zero, zero_mul] at hh
    exact (not_lt_of_ge (hv i.succ).le) hh
  have hb := composed_logTail_order_ge (T i) (a 0) (ha 0)
  rw [hk] at hb
  have hfinite : (a 0).order ≠ ⊤ := by
    intro htop
    have hTi0 : (T i : ℕ∞) ≠ 0 := by exact_mod_cast hTi.ne'
    simp only [htop, ENat.mul_top hTi0] at hb
    simp at hb
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  rw [← hn] at hb
  have hnat : T i * n ≤ k := by exact_mod_cast hb
  have hcontact := BranchContact.contact_bound v hv a hne 0 n hn.symm
  have hμ := BranchContact.contact_pos v hv a hne ha
  calc
    BranchContact.contact v a hne * v i.succ <
        BranchContact.contact v a hne * ((T i : ℚ) * v 0) :=
      mul_lt_mul_of_pos_left (hT i) hμ
    _ = (T i : ℚ) * (BranchContact.contact v a hne * v 0) := by ring
    _ ≤ (T i : ℚ) * (n : ℚ) := mul_le_mul_of_nonneg_left hcontact (by positivity)
    _ ≤ (k : ℚ) := by exact_mod_cast hnat

end PiExponent.FormalBranchContact

end

end OAI
