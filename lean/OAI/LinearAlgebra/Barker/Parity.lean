import OAI.LinearAlgebra.Barker.Model
import Mathlib.Tactic.NormNum

namespace OAI

namespace CirculantHadamard.Barker

open scoped BigOperators

theorem aperiodic_parity {n : ℕ} (h : Fin n → ℤ)
    (hs : ∀ j, IsSign (h j)) (k : ℕ) :
    (2 : ℤ) ∣ aperiodic h k - ((n - k : ℕ) : ℤ) := by
  have hp (j : Fin (n - k)) :
      (2 : ℤ) ∣ h ⟨j.val, by omega⟩ * h ⟨j.val + k, by omega⟩ - 1 := by
    rcases hs ⟨j.val, by omega⟩ with hx | hx
    all_goals rcases hs ⟨j.val + k, by omega⟩ with hy | hy
    all_goals norm_num [hx, hy]
  have hsum : (2 : ℤ) ∣ ∑ j : Fin (n - k),
      (h ⟨j.val, by omega⟩ * h ⟨j.val + k, by omega⟩ - 1) :=
    Finset.dvd_sum (fun j _ => hp j)
  simpa [aperiodic, Finset.sum_sub_distrib] using hsum

theorem aperiodic_bounds {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h)
    (k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    -1 ≤ aperiodic h k ∧ aperiodic h k ≤ 1 :=
  abs_le.mp (hb.2 k hk0 hkn)

theorem aperiodic_even_shift_zero {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h)
    (hn : Even n) (k : ℕ) (hk : Even k) (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = 0 := by
  obtain ⟨u, hu⟩ := hn
  obtain ⟨v, hv⟩ := hk
  obtain ⟨d, hd⟩ := aperiodic_parity h hb.1 k
  have hbnd := aperiodic_bounds hb k hk0 hkn
  omega

theorem periodic_zero {n : ℕ} [NeZero n] (h : Fin n → ℤ)
    (hs : ∀ j, IsSign (h j)) : periodic h 0 = (n : ℤ) := by
  have hp (j : Fin n) : h j * h j = 1 := by
    rcases hs j with hj | hj <;> simp [hj]
  simp [periodic, hp]

end CirculantHadamard.Barker

end OAI
