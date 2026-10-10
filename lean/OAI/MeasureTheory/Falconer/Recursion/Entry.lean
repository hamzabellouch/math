import OAI.MeasureTheory.Falconer.Estimates.Assembly
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases

namespace OAI

/-!
# Entry depth for the all-dimensional assembly

This is the numerical content of `asm:entry`. The dimension enters through
the Lipschitz constant of the two excess profiles. The envelope and
dimension constants are independent.
-/

namespace Falconer
open Set

/-- A common entry depth with a small graph cost and two positive tail
potentials. The large-scale hypothesis is explicit; the manuscript uses
this only for all sufficiently large `N`. -/
theorem exists_assembly_entry (A : Fin 2 → ℕ → ℝ) (N Q : ℕ)
    {d χ β ε : ℝ} (hd : 0 < d) (hχ : 0 < χ) (hβ : 0 < β)
    (hε : 0 ≤ ε) (hsmall : β + ε < χ / 4)
    (hN : 0 < N) (hlarge : 2 * d ≤ β * (N : ℝ))
    (hQ : 0 < Q) (hQsmall : 4 * Q ≤ N)
    (hzero : ∀ i, A i 0 = 0)
    (henvelope : ∀ i n, n ≤ N → χ * (n : ℝ) / N - ε ≤ A i n)
    (hlip : ∀ i m n, m ≤ N → n ≤ N →
      |A i n - A i m| ≤ d * |(n : ℝ) - m| / N) :
    ∃ c : ℕ, c < N ∧ β * N / (2 * d) ≤ (c : ℝ) ∧ (c : ℝ) < N / 4 ∧
      c + Q ≤ N ∧
      (∀ i n, c ≤ n → n ≤ N → β - d / N ≤ A i n) ∧
      min (PlanarFalconer.height (A 0) 0 c) (PlanarFalconer.height (A 1) 0 c) ≤ β + ε ∧
      (∀ i, 2 * β - 2 * d / N ≤ PlanarFalconer.potential (A i) c N Q) ∧
      -A 0 c - A 1 c +
        min (PlanarFalconer.height (A 0) 0 c) (PlanarFalconer.height (A 1) 0 c) +
        ((2 * A 0 c - PlanarFalconer.potential (A 0) c N Q) +
          (2 * A 1 c - PlanarFalconer.potential (A 1) c N Q)) / 2 ≤
          -β + ε + 2 * d / N := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let B : ℕ → ℝ := fun n => min (A 0 n) (A 1 n)
  obtain ⟨c, hcN, hc, hlast⟩ := PlanarFalconer.exists_last_crossing B N β (by
    simp only [B, hzero, min_self]
    exact hβ.le)
  have hBN : β < B N := by
    have h0 := henvelope 0 N le_rfl
    have h1 := henvelope 1 N le_rfl
    have hdiv : χ * (N : ℝ) / N = χ := by field_simp
    rw [hdiv] at h0 h1
    exact lt_min (by linarith) (by linarith)
  have hstep (n : ℕ) (hn : n < N) : B (n+1) ≤ B n + d / N := by
    have hi (i : Fin 2) : A i (n+1) ≤ A i n + d / N := by
      have hh := hlip i n (n+1) hn.le (by omega)
      have heq : |((n+1 : ℕ) : ℝ) - n| = 1 := by
        rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, abs_one]
      rw [heq, mul_one] at hh
      linarith [(abs_le.mp hh).2]
    exact PlanarFalconer.min_step (A 0) (A 1) (hi 0) (hi 1)
  obtain ⟨hcN', htail⟩ := PlanarFalconer.last_crossing_tail B hcN hc hBN
    (div_nonneg hd.le hNr.le) hlast hstep
  have hlowall (i : Fin 2) (n : ℕ) (hn : n ≤ N) : -ε ≤ A i n := by
    have hh := henvelope i n hn
    have hp : 0 ≤ χ * (n : ℝ) / N := by positivity
    linarith
  have htail' (i : Fin 2) (n : ℕ) (hcn : c ≤ n) (hn : n ≤ N) :
      β - d / N ≤ A i n := by
    have hh := htail n hcn hn
    fin_cases i
    · exact hh.trans (min_le_left _ _)
    · exact hh.trans (min_le_right _ _)
  have hnext := hlast (c+1) (by omega) (by omega)
  have hu := hlip 0 0 (c+1) (Nat.zero_le N) (by omega)
  rw [hzero, sub_zero, Nat.cast_zero, sub_zero, abs_of_nonneg (show 0 ≤ ((c+1 : ℕ) : ℝ) from Nat.cast_nonneg _)] at hu
  have hnext0 : β < A 0 (c+1) := hnext.trans_le (min_le_left _ _)
  have hbound : β * (N : ℝ) < d * ((c+1 : ℕ) : ℝ) :=
    (lt_div_iff₀ hNr).mp (hnext0.trans_le (le_abs_self _ |>.trans hu))
  have hdepthlo : β * N / (2 * d) ≤ (c : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * d)).mpr
    push_cast at hbound
    nlinarith
  have henvmin : χ * (c : ℝ) / N - ε ≤ B c :=
    le_min (henvelope 0 c hcN) (henvelope 1 c hcN)
  have hdepthhi : (c : ℝ) < (N : ℝ) / 4 := by
    have hdiv : χ * (c : ℝ) / N < χ / 4 := by linarith
    have hm := (div_lt_iff₀ hNr).mp hdiv
    nlinarith
  have hwidth : c + Q ≤ N := by
    have hQreal : (4 : ℝ) * Q ≤ N := by exact_mod_cast hQsmall
    have hcQ : (c : ℝ) + Q ≤ N := by linarith
    exact_mod_cast hcQ
  have hcost := PlanarFalconer.min_height_le (A 0) (A 1) c hc
    (fun n hn => hlowall 0 n (hn.trans hcN))
    (fun n hn => hlowall 1 n (hn.trans hcN))
  have hpot (i : Fin 2) : 2 * β - 2 * d / N ≤ PlanarFalconer.potential (A i) c N Q := by
    have hh := PlanarFalconer.potential_lower (A i) hQ hwidth (htail' i)
    convert hh using 1; ring
  refine ⟨c, hcN', hdepthlo, hdepthhi, hwidth, htail', hcost, hpot, ?_⟩
  have hg := PlanarFalconer.outer_profile_gain (A 0) (A 1) hQ hwidth hc
    (fun n hn => hlowall 0 n (hn.trans hcN))
    (fun n hn => hlowall 1 n (hn.trans hcN)) htail
  convert hg using 1; ring

end Falconer

end OAI
