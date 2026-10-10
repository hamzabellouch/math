import OAI.Analysis.IrrationalRotation.Sampling.MixedRadix

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.MixedRadix

theorem denominator_radices {q : ℕ → ℕ} (hq0 : q 0 = 1)
    (hdiv : ∀ n, q n ∣ q (n + 1)) (N : ℕ) : denominator (radices q) N = q N := by
  induction N with
  | zero => simpa using hq0.symm
  | succ N ih =>
      rw [denominator_succ, ih, radices]
      exact Nat.mul_div_cancel' (hdiv N)

theorem radices_ge_two {q : ℕ → ℕ} (hq : ∀ n, 0 < q n)
    (hstrict : StrictMono q) (hdiv : ∀ n, q n ∣ q (n + 1)) (n : ℕ) :
    2 ≤ radices q n := by
  have heq : q n * radices q n = q (n + 1) := Nat.mul_div_cancel' (hdiv n)
  have hi := hstrict (Nat.lt_succ_self n)
  have hp := hq n
  by_contra hnot
  have hle : radices q n ≤ 1 := by omega
  nlinarith

theorem radices_pos {q : ℕ → ℕ} (hq : ∀ n, 0 < q n)
    (hstrict : StrictMono q) (hdiv : ∀ n, q n ∣ q (n + 1)) (n : ℕ) :
    0 < radices q n := lt_of_lt_of_le (by decide) (radices_ge_two hq hstrict hdiv n)

theorem coordinate_eq_tailValue {q : ℕ → ℕ} (hq0 : q 0 = 1)
    (hq : ∀ n, 0 < q n) (hstrict : StrictMono q) (hdiv : ∀ n, q n ∣ q (n + 1))
    (d : Digits (radices q)) (hnt : Nonterminal d) (i : ℕ) :
    Int.fract ((q i : ℝ) * ofDigits d) = tailValue d i := by
  rw [← denominator_radices hq0 hdiv i]
  exact fract_denominator_mul_ofDigits (radices_pos hq hstrict hdiv) d hnt i

theorem coordinates_ordered {q : ℕ → ℕ} (hq0 : q 0 = 1)
    (hq : ∀ n, 0 < q n) (hstrict : StrictMono q) (hdiv : ∀ n, q n ∣ q (n + 1))
    {d e : Digits (radices q)} (hd : Nonterminal d) (he : Nonterminal e)
    (hde : ∀ n, d n ≤ e n) (i : ℕ) :
    Int.fract ((q i : ℝ) * ofDigits d) ≤ Int.fract ((q i : ℝ) * ofDigits e) := by
  rw [coordinate_eq_tailValue hq0 hq hstrict hdiv d hd i,
    coordinate_eq_tailValue hq0 hq hstrict hdiv e he i]
  exact tailValue_mono (radices_pos hq hstrict hdiv) hde i

theorem abs_coordinate_sub_raw_le {q : ℕ → ℕ} (hq0 : q 0 = 1)
    (hq : ∀ n, 0 < q n) (hstrict : StrictMono q) (hdiv : ∀ n, q n ∣ q (n + 1))
    (d : Digits (radices q)) (hnt : Nonterminal d) (i : ℕ) {X : ℝ} (hX : 0 ≤ X)
    (hfloor : ⌊(radices q i : ℝ) * X⌋₊ = (d i : ℕ)) :
    |Int.fract ((q i : ℝ) * ofDigits d) - X| ≤ 1 / (radices q i : ℝ) := by
  rw [coordinate_eq_tailValue hq0 hq hstrict hdiv d hnt i]
  exact abs_tailValue_sub_raw_le_of_floor (radices_pos hq hstrict hdiv) d i hX hfloor

@[simp] theorem hybrid_apply_lt {r : ℕ → ℕ} (d e : Digits r) {N n : ℕ} (hn : n < N) :
    hybrid d e N n = e n := ite_eq_left hn

@[simp] theorem hybrid_apply_ge {r : ℕ → ℕ} (d e : Digits r) {N n : ℕ} (hn : N ≤ n) :
    hybrid d e N n = d n := ite_eq_right (not_lt.mpr hn)

theorem nonterminal_hybrid {r : ℕ → ℕ} (d e : Digits r) (hd : Nonterminal d) (N : ℕ) :
    Nonterminal (hybrid d e N) := by
  intro j
  obtain ⟨n, hn, hdigit⟩ := hd (max j N)
  have hjn : j ≤ n := (le_max_left j N).trans hn
  have hNn : N ≤ n := (le_max_right j N).trans hn
  exact ⟨n, hjn, by simpa [hybrid_apply_ge d e hNn] using hdigit⟩

theorem hybrid_ordered {r : ℕ → ℕ} {d e : Digits r} (hde : ∀ n, d n ≤ e n) (N n : ℕ) :
    d n ≤ hybrid d e N n ∧ hybrid d e N n ≤ e n := by
  by_cases hn : n < N
  · simpa [hybrid, hn] using hde n
  · simpa [hybrid, hn] using hde n

theorem tailValue_hybrid {r : ℕ → ℕ} (d e : Digits r) (N : ℕ) :
    tailValue (hybrid d e N) N = tailValue d N := by
  unfold tailValue
  congr 1
  apply tsum_congr
  intro n
  simp [term]

theorem denominator_mul_hybrid_sub {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d e : Digits r) (N : ℕ) :
    (denominator r N : ℝ) * (ofDigits (hybrid d e N) - ofDigits d) =
      ((prefixRank (hybrid d e N) N : ℤ) - (prefixRank d N : ℤ) : ℤ) := by
  rw [mul_sub, denominator_mul_ofDigits hr (hybrid d e N) N,
    denominator_mul_ofDigits hr d N, tailValue_hybrid]
  push_cast
  ring

theorem hybrid_sub_eq_int_div {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d e : Digits r) (N : ℕ) :
    ∃ z : ℤ, ofDigits (hybrid d e N) - ofDigits d = (z : ℝ) / (denominator r N : ℝ) := by
  refine ⟨(prefixRank (hybrid d e N) N : ℤ) - (prefixRank d N : ℤ), ?_⟩
  have hq : (denominator r N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast denominator_pos hr N)
  apply (eq_div_iff hq).mpr
  simpa only [mul_comm] using denominator_mul_hybrid_sub hr d e N

theorem tendsto_ofDigits_hybrid {r : ℕ → ℕ} (hr : ∀ n, 2 ≤ r n) (d e : Digits r) :
    Tendsto (fun N => ofDigits (hybrid d e N)) atTop (𝓝 (ofDigits e)) := by
  apply tendsto_ofDigits_of_agree_prefix hr e (hybrid d e)
  intro N n hn
  exact hybrid_apply_lt d e hn

end Invariant233.MixedRadix

end OAI
