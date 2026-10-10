import OAI.Analysis.LipschitzHilbert.Estimates.DyadicLongScales

namespace OAI

/-! The bounded overlap of the dyadic annulus part of the error source. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem dyadic_band_card (N K : ℕ) (a v : ℝ) (ha : 0 < a) :
    (Finset.univ.filter (fun j : Fin N => a * (2 : ℝ)^j.val ≤ v ∧
      v ≤ (2 : ℝ)^K * (a * (2 : ℝ)^j.val))).card ≤ K+1 := by
  let s := Finset.univ.filter (fun j : Fin N => a * (2 : ℝ)^j.val ≤ v ∧
    v ≤ (2 : ℝ)^K * (a * (2 : ℝ)^j.val))
  change s.card ≤ K+1
  by_cases hs : s.Nonempty
  · let m := s.min' hs
    have hm : m ∈ s := s.min'_mem hs
    have hmin (j : Fin N) (hj : j ∈ s) : m.val ≤ j.val := s.min'_le j hj
    have hmax (j : Fin N) (hj : j ∈ s) : j.val ≤ m.val+K := by
      have hm' := (Finset.mem_filter.mp hm).2
      have hj' := (Finset.mem_filter.mp hj).2
      have hmul : a*(2 : ℝ)^j.val ≤ a*(2 : ℝ)^(m.val+K) := by
        calc
          _ ≤ v := hj'.1
          _ ≤ (2 : ℝ)^K * (a*(2 : ℝ)^m.val) := hm'.2
          _ = _ := by rw [pow_add]; ring
      have hp : (2 : ℝ)^j.val ≤ (2 : ℝ)^(m.val+K) :=
        (mul_le_mul_iff_right₀ ha).mp (by nlinarith [hmul])
      exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hp
    have hcard := Finset.card_le_card_of_injOn (s := s) (t := Finset.range (K+1))
      (fun j : Fin N => j.val-m.val)
      (fun j hj => Finset.mem_range.mpr (by
        change j.val-m.val < K+1
        have := hmin j hj
        have := hmax j hj
        omega))
      (by
        intro j hj k hk heq
        change j.val-m.val = k.val-m.val at heq
        apply Fin.ext
        have := hmin j hj
        have := hmin k hk
        omega)
    simpa only [Finset.card_range] using hcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty]
    omega

theorem increasing_dyadic_reverse (N : ℕ) (a : ℝ) (j : Fin N) :
    a * (2 : ℝ)^j.val = (a*(2 : ℝ)^(N-1)) / (2 : ℝ)^(j.rev.val) := by
  have he : N-1 = j.val+j.rev.val := by simp only [Fin.val_rev]; omega
  rw [he, pow_add]
  field_simp

theorem sum_large_increasing_dyadic_reciprocals (N : ℕ) (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    (∑ j : Fin N, if r < a*(2 : ℝ)^j.val then (a*(2 : ℝ)^j.val)⁻¹ else 0) ≤ 2/r := by
  have h := sum_long_dyadic_reciprocals N (a*(2 : ℝ)^(N-1)) r (by positivity) hr
  have hs := Equiv.sum_comp (Fin.revPerm (n := N)) (fun j : Fin N =>
    if r < (a*(2 : ℝ)^(N-1))/(2 : ℝ)^j.val then
      ((a*(2 : ℝ)^(N-1))/(2 : ℝ)^j.val)⁻¹ else 0)
  change (∑ j : Fin N, if r < (a*(2 : ℝ)^(N-1))/(2 : ℝ)^j.rev.val then
    ((a*(2 : ℝ)^(N-1))/(2 : ℝ)^j.rev.val)⁻¹ else 0) = _ at hs
  simp_rw [← increasing_dyadic_reverse N a] at hs
  rw [hs]
  exact h

end LipschitzHilbert

end

end OAI
