import OAI.Analysis.LipschitzHilbert.Fourier.BandAverageComparison
import OAI.Analysis.LipschitzHilbert.Estimates.VariationSubsequence

namespace OAI

/-! The exact even/odd decomposition of the dyadic partial sums. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem sum_range_parity {E : Type*} [AddCommGroup E] (u : ℕ → E) (n : ℕ) :
    (∑ j ∈ Finset.range n, u j) =
      (∑ j ∈ Finset.range ((n + 1) / 2), u (2 * j)) +
        ∑ j ∈ Finset.range (n / 2), u (2 * j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmod := Nat.mod_lt n (by omega : 0 < 2)
    by_cases hn : n % 2 = 0
    · have h1 : (n + 1) / 2 = n / 2 := by omega
      have h2 : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
      have h3 : 2 * (n / 2) = n := by omega
      simp only [h1, h2, Finset.sum_range_succ, h3] at ih ⊢
      rw [ih]
      abel
    · have h1 : (n + 1) / 2 = n / 2 + 1 := by omega
      have h2 : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
      have h3 : 2 * (n / 2) + 1 = n := by omega
      simp only [h1, h2, Finset.sum_range_succ, h3] at ih ⊢
      rw [ih]
      abel

def paddedPacket {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (j : ℕ) : SchwartzMap ℝ ℂ :=
  if h : j < N then f ⟨j,h⟩ else 0

def parityPacket {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (r : ℕ) (j : Fin N) : SchwartzMap ℝ ℂ :=
  paddedPacket f (2 * j.val + r)

theorem partialBandSum_eq_sum_range {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    {i : ℕ} (hi : i ≤ N) (x : ℝ) :
    partialBandSum f i x = ∑ j ∈ Finset.range i, paddedPacket f j x := by
  classical
  have hfin : partialBandSum f i x =
      ∑ j : Fin N, if j.val < i then paddedPacket f j.val x else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [paddedPacket, dite_eq_left j.isLt]
  rw [hfin]
  have heq := Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if j < i then paddedPacket f j x else 0) N
  rw [heq]
  rw [← Finset.sum_filter]
  have hs : (Finset.range N).filter (fun j => j < i) = Finset.range i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hs]

theorem partialBandSum_parity {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    {i : ℕ} (hi : i ≤ N) (x : ℝ) :
    partialBandSum f i x =
      partialBandSum (parityPacket f 0) ((i + 1) / 2) x +
        partialBandSum (parityPacket f 1) (i / 2) x := by
  rw [partialBandSum_eq_sum_range f hi, sum_range_parity]
  rw [partialBandSum_eq_sum_range _ (by omega : (i + 1) / 2 ≤ N),
    partialBandSum_eq_sum_range _ (by omega : i / 2 ≤ N)]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hjN : j < N := by have := Finset.mem_range.mp hj; omega
    simp only [paddedPacket, dite_eq_left hjN, parityPacket, Nat.add_zero]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjN : j < N := by have := Finset.mem_range.mp hj; omega
    simp only [paddedPacket, dite_eq_left hjN, parityPacket]

end LipschitzHilbert

end

end OAI
