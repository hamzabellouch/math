import OAI.NumberTheory.TwoPoint.Fourier.MinorArcLogSaving

namespace OAI

/-! Summing the minor-arc estimate over the actual dyadic prime blocks. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem minor_arc_bilinear_log_saving :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ,
      ∀ (P J : Finset ℕ) (X H N : ℕ), 1 ≤ H → H ≤ X →
      1 ≤ Real.log (H : ℝ) → J ⊆ Icc 1 N →
      (∀ p ∈ P, Nat.log 2 p ∈ J) → (∀ p ∈ P, p.Prime ∧ p ≠ 2) →
      (∀ j ∈ J, R₀ ≤ 2 ^ j ∧ 2 ^ j ≤ X) →
      (∀ j ∈ J, (Real.log (H : ℝ)) ^ 5 ≤ (2 : ℝ) ^ j ∧
        (2 : ℝ) ^ j ≤ (H : ℝ) / (Real.log (H : ℝ)) ^ 5) →
      ∀ (a c : ℕ → ℂ), (∀ m, ‖a m‖ ≤ 1) → (∀ p ∈ P, ‖c p‖ ≤ 1) →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q →
      (Real.log (H : ℝ)) ^ 5 ≤ (q : ℝ) →
      (q : ℝ) ≤ (H : ℝ) / (Real.log (H : ℝ)) ^ 5 →
      ∀ α : ℝ, IsCoprime (q : ℤ) r →
      |α - (r : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      (∑ k ∈ range X, ‖minorArcBilinearWindow P (X + H + 1) H 1 a c α k‖) ≤
        C * (X : ℝ) * H * (1 + Real.log (N : ℝ)) / Real.log (H : ℝ) := by
  obtain ⟨D, hD, hbound⟩ := minor_arc_dyadic_log_saving
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hbound
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨D / Real.log 2, div_pos hD hlog2, R₀, ?_⟩
  intro P J X H N hH hHX hlogH hJN hPJ hP hR hgeom a c ha hc r q hq hWq hqH α hcop happ
  let M : ℕ → ℕ := fun j => (X + H) / 2 ^ j + 1
  have hcut : ∀ k ∈ range X, ∀ p ∈ P, (k + H) / (1 * p) < X + H + 1 := by
    intro k hk p _
    have hkX := mem_range.mp hk
    have hd := Nat.div_le_self (k + H) (1 * p)
    omega
  have hcuts : ∀ j ∈ J, ∀ k ∈ range X, ∀ p ∈ minorArcDyadicPrimes P j,
      (k + H) / (1 * p) < M j := by
    intro j hj k hk p hp
    simp only [one_mul]
    exact minor_arc_cofactor_cutoff X H (2 ^ j) p k (by positivity)
      (minor_arc_dyadic_primes_bounds P j p hp (hP p (mem_filter.mp hp).1).1.pos).1
      (mem_range.mp hk)
  let K : ℝ := D * (X : ℝ) * H / Real.log (H : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hblock : ∀ j ∈ J,
      (∑ k ∈ range X, ‖minorArcBilinearWindow (minorArcDyadicPrimes P j) (M j) H 1 a c α k‖) ≤
        K / Real.log ((2 : ℝ) ^ j) := by
    intro j hj
    have hprime : ∀ p ∈ minorArcDyadicPrimes P j,
        p.Prime ∧ p ≠ 2 ∧ 2 ^ j ≤ p ∧ p ≤ 2 * 2 ^ j := by
      intro p hp
      have hpP := (mem_filter.mp hp).1
      exact ⟨(hP p hpP).1, (hP p hpP).2,
        minor_arc_dyadic_primes_bounds P j p hp (hP p hpP).1.pos⟩
    have hh := hR₀ (2 ^ j) (hR j hj).1 (minorArcDyadicPrimes P j) X H
      hH hHX (hR j hj).2 hlogH hprime a c ha
      (fun p hp => hc p (mem_filter.mp hp).1)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using (hgeom j hj).1)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using (hgeom j hj).2)
      r q hq hWq hqH α hcop happ
    dsimp [M, K]
    convert hh using 1
    push_cast
    ring
  calc
    _ ≤ ∑ j ∈ J, ∑ k ∈ range X,
        ‖minorArcBilinearWindow (minorArcDyadicPrimes P j) (M j) H 1 a c α k‖ :=
      minor_arc_bilinear_dyadic_sum_le J P hPJ X (X + H + 1) H 1 M hcut hcuts a c α
    _ ≤ K * (1 + Real.log (N : ℝ)) / Real.log 2 :=
      minor_arc_weighted_dyadic_log_sum J N hJN K hK _ hblock
    _ = _ := by dsimp [K]; ring

end TwoPointCorrelations

end OAI
