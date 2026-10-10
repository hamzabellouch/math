import OAI.NumberTheory.Ostmann.Arithmetic.MatchedHistoryEnergy
import OAI.NumberTheory.Ostmann.Construction.ConstituentUniqueRootEnergy

namespace OAI

/-! # Matched history energy using only its nonzero support -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem permuted_root_energy_on_support {A R : Type*} [Fintype A] [Fintype R]
    (e : Equiv.Perm A) (μ : A → ℝ) (F : R → A → ℂ) (A₀ : ℝ)
    (hA₀ : 0 ≤ A₀) (hμ : ∀ a, 0 ≤ μ a) (hbound : ∀ s a, F s a ≠ 0 → μ a ≤ A₀) :
    ‖∑ s, ∑ a, ((μ a * μ (e a) : ℝ) : ℂ) * F s a * conj (F s (e a))‖ ≤
      A₀ * ∑ s, ∑ a, μ a * ‖F s a‖ ^ 2 := by
  have hs (s : R) := matched_diagonal_energy e μ μ (F s) (F s) (fun _ => 1) A₀
    hA₀ hμ hμ (fun _ => by simp) (fun a ha he => ⟨hbound s a ha, hbound s (e a) he⟩)
  simp only [mul_one] at hs
  calc
    _ ≤ ∑ s, ‖∑ a, ((μ a * μ (e a) : ℝ) : ℂ) * F s a * conj (F s (e a))‖ := norm_sum_le _ _
    _ ≤ ∑ s, A₀ / 2 * ((∑ a, μ a * ‖F s a‖ ^ 2) + ∑ a, μ a * ‖F s a‖ ^ 2) :=
      Finset.sum_le_sum fun s _ => hs s
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]; ring

/-- Root equality is retained in the diagonal. Uniqueness removes the entire
frequency-history multiplicity from its square-energy estimate. -/
theorem permuted_history_energy_on_support {A D R : Type*}
    [Fintype A] [Fintype D] [Fintype R]
    (e : Equiv.Perm A) (μ : A → ℝ) (root : D → R) (F : D → A → ℂ) (A₀ : ℝ)
    (hA₀ : 0 ≤ A₀) (hμ : ∀ a, 0 ≤ μ a) (hbound : ∀ a d, F d a ≠ 0 → μ a ≤ A₀)
    (hunique : ∀ a d d', F d a ≠ 0 → F d' a ≠ 0 → root d = root d' → d = d') :
    ‖∑ d, ∑ d', if root d = root d' then
      ∑ a, ((μ a * μ (e a) : ℝ) : ℂ) * (F d a * conj (F d' (e a))) else 0‖ ≤
      A₀ * ∑ d, ∑ a, μ a * ‖F d a‖ ^ 2 := by
  rw [← rootFibreSum_weighted_pair root root (fun a => μ a * μ (e a)) F
    (fun d a => F d (e a))]
  have h := permuted_root_energy_on_support e μ (fun s a => rootFibreSum root s (fun d => F d a))
    A₀ hA₀ hμ (by
      intro s a ha
      by_contra hn
      have hz (d : D) : F d a = 0 := by
        by_contra hd
        exact hn (hbound a d hd)
      exact ha (by simp [rootFibreSum, hz]))
  simp only [mul_assoc] at h
  apply h.trans_eq
  congr 1
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, rootFibreSum_energy_of_unique root _ (hunique _), Finset.mul_sum]
  exact Finset.sum_comm

end Ostmann

end OAI
