import OAI.NumberTheory.Ostmann.QuadraticSieve
import OAI.NumberTheory.Ostmann.QuadraticSieveMainRemainderSupport

namespace OAI

namespace Ostmann.QuadraticSieve

theorem mainRemainder_sum_le_squarefree (K Δ : ℕ) (hΔ : 0 < Δ)
    (F : ℕ → ℝ) (hF : ∀ w, 0 ≤ F w) :
    (∑ w ∈ Finset.Ioc K (K * Δ ^ 2), (|mainRemainder K Δ w| : ℤ) * F w) ≤
      2 * (Δ.divisors.card : ℝ) *
        ∑ s ∈ Δ.divisors, ∑ r ∈ oddSquarefreeUpTo (K * Δ ^ 2), F (s ^ 2 * r) := by
  classical
  let R := (Finset.Ioc K (K * Δ ^ 2)).filter (fun w => mainRemainder K Δ w ≠ 0)
  let P := Δ.divisors.product (oddSquarefreeUpTo (K * Δ ^ 2))
  let g : ℕ × ℕ → ℕ := fun p => p.1 ^ 2 * p.2
  have hcover : R ⊆ P.image g := by
    intro w hw
    obtain ⟨hwI, hwγ⟩ := Finset.mem_filter.mp hw
    obtain ⟨r, s, hrs, hsΔ, hws⟩ := mainRemainder_factors hwγ
    have hs : s ∈ Δ.divisors := Nat.mem_divisors.mpr ⟨hsΔ, hΔ.ne'⟩
    have hsp := Nat.pos_of_mem_divisors hs
    have hrle : r ≤ w := by
      rw [hws]
      have hsq : 1 ≤ s ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hsp.ne')
      simpa only [one_mul] using Nat.mul_le_mul_right r hsq
    have hrmem : r ∈ oddSquarefreeUpTo (K * Δ ^ 2) := mem_oddSquarefreeUpTo.mpr
      ⟨Nat.pos_of_ne_zero hrs.ne_zero, hrle.trans (Finset.mem_Ioc.mp hwI).2,
        (mainRemainder_support hΔ.ne' hwγ).1.of_dvd_nat
          (by rw [hws]; exact dvd_mul_left _ _), hrs⟩
    exact Finset.mem_image.mpr ⟨(s, r), Finset.mem_product.mpr ⟨hs, hrmem⟩, hws.symm⟩
  have hsum : (∑ w ∈ R, F w) ≤ ∑ s ∈ Δ.divisors,
      ∑ r ∈ oddSquarefreeUpTo (K * Δ ^ 2), F (s ^ 2 * r) := by
    calc
      _ ≤ ∑ w ∈ P.image g, F w :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun w _ _ => hF w)
      _ ≤ ∑ p ∈ P, F (g p) := Finset.sum_image_le_of_nonneg (fun w _ => hF w)
      _ = _ := by simp only [P, g, Finset.product_eq_sprod, Finset.sum_product]
  calc
    _ = ∑ w ∈ R, (|mainRemainder K Δ w| : ℤ) * F w := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro w hw
      by_cases h : mainRemainder K Δ w = 0 <;> simp [h]
    _ ≤ ∑ w ∈ R, (2 * (Δ.divisors.card : ℝ)) * F w := by
      apply Finset.sum_le_sum
      intro w hw
      apply mul_le_mul_of_nonneg_right _ (hF w)
      exact_mod_cast abs_mainRemainder_le K Δ w
    _ = (2 * (Δ.divisors.card : ℝ)) * ∑ w ∈ R, F w := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

end Ostmann.QuadraticSieve

end OAI
