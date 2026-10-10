import OAI.NumberTheory.Ostmann.Arithmetic.MovingHarmonicProductFiber

namespace OAI

/-! # Original harmonic mass of a giant/product/frequency fibre -/

namespace Ostmann
open scoped Classical BigOperators

/-- On a fixed giant and frequency, the regular tuple determines the row.
Zero rows are discarded exactly; the other rows retain their original mass. -/
theorem indexed_harmonic_key_mass {A I : Type*} [Fintype A] [Fintype I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : I → Finset ℕ)
    (X : A → ℕ) (y : A → I → P) (v : A → ℤ) (μ : A → ℝ)
    (g : ℕ → ℝ) (hg : ∀ q, 0 ≤ g q)
    (hrow : ∀ a b, X a = X b → y a = y b → v a = v b → a = b)
    (hinj : ∀ a, μ a ≠ 0 → Function.Injective (y a))
    (hpoint : ∀ a, μ a ≠ 0 →
      μ a ≤ g (X a) * ∏ i, primeSubsetPrior P (Q i) (y a i))
    (k : ℕ × ℕ × ℤ) :
    (∑ a, if (X a, (∏ i, (y a i : ℕ)), v a) = k then μ a else 0) ≤
      g k.1 * ((Fintype.card I).factorial : ℝ) *
        (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (k.2.1 : ℝ)⁻¹ := by
  let S := Finset.univ.filter (fun a =>
    (X a, (∏ i, (y a i : ℕ)), v a) = k ∧ μ a ≠ 0)
  let T := (Finset.univ : Finset (I → P)).filter
    (fun z : I → P => Function.Injective z)
  let U := T.filter (fun z : I → P => (∏ i, (z i : ℕ)) = k.2.1)
  have hs : (∑ a, if (X a, (∏ i, (y a i : ℕ)), v a) = k then μ a else 0) =
      ∑ a ∈ S, μ a := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hk : (X a, (∏ i, (y a i : ℕ)), v a) = k <;>
      by_cases hm : μ a = 0 <;> simp [hk, hm]
  have hkey a (ha : a ∈ S) :
      X a = k.1 ∧ (∏ i, (y a i : ℕ)) = k.2.1 ∧ v a = k.2.2 := by
    have h := (Finset.mem_filter.mp ha).2.1
    simpa only [Prod.ext_iff] using h
  have hm a (ha : a ∈ S) : μ a ≠ 0 := (Finset.mem_filter.mp ha).2.2
  have hmap : Set.InjOn y S := by
    intro a ha b hb hab
    exact hrow a b ((hkey a ha).1.trans (hkey b hb).1.symm) hab
      ((hkey a ha).2.2.trans (hkey b hb).2.2.symm)
  have hmem : Set.MapsTo y S U := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hinj a (hm a ha)⟩, (hkey a ha).2.1⟩
  calc
    _ = ∑ a ∈ S, μ a := hs
    _ ≤ ∑ z ∈ U, g k.1 * ∏ i, primeSubsetPrior P (Q i) (z i) := by
      apply Finset.sum_le_sum_of_injOn y hmap (by
        intro z hz
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
        exact hmem ha)
      · intro a ha
        simpa only [(hkey a ha).1] using hpoint a (hm a ha)
      · intro z _ _
        exact mul_nonneg (hg _) (Finset.prod_nonneg
          (fun i _ => primeSubsetPrior_nonneg P (Q i) (z i)))
    _ = g k.1 * ∑ z ∈ U, ∏ i, primeSubsetPrior P (Q i) (z i) := by
      rw [Finset.mul_sum]
    _ ≤ g k.1 * (((Fintype.card I).factorial : ℝ) *
        (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (k.2.1 : ℝ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (hg _)
      exact indexed_harmonic_distinct_product_mass P hP Q T
        (fun z hz => (Finset.mem_filter.mp hz).2) k.2.1
    _ = _ := by ring

end Ostmann

end OAI
