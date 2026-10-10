import OAI.NumberTheory.Ostmann.Characters.PivotProductPrior
import OAI.NumberTheory.Ostmann.Construction.PrimeProductMatching

namespace OAI

/-! # Harmonic product fibres on the actual regular-slot index type -/

namespace Ostmann
open scoped Classical BigOperators

theorem card_indexed_distinct_prime_product_fiber {I : Type*} [Fintype I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (M : ℕ) :
    ((Finset.univ : Finset (I → P)).filter
      (fun x : I → P => Function.Injective x ∧ (∏ i, (x i : ℕ)) = M)).card ≤
        (Fintype.card I).factorial := by
  let S := (Finset.univ : Finset (I → P)).filter
    (fun x : I → P => Function.Injective x ∧ (∏ i, (x i : ℕ)) = M)
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hx' := (Finset.mem_filter.mp hx).2
    have hex (y : S) : ∃ e : Equiv.Perm I, ∀ i, (x i : ℕ) = (y.val (e i) : ℕ) := by
      have hy := (Finset.mem_filter.mp y.property).2
      obtain ⟨e, he, _⟩ := prime_product_matching_exists_unique
        (fun i => (x i : ℕ)) (fun i => (y.val i : ℕ))
        (fun i => hP _ (x i).property) (fun i => hP _ (y.val i).property)
        (fun i j h => hx'.1 (Subtype.ext h))
        (fun i j h => hy.1 (Subtype.ext h)) (hx'.2.trans hy.2.symm)
      exact ⟨e, he⟩
    let f : S → Equiv.Perm I := fun y => Classical.choose (hex y)
    have hf (y : S) (i : I) : (x i : ℕ) = (y.val (f y i) : ℕ) :=
      Classical.choose_spec (hex y) i
    have hinj : Function.Injective f := by
      intro y z he
      apply Subtype.ext
      funext j
      obtain ⟨i, rfl⟩ := (f y).surjective j
      apply Subtype.ext
      rw [← hf y i, he]
      exact hf z i
    have hc := Fintype.card_le_of_injective f hinj
    simpa only [S, Fintype.card_coe, Fintype.card_perm] using hc
  · change S.card ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty]
    exact Nat.zero_le _

theorem indexed_harmonic_product_point_bound {I : Type*} [Fintype I]
    (P : Finset ℕ) (Q : I → Finset ℕ) (x : I → P) :
    (∏ i, primeSubsetPrior P (Q i) (x i)) ≤
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (∏ i, (x i : ℝ))⁻¹ := by
  have hi (i : I) : primeSubsetPrior P (Q i) (x i) ≤
      (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ * (x i : ℝ)⁻¹ := by
    unfold primeSubsetPrior
    split_ifs
    · rw [div_eq_mul_inv, mul_comm]
    · positivity
  have h : (∏ i, primeSubsetPrior P (Q i) (x i)) ≤
      ∏ i, ((∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ * (x i : ℝ)⁻¹) :=
    Finset.prod_le_prod₀ (fun i _ => primeSubsetPrior_nonneg P (Q i) (x i))
    (fun i _ => hi i)
  simpa only [Finset.prod_mul_distrib, Finset.prod_inv_distrib] using h

/-- Reindexing the regular roles changes neither the original harmonic
normalizers nor the factorial cost of a distinct-prime product fibre. -/
theorem indexed_harmonic_distinct_product_mass {I : Type*} [Fintype I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : I → Finset ℕ)
    (S : Finset (I → P)) (hS : ∀ x ∈ S, Function.Injective x) (M : ℕ) :
    (∑ x ∈ S.filter (fun x : I → P => (∏ i, (x i : ℕ)) = M),
      (∏ i, primeSubsetPrior P (Q i) (x i))) ≤
      ((Fintype.card I).factorial : ℝ) *
        (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹ := by
  let T := S.filter (fun x : I → P => (∏ i, (x i : ℕ)) = M)
  have hc : T.card ≤ (Fintype.card I).factorial := by
    apply (Finset.card_le_card (show T ⊆ (Finset.univ : Finset (I → P)).filter
      (fun x : I → P => Function.Injective x ∧ (∏ i, (x i : ℕ)) = M) from ?_)).trans
      (card_indexed_distinct_prime_product_fiber P hP M)
    intro x hx
    obtain ⟨hxS, hxM⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hS x hxS, hxM⟩
  calc
    _ ≤ ∑ _x ∈ T, (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro x hx
      have he : (∏ i, (x i : ℝ)) = (M : ℝ) := by
        exact_mod_cast (Finset.mem_filter.mp hx).2
      simpa only [he] using indexed_harmonic_product_point_bound P Q x
    _ = (T.card : ℝ) * ((∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      have hc' : (T.card : ℝ) ≤ (Fintype.card I).factorial := by exact_mod_cast hc
      calc
        _ ≤ ((Fintype.card I).factorial : ℝ) *
            ((∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (M : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right hc' (by positivity)
        _ = _ := by ring

end Ostmann

end OAI
