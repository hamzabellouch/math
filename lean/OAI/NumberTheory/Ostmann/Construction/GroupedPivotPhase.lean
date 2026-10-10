import OAI.NumberTheory.Ostmann.Construction.DirectedPrimePhase
import OAI.NumberTheory.Ostmann.Construction.TransferCompletePhase

namespace OAI

/-! # Removing every constituent of a grouped pivot from the directed phase -/

namespace Ostmann

open scoped BigOperators Classical

/-- A regular outgoing row includes the cofactor, with its diagonal omitted. -/
theorem regular_prime_row_product {I : Type*} [Fintype I] (p : I → ℕ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : I → I → ℤ) (i : I) (ε : ℤ)
    (hself : b i i = 0) (hrow : ∀ j, j ≠ i → b i j = ε) :
    (∏ j, χ (p j : ZMod q) ^ b i j) = χ (tupleCofactor p i : ZMod q) ^ ε := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => χ (p j : ZMod q) ^ b i j)
    (Finset.mem_univ i), hself, zpow_zero, one_mul]
  simp only [tupleCofactor, Nat.cast_prod, map_prod]
  rw [← Finset.prod_zpow]
  exact Finset.prod_congr rfl (fun j hj => by rw [hrow j (Finset.mem_erase.mp hj).1])

/-- The incoming exponents are constant over all prime constituents of a pivot.
Thus their entire contribution uses only the product of those primes. -/
theorem grouped_incoming_row {K I : Type*} [Fintype K] [Fintype I]
    (P : K → ℕ) (Q : I → ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (g : (K ⊕ I) → (K ⊕ I) → ℤ)
    (b : Option I → Option I → ℤ) (i : I)
    (hpivot : ∀ k, g (.inr i) (.inl k) = b (some i) none)
    (hrest : ∀ j, g (.inr i) (.inr j) = b (some i) (some j)) :
    (∏ j, χ ((Sum.elim P Q j : ℕ) : ZMod q) ^ g (.inr i) j) =
      retainedGraphRow χ b i ((∏ k, P k : ℕ) : ZMod q)
        (fun j => (Q j : ZMod q)) := by
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, hpivot, hrest, retainedGraphRow]
  rw [Nat.cast_prod, character_product_power]

/-- The phase left after the outgoing pivot rows have been removed. -/
noncomputable def retainedGroupedPhase {I : Type*} [Fintype I] (Q : I → ℕ)
    [∀ i, NeZero (Q i)] (χ : ∀ i, DirichletCharacter ℂ (Q i))
    (t : ∀ i, ZMod (Q i)) (ν : I → ℂ)
    (b : Option I → Option I → ℤ) (M : ℕ) (v : ℤ) : ℂ :=
  ∏ i, ZMod.stdAddChar (t i * (((M * tupleCofactor Q i : ℕ) : ZMod (Q i))⁻¹ * (v : ZMod (Q i)))) * ν i *
      retainedGraphRow (χ i) b i (M : ZMod (Q i)) (fun j => (Q j : ZMod (Q i)))

/-- Literal partition of the full directed phase. No cancellation or estimate
is assumed: every incoming pivot edge remains in the retained phase. -/
theorem directedPrimePhase_remove_grouped_pivot {K I : Type*} [Fintype K] [Fintype I]
    (p : K ⊕ I → ℕ) [∀ j, NeZero (p j)]
    (χ : ∀ j, DirichletCharacter ℂ (p j))
    (t : ∀ j, ZMod (p j)) (ν : (K ⊕ I) → ℂ)
    (g : (K ⊕ I) → (K ⊕ I) → ℤ) (b : Option I → Option I → ℤ)
    (ε : K → ℤ) (v : ℤ)
    (hself : ∀ k, g (.inl k) (.inl k) = 0)
    (hrow : ∀ k j, j ≠ .inl k → g (.inl k) j = ε k)
    (hpivot : ∀ i k, g (.inr i) (.inl k) = b (some i) none)
    (hrest : ∀ i j, g (.inr i) (.inr j) = b (some i) (some j)) :
    directedPrimePhase p χ t ν g v =
      (∏ k, ZMod.stdAddChar (t (.inl k) *
        (((tupleCofactor (fun k => p (.inl k)) k * ∏ i, p (.inr i) : ℕ) :
          ZMod (p (.inl k)))⁻¹ * (v : ZMod (p (.inl k))))) *
        ν (.inl k) *
        χ (.inl k) ((tupleCofactor (fun k => p (.inl k)) k * ∏ i, p (.inr i) : ℕ) :
          ZMod (p (.inl k))) ^ ε k) *
      retainedGroupedPhase (fun i => p (.inr i)) (fun i => χ (.inr i))
        (fun i => t (.inr i)) (fun i => ν (.inr i)) b (∏ k, p (.inl k)) v := by
  have hp : p = Sum.elim (fun k => p (.inl k)) (fun i => p (.inr i)) := by
    funext j
    cases j <;> rfl
  have hcoP (k : K) : tupleCofactor p (.inl k) =
      tupleCofactor (fun k => p (.inl k)) k * ∏ i, p (.inr i) := by
    conv_lhs => rw [hp]
    exact tupleCofactor_sum_left _ _ k (NeZero.ne _)
  have hcoQ (i : I) : tupleCofactor p (.inr i) =
      (∏ k, p (.inl k)) * tupleCofactor (fun i => p (.inr i)) i := by
    conv_lhs => rw [hp]
    exact tupleCofactor_sum_right _ _ i (NeZero.ne _)
  rw [directedPrimePhase, Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro k _
    rw [regular_prime_row_product p (χ (.inl k)) g (.inl k) (ε k)
      (hself k) (hrow k), hcoP]
  · unfold retainedGroupedPhase
    apply Finset.prod_congr rfl
    intro i _
    rw [hcoQ]
    congr 1
    convert grouped_incoming_row (fun k => p (.inl k)) (fun j => p (.inr j))
      (χ (.inr i)) g b i (hpivot i) (hrest i) using 1
    apply Finset.prod_congr rfl
    intro j _
    cases j <;> rfl

end Ostmann

end OAI
