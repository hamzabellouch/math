import OAI.NumberTheory.Ostmann.Construction.DirectedPrimePhase

namespace OAI

/-! # Common-center additive phases cancel under the actual matching -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem tupleCofactor_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (i : I) :
    tupleCofactor (fun i => p (e i)) i = tupleCofactor p (e i) := by
  apply mul_left_cancel₀ (hp (e i))
  calc
    _ = ∏ j, p (e j) := tupleCofactor_mul _ i
    _ = ∏ j, p j := e.prod_comp p
    _ = _ := (tupleCofactor_mul p (e i)).symm

noncomputable def primeTupleAdditivePhase {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, p i ≠ 0) (t : ∀ p : ℕ, ZMod p) (v : ℤ) : ℂ := by
  let : ∀ i, NeZero (p i) := fun i => ⟨hp i⟩
  exact ∏ i, ZMod.stdAddChar (t (p i) * ((tupleCofactor p i : ZMod (p i))⁻¹ * (v : ZMod (p i))))

theorem primeTupleAdditivePhase_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (t : ∀ p : ℕ, ZMod p) (v : ℤ) :
    primeTupleAdditivePhase (fun i => p (e i)) (fun i => hp (e i)) t v =
      primeTupleAdditivePhase p hp t v := by
  let : ∀ j, NeZero (p j) := fun j => ⟨hp j⟩
  unfold primeTupleAdditivePhase
  simp_rw [tupleCofactor_equiv e p hp]
  exact e.prod_comp (fun j => (ZMod.stdAddChar
    (t (p j) * ((tupleCofactor p j : ZMod (p j))⁻¹ * (v : ZMod (p j)))) : ℂ))

theorem primeTupleAdditivePhase_norm {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, p i ≠ 0) (t : ∀ p : ℕ, ZMod p) (v : ℤ) :
    ‖primeTupleAdditivePhase p hp t v‖ = 1 := by
  unfold primeTupleAdditivePhase
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i _
  simp only [ZMod.stdAddChar_apply, Circle.norm_coe]

/-- This is the exact cancellation needed in both a bulk permutation and
an identified diagonal pair; the centers are functions of the actual prime. -/
theorem permuted_additive_phase_cancel {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (t : ∀ p : ℕ, ZMod p) (v : ℤ)
    (W₁ W₂ : ℂ) :
    (primeTupleAdditivePhase (fun i => p (e i)) (fun i => hp (e i)) t v * W₁) *
      conj (primeTupleAdditivePhase p hp t v * W₂) = W₁ * conj W₂ := by
  rw [primeTupleAdditivePhase_equiv, map_mul]
  have he : primeTupleAdditivePhase p hp t v * conj (primeTupleAdditivePhase p hp t v) = 1 := by
    rw [Complex.mul_conj', primeTupleAdditivePhase_norm]
    norm_num
  calc
    _ = (primeTupleAdditivePhase p hp t v * conj (primeTupleAdditivePhase p hp t v)) *
      (W₁ * conj W₂) := by ring
    _ = _ := by rw [he, one_mul]

end Ostmann

end OAI
