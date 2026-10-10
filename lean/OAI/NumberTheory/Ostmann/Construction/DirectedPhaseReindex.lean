import OAI.NumberTheory.Ostmann.Characters.PermutedAdditiveCancellation

namespace OAI

/-! # Exact reindexing of the directed phase and its cofactors -/

namespace Ostmann

open scoped BigOperators Classical

theorem directedPrimePhase_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) [∀ j, NeZero (p j)]
    (χ : ∀ j, DirichletCharacter ℂ (p j)) (t : ∀ j, ZMod (p j))
    (ν : J → ℂ) (b : J → J → ℤ) (v : ℤ) :
    directedPrimePhase (fun i => p (e i)) (fun i => χ (e i)) (fun i => t (e i))
        (fun i => ν (e i)) (fun i j => b (e i) (e j)) v =
      directedPrimePhase p χ t ν b v := by
  unfold directedPrimePhase
  rw [← e.prod_comp (fun j => ZMod.stdAddChar
    (t j * ((tupleCofactor p j : ZMod (p j))⁻¹ * (v : ZMod (p j)))) *
      ν j * ∏ k, χ j (p k : ZMod (p j)) ^ b j k)]
  apply Finset.prod_congr rfl
  intro i _
  rw [tupleCofactor_equiv e p (fun j => NeZero.ne (p j)) i]
  dsimp only
  rw [e.prod_comp (fun j => χ (e i) (p j : ZMod (p (e i))) ^ b (e i) j)]

end Ostmann

end OAI
