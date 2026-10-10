import OAI.NumberTheory.Ostmann.Arithmetic.MovingRestoredMultiplier

namespace OAI

/-! # Reindexing the complete masked cofactor multiplier -/

namespace Ostmann
open scoped Classical BigOperators

theorem naturalRegularMultiplier_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, (p j).Prime) (active : J → Bool)
    (g : ∀ q : ℕ, ZMod q → ℂ) (D XL XR : ℕ) (s : ℤ) :
    let _ : ∀ j, Fact (p j).Prime := fun j => ⟨hp j⟩
    let _ : ∀ i, Fact (p (e i)).Prime := fun i => ⟨hp (e i)⟩
    naturalRegularMultiplier (fun i => p (e i)) (fun i => active (e i)) s
      (fun i => ((D * tupleCofactor (fun j => p (e j)) i : ℕ) : ZMod (p (e i))))
      (fun i => g (p (e i))) XL XR =
    naturalRegularMultiplier p active s
      (fun i => ((D * tupleCofactor p i : ℕ) : ZMod (p i)))
      (fun i => g (p i)) XL XR := by
  dsimp only
  let _ : ∀ j, Fact (p j).Prime := fun j => ⟨hp j⟩
  let _ : ∀ i, Fact (p (e i)).Prime := fun i => ⟨hp (e i)⟩
  rw [naturalRegularMultiplier_eq_transform_norm, naturalRegularMultiplier_eq_transform_norm]
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
    (movingRegularTransform_equiv e p (fun j z => if active j then g (p j) z else 1)
      (D * XL * XR) s)

end Ostmann

end OAI
