import OAI.NumberTheory.Ostmann.Construction.GroupedPhaseFactorization

namespace OAI

/-! # The actual harmonic-prior pivot row -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def primeTupleResidueRow (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (χ : Fin n → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : Fin n → P → ℂ) (t : ∀ p : ℕ, ZMod p) (Y : ℕ) (ε : Fin n → ℤ)
    (x : Fin n → P) (u : Fin (∏ i, (x i : ℕ))) : ℂ := by
  letI : ∀ i, Fact (x i : ℕ).Prime := fun i => ⟨hP (x i) (x i).property⟩
  exact groupedResidueRow (fun i => (x i : ℕ)) (fun i => χ i (x i))
    (fun i => κ i (x i)) (fun i => t (x i)) Y ε u

theorem primeTupleResidueRow_norm_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (χ : Fin n → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : Fin n → P → ℂ) (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (t : ∀ p : ℕ, ZMod p)
    (Y : ℕ) (ε : Fin n → ℤ) (x : Fin n → P) (u : Fin (∏ i, (x i : ℕ))) :
    ‖primeTupleResidueRow P hP χ κ t Y ε x u‖ ≤ 1 := by
  let : ∀ i, Fact (x i : ℕ).Prime := fun i => ⟨hP (x i) (x i).property⟩
  exact groupedResidueRow_norm_le_one (fun i => (x i : ℕ)) (fun i => χ i (x i))
    (fun i => κ i (x i)) (fun i => hκ i (x i)) (fun i => t (x i)) Y ε u

end Ostmann

end OAI
