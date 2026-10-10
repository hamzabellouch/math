import Mathlib.LinearAlgebra.Pi

namespace OAI

noncomputable section
namespace ArExplicit
universe u v w z
variable {k : Type u} [Field k] {ι : Type v} {κ : Type w}
variable (M : κ → Type z) [∀ j, AddCommGroup (M j)] [∀ j, Module k (M j)]
variable (f : ι → κ)

def supportedRestriction : (∀ j, M j) →ₗ[k] (∀ i, M (f i)) where
  toFun x i := x (f i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem supportedRestriction_bijective (hf : Function.Injective f)
    (hz : ∀ j, (¬ ∃ i, f i = j) → ∀ x : M j, x = 0) :
    Function.Bijective (supportedRestriction (k := k) M f) := by
  constructor
  · intro x y hxy
    funext j
    by_cases hj : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := hj
      exact congrFun hxy i
    · exact (hz j hj (x j)).trans (hz j hj (y j)).symm
  · intro y
    classical
    let x : ∀ j, M j := fun j => if hj : ∃ i, f i = j then
      hj.choose_spec ▸ y hj.choose else 0
    refine ⟨x, ?_⟩
    funext i
    change x (f i) = y i
    have hi : ∃ a, f a = f i := ⟨i, rfl⟩
    simp only [x, dite_eq_left hi]
    have hs (a : ι) (ha : f a = f i) : ha ▸ y a = y i := by
      have hai : a = i := hf ha
      subst a
      rfl
    exact hs _ _

def supportedPiEquiv (hf : Function.Injective f)
    (hz : ∀ j, (¬ ∃ i, f i = j) → ∀ x : M j, x = 0) :
    (∀ j, M j) ≃ₗ[k] (∀ i, M (f i)) :=
  LinearEquiv.ofBijective (supportedRestriction M f)
    (supportedRestriction_bijective M f hf hz)

end ArExplicit

end

end OAI
