import Mathlib

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section ModulusDefinitions
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed finite-codimensional subspaces. -/
def Cofinite : Type :=
  {F : Submodule ℝ E // IsClosed (F : Set E) ∧ FiniteDimensional ℝ (E ⧸ F)}

noncomputable def cofiniteTop : Cofinite E :=
  ⟨⊤, by simp, inferInstance⟩

/-- The inner one-sided excess values and their infimum. -/
def aucValues (N : E → ℝ) (t : ℝ) (x : E) (F : Cofinite E) : Set ℝ :=
  {a | ∃ y : E, y ∈ F.val ∧ N y = 1 ∧ a = N (x + t • y) - 1}

noncomputable def aucInner (N : E → ℝ) (t : ℝ) (x : E) (F : Cofinite E) : ℝ :=
  sInf (aucValues E N t x F)

noncomputable def aucCenter (N : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  sSup (Set.range (aucInner E N t x))

/-- The one-sided asymptotic uniform convexity modulus, with the order
of infimum, supremum and infimum. -/
noncomputable def aucModulus (N : E → ℝ) (t : ℝ) : ℝ :=
  sInf {a | ∃ x : E, N x = 1 ∧ a = aucCenter E N t x}

/-- The inner averaged signed excess; it is not replaced by a maximum. -/
def averageValues (N : E → ℝ) (t : ℝ) (x : E) (F : Cofinite E) : Set ℝ :=
  {a | ∃ y : E, y ∈ F.val ∧ N y = 1 ∧
    a = (N (x+t•y) + N (x-t•y))/((2 : ℕ) : ℝ) - 1}

noncomputable def averageInner (N : E → ℝ) (t : ℝ) (x : E) (F : Cofinite E) : ℝ :=
  sInf (averageValues E N t x F)

noncomputable def averageCenter (N : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  sSup (Set.range (averageInner E N t x))

/-- The averaged asymptotic midpoint modulus. -/
noncomputable def averageModulus (N : E → ℝ) (t : ℝ) : ℝ :=
  sInf {a | ∃ x : E, N x = 1 ∧ a = averageCenter E N t x}

end ModulusDefinitions

/-- An equivalent norm is kept as its exact real seminorm, with explicit positive
comparison constants. The lower inequality makes it a norm. -/
structure EquivalentNorm (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α β : ℝ) where
  N : Seminorm ℝ E
  alpha_pos : 0 < α
  alpha_le_beta : α ≤ β
  lower : ∀ x : E, α*‖x‖ ≤ N x
  upper : ∀ x : E, N x ≤ β*‖x‖
/-- Canonical (not merely abstract) reflexivity. -/
def Reflexive (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E)
/-- AUC requires positivity at every strictly positive parameter. -/
def IsAUC {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : E → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → 0 < aucModulus E N t

end

end ForestSpace

end OAI
