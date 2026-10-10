import OAI.Algebra.Finitistic.Encoding.ThreeVertexAlgebra
import Mathlib.RingTheory.TensorProduct.Finite

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ}

/-- Coefficients of the finite quadratic relation list, including degrees zero and one. -/
structure Relations (k : Type u) (d t : ℕ) where
  constant : Fin t → k
  linear : Fin t → Fin d → k
  quadratic : Fin t → Fin d → Fin d → k

abbrev Arrows (k : Type u) (d : ℕ) := Fin (d + 1) → k
abbrev Paths (k : Type u) [Field k] (d : ℕ) := Arrows k d ⊗[k] Arrows k d

def basis (i : Fin (d + 1)) : Arrows k d := Pi.single i 1

def commutation (h : Fin d) : Paths k d :=
  basis h.succ ⊗ₜ[k] basis 0 - basis 0 ⊗ₜ[k] basis h.succ

def homogenized (P : Relations k d t) (j : Fin t) : Paths k d :=
  (∑ h, ∑ l, P.quadratic j h l • (basis h.succ ⊗ₜ[k] basis l.succ)) +
  (∑ h, P.linear j h • (basis 0 ⊗ₜ[k] basis h.succ)) +
  P.constant j • (basis 0 ⊗ₜ[k] basis 0)

/-- Exactly the span of a'_h s - s' a_h and all homogenized p_j. -/
def relationSpace (P : Relations k d t) : Submodule k (Paths k d) :=
  Submodule.span k (Set.range (commutation (k := k) (d := d)) ∪ Set.range (homogenized P))

/-- Compose arrows, then quotient only the length-two path space by the specified relations. -/
def composition (P : Relations k d t) :
    Arrows k d →ₗ[k] Arrows k d →ₗ[k] (Paths k d ⧸ relationSpace P) :=
  (TensorProduct.mk k (Arrows k d) (Arrows k d)).compr₂ (relationSpace P).mkQ

/-- The six path-endpoint components of the manuscript's directed encoding. -/
abbrev B (P : Relations k d t) := ThreeVertexAlgebra (composition P)

variable (P : Relations k d t)

theorem finiteDimensional : FiniteDimensional k (B P) := by
  have : FiniteDimensional k (Arrows k d) := inferInstance
  have : FiniteDimensional k (Paths k d) := inferInstance
  have : FiniteDimensional k (Paths k d ⧸ relationSpace P) := inferInstance
  exact inferInstanceAs (FiniteDimensional k
    (k × k × k × Arrows k d × Arrows k d × (Paths k d ⧸ relationSpace P)))

open CategoryTheory in
/-- Actual global dimensions of the constructed finite-dimensional encoding. -/
theorem globalDimension_le_two :
    (⨆ N : ModuleCat.{max u v} (B P), projectiveDimension N) ≤ (2 : ℕ) ∧
    (⨆ N : ModuleCat.{max u v} (B P)ᵐᵒᵖ, projectiveDimension N) ≤ (2 : ℕ) :=
  ThreeVertexAlgebra.globalDimension_le_two (composition P)

/-- Includes a length-two residue class as the 0-to-2 component. -/
def lengthTwo : (Paths k d ⧸ relationSpace P) →ₗ[k] B P where
  toFun z := (0, 0, 0, 0, 0, z)
  map_add' x y := by
    change ((0, 0, 0, 0, 0, x+y) : B P) = (0, 0, 0, 0, 0, x) + (0, 0, 0, 0, 0, y)
    rw [ThreeVertexAlgebra.add_eq (composition P)]
    simp
  map_smul' c x := by
    change ((0, 0, 0, 0, 0, c • x) : B P) = c • (0, 0, 0, 0, 0, x)
    rw [ThreeVertexAlgebra.smul_eq (composition P)]
    simp

def pathMap : Paths k d →ₗ[k] B P := (lengthTwo P).comp (relationSpace P).mkQ

/-- This records that no additional linear length-two relation was introduced. -/
theorem pathMap_eq_zero_iff (z : Paths k d) : pathMap P z = 0 ↔ z ∈ relationSpace P := by
  have hi : Function.Injective (lengthTwo P) := by
    intro x y h
    exact congrArg (fun a : B P => a.2.2.2.2.2) h
  rw [pathMap, LinearMap.comp_apply, (map_eq_zero_iff _ hi)]
  exact Submodule.Quotient.mk_eq_zero _

/-- Arrows s,a_1,...,a_d from vertex 0 to 1; index zero is s. -/
def arrow01 (i : Fin (d + 1)) : B P := (0, 0, 0, basis i, 0, 0)
/-- Arrows s',a'_1,...,a'_d from vertex 1 to 2; index zero is s'. -/
def arrow12 (i : Fin (d + 1)) : B P := (0, 0, 0, 0, basis i, 0)

lemma arrow_product (i j : Fin (d + 1)) :
    arrow12 P i * arrow01 P j = pathMap P (basis i ⊗ₜ[k] basis j) := by
  change ThreeVertexAlgebra.mul (composition P) (0,0,0,0,basis i,0)
    (0,0,0,basis j,0,0) = (0,0,0,0,0,(relationSpace P).mkQ (basis i ⊗ₜ[k] basis j))
  simp [ThreeVertexAlgebra.mul, composition]

/-- Equation a'_h s = s' a_h, with exactly the manuscript's composition order. -/
theorem commutation_holds (h : Fin d) :
    arrow12 P h.succ * arrow01 P 0 = arrow12 P 0 * arrow01 P h.succ := by
  rw [arrow_product, arrow_product, ← sub_eq_zero, ← map_sub]
  exact (pathMap_eq_zero_iff P _).mpr (Submodule.subset_span (Or.inl ⟨h, rfl⟩))

/-- Every homogenized defining equation holds in the constructed algebra. -/
theorem homogenized_holds (j : Fin t) :
    (∑ h, ∑ l, P.quadratic j h l • (arrow12 P h.succ * arrow01 P l.succ)) +
    (∑ h, P.linear j h • (arrow12 P 0 * arrow01 P h.succ)) +
    P.constant j • (arrow12 P 0 * arrow01 P 0) = 0 := by
  have hz := (pathMap_eq_zero_iff P (homogenized P j)).mpr
    (Submodule.subset_span (Or.inr ⟨j, rfl⟩))
  simpa only [homogenized, map_add, map_sum, map_smul, ← arrow_product] using hz
end LittleFinitistic.QuadraticEncoding

end

end OAI
