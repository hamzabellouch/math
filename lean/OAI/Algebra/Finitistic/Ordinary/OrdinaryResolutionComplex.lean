import OAI.Algebra.Finitistic.Ordinary.OrdinaryTerminalResolution
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.OrdinarySimulation.ChainAlgebra
universe u
variable (k : Type u) [Field k] (l : ℕ)

/-- Extending the source idempotents by zero keeps all right ideals in the same C. -/
def extendedVertex (n : ℕ) : ChainAlgebra k l :=
  if h : n ≤ l then vertex k l ⟨n,by omega⟩ else 0

def extendedArrow (n : ℕ) : ChainAlgebra k l :=
  if h : n < l then arrow k l ⟨n,h⟩ else 0

theorem extendedVertex_idempotent (n : ℕ) :
    extendedVertex k l n * extendedVertex k l n = extendedVertex k l n := by
  unfold extendedVertex
  split
  · exact vertex_idempotent k l _
  · exact zero_mul _

theorem extendedArrow_target (n : ℕ) :
    extendedVertex k l (n+1) * extendedArrow k l n = extendedArrow k l n := by
  by_cases h : n < l
  · have h1 : n+1 ≤ l := by omega
    simp only [extendedVertex, extendedArrow, dite_eq_left h, dite_eq_left h1]
    exact vertex_target_arrow k l ⟨n,h⟩
  · rw [extendedArrow, dite_eq_right h, mul_zero]

theorem extendedArrow_square (n : ℕ) : extendedArrow k l (n+1) * extendedArrow k l n = 0 := by
  by_cases h1 : n+1 < l
  · have h0 : n < l := by omega
    simp only [extendedArrow, dite_eq_left h1, dite_eq_left h0, arrow_mul_arrow]
  · rw [extendedArrow, dite_eq_right h1, zero_mul]

abbrev resolutionIdeal (n : ℕ) := IdempotentTensor.rightIdeal (extendedVertex k l n)
abbrev resolutionTerm (n : ℕ) : ModuleCat.{u} (ChainAlgebra k l)ᵐᵒᵖ :=
  ModuleCat.of _ (resolutionIdeal k l n)

/-- Actual left-arrow differentials, with no transport of module types. -/
def resolutionDifferential (n : ℕ) : resolutionTerm k l n ⟶ resolutionTerm k l (n+1) :=
  ModuleCat.ofHom (((leftMultiply (extendedArrow k l n)).comp (resolutionIdeal k l n).subtype).codRestrict _
    (fun x => by
      change extendedVertex k l (n+1) * (extendedArrow k l n * x.val) = extendedArrow k l n * x.val
      rw [← mul_assoc, extendedArrow_target]))

theorem resolutionDifferential_square (n : ℕ) :
    resolutionDifferential k l n ≫ resolutionDifferential k l (n+1) = 0 := by
  ext x
  change extendedArrow k l (n+1) * (extendedArrow k l n * x.val) = 0
  rw [← mul_assoc, extendedArrow_square, zero_mul]

/-- The source's projective complex, extended by zero after degree l. -/
def terminalProjectiveComplex : CochainComplex (ModuleCat.{u} (ChainAlgebra k l)ᵐᵒᵖ) ℕ :=
  CochainComplex.of (resolutionTerm k l) (resolutionDifferential k l) (resolutionDifferential_square k l)

theorem resolutionTerm_projective (n : ℕ) : Projective (resolutionTerm k l n) := by
  let : Module.Projective (ChainAlgebra k l)ᵐᵒᵖ (ChainAlgebra k l) := Module.Projective.of_equiv rightRegularEquiv
  let r : ChainAlgebra k l →ₗ[(ChainAlgebra k l)ᵐᵒᵖ] resolutionIdeal k l n :=
    (leftMultiply (extendedVertex k l n)).codRestrict _ (fun x => by
      change extendedVertex k l n * (extendedVertex k l n * x) = extendedVertex k l n * x
      rw [← mul_assoc, extendedVertex_idempotent])
  have : Module.Projective (ChainAlgebra k l)ᵐᵒᵖ (resolutionIdeal k l n) :=
    Module.Projective.of_split (resolutionIdeal k l n).subtype r (by ext x; exact x.property)
  infer_instance

theorem resolutionTerm_vanishes (n : ℕ) (h : l < n) : IsZero (resolutionTerm k l n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hz (x : resolutionIdeal k l n) : x = 0 := by
    apply Subtype.ext
    have hp := x.property
    change extendedVertex k l n * x.val = x.val at hp
    rw [extendedVertex, dite_eq_right (Nat.not_le.mpr h), zero_mul] at hp
    exact hp.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩
end LittleFinitistic.OrdinarySimulation.ChainAlgebra

end

end OAI
