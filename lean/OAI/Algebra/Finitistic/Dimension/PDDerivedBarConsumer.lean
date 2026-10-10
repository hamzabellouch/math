import OAI.Algebra.Finitistic.Dimension.PDBarDetection
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.PDBar
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} k) :=
  HasDerivedCategory.standard (ModuleCat.{u} k)

/-- Actual derived object of a nonnegative chain complex, with degree n sent to -n. -/
abbrev derivedObject (C : ChainComplex (ModuleCat.{u} k) ℕ) :=
  DerivedCategory.Q.obj (C.extend ComplexShape.embeddingDownNat)

def derivedHomologyIso (C : ChainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat k) (-(n : ℤ))).obj (derivedObject C) ≅
      C.homology n :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat k) (-(n : ℤ))).app _ ≪≫
    C.extendHomologyIso ComplexShape.embeddingDownNat rfl

variable (M : PDMinimal.FiniteModule k A) (P : ProjectiveResolution M.cat)

/-- A supplied actual derived bar comparison and bounded residue cohomology
imply finite projective dimension. The comparison is an explicit input. -/
theorem finite_pd_of_derived_iso
    (Z : DerivedCategory (ModuleCat.{u} k))
    (e : derivedObject (tensorComplex M (PDTensor.Residue (A := A)) P) ≅ Z)
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat k) (-(n : ℤ))).obj Z)) :
    projectiveDimension M.cat < ⊤ := by
  apply PDTensor.finite_pd_of_resolution M P
  obtain ⟨b,hb⟩ := h
  refine ⟨b, fun n hn => ?_⟩
  exact (hb n hn).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat k) (-(n : ℤ))).mapIso e.symm ≪≫
      derivedHomologyIso _ n).symm

variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]

/-- Nonzero cohomology of a retract of the supplied actual derived bar object
provides the lower pd bound. Inclusion and projection retain the summand data. -/
theorem lower_bound_of_derived_retract
    (Z T : DerivedCategory (ModuleCat.{u} k))
    (e : derivedObject (tensorComplex M U P) ≅ Z)
    (i : T ⟶ Z) (p : Z ⟶ T) (hip : i ≫ p = 𝟙 T)
    (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat k) (-(n : ℤ))).obj T)) :
    r ≤ projectiveDimension M.cat := by
  apply PDTensor.lower_bound_of_resolution M U P r n hrn
  intro hz
  let F := DerivedCategory.homologyFunctor (ModuleCat k) (-(n : ℤ))
  have hz' : IsZero (F.obj Z) := hz.of_iso
    (F.mapIso e.symm ≪≫ derivedHomologyIso _ n)
  apply h
  apply (IsZero.iff_id_eq_zero _).mpr
  have he : F.map i ≫ F.map p = 𝟙 (F.obj T) := by rw [← F.map_comp, hip, F.map_id]
  rw [← he, hz'.eq_of_tgt (F.map i) 0, zero_comp]
end LittleFinitistic.PDBar

end

end OAI
