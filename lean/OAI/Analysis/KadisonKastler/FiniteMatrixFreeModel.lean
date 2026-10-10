import OAI.Analysis.KadisonKastler.FiniteBaseFreeHaar
import OAI.Analysis.KadisonKastler.FiniteMatrixPolar
import OAI.Analysis.KadisonKastler.VaryingUnitaryLifts
import OAI.Analysis.KadisonKastler.FreeHaarMap

namespace OAI

/-! # A free Haar unitary with finite-matrix representatives

This is the first stage of the controlled-lift construction. The scalar
matrix base is embedded in the varying product, the published independence
identity produces the free unitary, and finite polar decomposition gives
actual unitary representatives at every coordinate.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]
variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]

/-- A uniformly contractive family of star homomorphisms defines a homomorphism
into the bounded varying product. -/
def varyingSequenceHom (φ : ∀ j, A →⋆ₐ[ℂ] B j) : A →⋆ₐ[ℂ] VaryingBoundedSequence B where
  toFun x := ⟨fun j => φ j x, memℓp_infty ⟨‖x‖, by
    rintro _ ⟨j, rfl⟩
    exact NonUnitalStarAlgHom.norm_apply_le (φ j) x⟩⟩
  map_one' := by apply lp.ext; funext j; exact map_one (φ j)
  map_mul' x y := by apply lp.ext; funext j; exact map_mul (φ j) x y
  map_zero' := by apply lp.ext; funext j; exact map_zero (φ j)
  map_add' x y := by apply lp.ext; funext j; exact map_add (φ j) x y
  commutes' z := by apply lp.ext; funext j; exact (φ j).commutes z
  map_star' x := by apply lp.ext; funext j; exact map_star (φ j) x

@[simp]
theorem varyingSequenceHom_apply (φ : ∀ j, A →⋆ₐ[ℂ] B j) (x : A) (j : ℕ) :
    varyingSequenceHom φ x j = φ j x := rfl

local instance freeMatrixScalarOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance freeMatrixScalarStarOrder : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _
instance freeMatrixModelCStar (n j : ℕ) : CStarAlgebra (FiniteMatrixModel n j) := inferInstance
instance freeMatrixSequenceCStar (n : ℕ) [NeZero n] :
    CStarAlgebra (VaryingBoundedSequence (FiniteMatrixModel n)) := varyingSequenceCStarAlgebra _
instance freeMatrixSequenceStarRing (n : ℕ) [NeZero n] :
    StarRing (VaryingBoundedSequence (FiniteMatrixModel n)) :=
  (freeMatrixSequenceCStar n).toStarRing
local instance freeMatrixModelOrder (n j : ℕ) : PartialOrder (FiniteMatrixModel n j) :=
  CStarAlgebra.spectralOrder _
local instance freeMatrixModelStarOrder (n j : ℕ) : StarOrderedRing (FiniteMatrixModel n j) :=
  CStarAlgebra.spectralOrderedRing _
local instance freeMatrixModelCFC (n j : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (FiniteMatrixModel n j) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
local instance freeMatrixModelSpectrum (n j : ℕ) : NonnegSpectrumClass ℝ (FiniteMatrixModel n j) :=
  CStarAlgebra.instNonnegSpectrumClass

variable {n : ℕ} [NeZero n] {ω : Ultrafilter ℕ}

/-- The same outer scalar matrix is inserted in every finite coordinate. -/
def finiteMatrixScalarSequence :
    CStarMatrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] VaryingBoundedSequence (FiniteMatrixModel n) :=
  varyingSequenceHom fun j =>
    coefficientMatrixMap (StarAlgHom.ofId ℂ (CStarMatrix (Fin (j + 1)) (Fin (j + 1)) ℂ))

def FiniteMatrixUltraproduct.scalarHom (Q : FiniteMatrixUltraproduct n ω) :
    CStarMatrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] Algebra Q.algebra :=
  Q.quotient.comp finiteMatrixScalarSequence

/-- The first model unitary is free from the scalar outer matrices and
has genuine finite-matrix unitary representatives. -/
theorem FiniteMatrixUltraproduct.exists_freeHaar_lift
    (Q : FiniteMatrixUltraproduct n ω)
    (hind : FiniteBaseIndependence (concreteFactorTrace Q.factor)) :
    ∃ v : unitary (VaryingBoundedSequence (FiniteMatrixModel n)),
      FreeHaarMoments (concreteFactorTrace Q.factor) Q.scalarHom.range
        (Unitary.map (StarMonoidHom.ofClass Q.quotient) v) := by
  let : FiniteDimensional ℂ (CStarMatrix (Fin n) (Fin n) ℂ) :=
    FiniteDimensional.of_surjective CStarMatrix.ofMatrixₗ.toLinearMap
      CStarMatrix.ofMatrixₗ.surjective
  let : FiniteDimensional ℂ Q.scalarHom.range :=
    FiniteDimensional.of_surjective Q.scalarHom.toAlgHom.rangeRestrict.toLinearMap
      Q.scalarHom.toAlgHom.rangeRestrict_surjective
  obtain ⟨w, hw⟩ := hind.exists_freeHaar _ Q.scalarHom.range
  obtain ⟨v, hv⟩ := exists_varying_unitary_lift
    (fun j x => finiteMatrixModel_unitary_polar n j x) Q.quotient Q.surjective w
  refine ⟨v, ?_⟩
  have he : Unitary.map (StarMonoidHom.ofClass Q.quotient) v = w := Subtype.ext hv
  rwa [he]

end

end KadisonKastler

end OAI
