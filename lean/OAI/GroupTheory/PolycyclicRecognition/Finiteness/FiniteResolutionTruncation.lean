import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ProjectiveResolutionSyzygies
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteIntegralRepresentations
import Mathlib.Algebra.Homology.Embedding.TruncGEHomology

namespace OAI

/-! # A finite resolution from finite dimension and finite generation

Canonical truncation replaces the last term by its quotient syzygy. The
projectivity of that syzygy follows from finite projective dimension, while
finite generation passes to the quotient.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits

def finiteResolutionShape (d : ℕ) : ComplexShape (Fin (d + 1)) where
  Rel i j := j.val + 1 = i.val
  next_eq := by intros; apply Fin.ext; omega
  prev_eq := by intros; apply Fin.ext; omega

def finiteResolutionEmbedding (d : ℕ) :
    (finiteResolutionShape d).Embedding (ComplexShape.down ℕ) :=
  ComplexShape.Embedding.mk' _ _ Fin.val Fin.val_injective (fun _ _ => Iff.rfl)

instance (d : ℕ) : (finiteResolutionEmbedding d).IsTruncGE where
  rel' _ _ h := h
  mem_next {j k} h := by
    change k + 1 = j.val at h
    exact ⟨⟨k, by omega⟩, rfl⟩

theorem finiteResolutionEmbedding_boundary (d : ℕ) (i : Fin (d + 1)) :
    (finiteResolutionEmbedding d).BoundaryGE i ↔ i.val = d := by
  constructor
  · intro h
    by_contra hi
    have hi' : i.val + 1 < d + 1 := by omega
    exact h.2 ⟨i.val + 1, hi'⟩ rfl
  · intro hi
    apply (finiteResolutionEmbedding d).boundaryGE (i' := d + 1)
    · change i.val + 1 = d + 1
      omega
    · intro j hj
      change j.val = d + 1 at hj
      omega

variable {G : Type} [Group G] (P : ProjectiveResolution (trivialIntegral G)) (d : ℕ)

def finiteTruncation : ChainComplex (Rep ℤ G) ℕ :=
  P.complex.truncGE (finiteResolutionEmbedding d)

theorem finiteTruncation_isZero (i : ℕ) (hi : d < i) :
    IsZero ((finiteTruncation P d).X i) := by
  apply P.complex.truncGE (finiteResolutionEmbedding d) |>.isZero_X_of_isStrictlySupported
    (finiteResolutionEmbedding d) i
  intro j hj
  change j.val = i at hj
  omega

def finiteTruncationIso (i : ℕ) (hi : i < d) :
    (finiteTruncation P d).X i ≅ P.complex.X i :=
  P.complex.truncGEXIso (finiteResolutionEmbedding d) (i := ⟨i, by omega⟩) rfl
    (by rw [finiteResolutionEmbedding_boundary]; change i ≠ d; omega)

def finiteTruncationTopIso :
    (finiteTruncation P d).X d ≅ P.complex.opcycles d :=
  P.complex.truncGEXIsoOpcycles (finiteResolutionEmbedding d)
    (i := ⟨d, by omega⟩) rfl ((finiteResolutionEmbedding_boundary d _).mpr rfl)

theorem finiteTruncation_projective
    [HasProjectiveDimensionLE (trivialIntegral G) d] (i : ℕ) :
    Projective ((finiteTruncation P d).X i) := by
  rcases lt_trichotomy i d with hi | hi | hi
  · exact Projective.of_iso (finiteTruncationIso P d i hi).symm inferInstance
  · subst i
    exact Projective.of_iso (finiteTruncationTopIso P d).symm
      (resolutionOpcycles_projective P d)
  · exact (finiteTruncation_isZero P d i hi).projective

theorem finiteTruncation_finite
    (hfin : ∀ i, i ≤ d → IntegralRepresentationFinite G (P.complex.X i)) (i : ℕ) :
    IntegralRepresentationFinite G ((finiteTruncation P d).X i) := by
  rcases lt_trichotomy i d with hi | hi | hi
  · exact (hfin i (by omega)).of_iso (finiteTruncationIso P d i hi).symm
  · subst i
    exact (resolutionOpcycles_finite P d (hfin d le_rfl)).of_iso
      (finiteTruncationTopIso P d).symm
  · exact integralRepresentationFinite_of_isZero G _ (finiteTruncation_isZero P d i hi)

instance finiteResolution_single_supported :
    ((ChainComplex.single₀ (Rep ℤ G)).obj (trivialIntegral G)).IsStrictlySupported
      (finiteResolutionEmbedding d) where
  isZero i hi := by
    apply HomologicalComplex.isZero_single_obj_X
    intro h
    subst i
    exact hi ⟨0, by omega⟩ rfl

def finiteTruncationAugmentation :
    finiteTruncation P d ⟶ (ChainComplex.single₀ (Rep ℤ G)).obj (trivialIntegral G) :=
  HomologicalComplex.truncGEMap P.π (finiteResolutionEmbedding d) ≫
    inv (((ChainComplex.single₀ (Rep ℤ G)).obj (trivialIntegral G)).πTruncGE
      (finiteResolutionEmbedding d))

instance finiteTruncationAugmentation_quasiIso :
    QuasiIso (finiteTruncationAugmentation P d) := by
  have : QuasiIso (HomologicalComplex.truncGEMap P.π (finiteResolutionEmbedding d)) :=
    (HomologicalComplex.quasiIso_truncGEMap_iff P.π (finiteResolutionEmbedding d)).mpr
      (fun _ _ _ => inferInstance)
  exact quasiIso_comp (HomologicalComplex.truncGEMap P.π (finiteResolutionEmbedding d))
    (inv (((ChainComplex.single₀ (Rep ℤ G)).obj (trivialIntegral G)).πTruncGE
      (finiteResolutionEmbedding d)))

def finiteProjectiveResolution [HasProjectiveDimensionLE (trivialIntegral G) d] :
    ProjectiveResolution (trivialIntegral G) where
  complex := finiteTruncation P d
  projective := finiteTruncation_projective P d
  π := finiteTruncationAugmentation P d

theorem finiteProjectiveResolution_of_finiteDimension_typeFP
    (hdim : HasFiniteIntegralCohomologicalDimension G) (hfp : TypeFPInfinity G) :
    HasFiniteProjectiveResolution G := by
  obtain ⟨d, hd⟩ := hdim
  obtain ⟨P, hP⟩ := hfp d
  have := hd
  exact ⟨finiteProjectiveResolution P d, d, finiteTruncation_finite P d hP,
    finiteTruncation_isZero P d⟩

end PolycyclicRecognition

end

end OAI
