import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteResolutionTruncation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalGroupDimension

namespace OAI

/-! # The finite rational group resolution needed for the homology bound -/
noncomputable section
namespace PolycyclicRecognition.RationalResolution
open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G] (P : ProjectiveResolution (Rep.trivial ℚ G ℚ))

def resolutionOpcyclesSequence (n : ℕ) : ShortComplex (Rep ℚ G) :=
  ShortComplex.mk (P.complex.fromOpcycles (n + 1) n) (P.complex.pOpcycles n) (by
    rw [← cancel_epi (P.complex.pOpcycles (n + 1)),
      P.complex.p_fromOpcycles_assoc, P.complex.d_pOpcycles, comp_zero])

theorem resolutionOpcyclesSequence_shortExact (n : ℕ) :
    (resolutionOpcyclesSequence P n).ShortExact := by
  have hsc : (P.complex.sc' (n + 2) (n + 1) n).Exact := P.exact_succ n
  let e := P.complex.opcyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)
  have : Mono (P.complex.sc' (n + 2) (n + 1) n).fromOpcycles := hsc.mono_fromOpcycles
  have he : P.complex.fromOpcycles (n + 1) n =
      e.hom ≫ (P.complex.sc' (n + 2) (n + 1) n).fromOpcycles := by
    exact (e.inv_comp_eq).mp
      (P.complex.opcyclesIsoSc'_inv_fromOpcycles (n + 2) (n + 1) n (by simp) (by simp))
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · let S := ShortComplex.mk (P.complex.d (n + 1) n) (P.complex.pOpcycles n)
      (P.complex.d_pOpcycles (n + 1) n)
    have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel _
      (P.complex.opcyclesIsCokernel (n + 1) n (by simp))
    let φ : S ⟶ resolutionOpcyclesSequence P n :=
      { τ₁ := P.complex.pOpcycles (n + 1)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [S, resolutionOpcyclesSequence]
        comm₂₃ := by simp [S, resolutionOpcyclesSequence] }
    have : Epi φ.τ₁ := by
      change Epi (P.complex.pOpcycles (n + 1))
      infer_instance
    have : IsIso φ.τ₂ := by
      change IsIso (𝟙 _)
      infer_instance
    have : Mono φ.τ₃ := by
      change Mono (𝟙 _)
      infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hS
  · change Mono (P.complex.fromOpcycles (n + 1) n)
    have hmono : Mono (e.hom ≫ (P.complex.sc' (n + 2) (n + 1) n).fromOpcycles) :=
      inferInstance
    exact he.symm ▸ hmono
  · change Epi (P.complex.pOpcycles n)
    infer_instance

def resolutionOpcyclesZeroIso : P.complex.opcycles 0 ≅ Rep.trivial ℚ G ℚ :=
  (P.complex.opcyclesIsCokernel 1 0 (by simp)).coconePointUniqueUpToIso
    P.isColimitCokernelCofork

theorem resolutionOpcycles_projectiveDimension (n d : ℕ)
    [hdim : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) (n + d)] :
    HasProjectiveDimensionLE (P.complex.opcycles n) d := by
  induction n generalizing d with
  | zero =>
    have : HasProjectiveDimensionLT (Rep.trivial ℚ G ℚ) (d + 1) := by
      simpa only [Nat.zero_add] using hdim
    exact hasProjectiveDimensionLT_of_iso (resolutionOpcyclesZeroIso P).symm (d + 1)
  | succ n ih =>
    have : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) (n + (d + 1)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hdim
    have hq := ih (d + 1)
    exact (resolutionOpcyclesSequence_shortExact P n).hasProjectiveDimensionLT_X₁ (d + 1)
      (hasProjectiveDimensionLT_of_ge (P.complex.X n) 1 (d + 1) (by omega)) hq

theorem resolutionOpcycles_projective (d : ℕ)
    [hdim : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d] : Projective (P.complex.opcycles d) := by
  have : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) (d + 0) := by simpa using hdim
  exact (projective_iff_hasProjectiveDimensionLE_zero _).mpr
    (resolutionOpcycles_projectiveDimension P d 0)

variable {G : Type} [Group G] (P : ProjectiveResolution (Rep.trivial ℚ G ℚ)) (d : ℕ)

def finiteTruncation : ChainComplex (Rep ℚ G) ℕ :=
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
    [HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d] (i : ℕ) :
    Projective ((finiteTruncation P d).X i) := by
  rcases lt_trichotomy i d with hi | hi | hi
  · exact Projective.of_iso (finiteTruncationIso P d i hi).symm inferInstance
  · subst i
    exact Projective.of_iso (finiteTruncationTopIso P d).symm
      (resolutionOpcycles_projective P d)
  · exact (finiteTruncation_isZero P d i hi).projective

instance finiteResolution_single_supported :
    ((ChainComplex.single₀ (Rep ℚ G)).obj (Rep.trivial ℚ G ℚ)).IsStrictlySupported
      (finiteResolutionEmbedding d) where
  isZero i hi := by
    apply HomologicalComplex.isZero_single_obj_X
    intro h
    subst i
    exact hi ⟨0, by omega⟩ rfl

def finiteTruncationAugmentation :
    finiteTruncation P d ⟶ (ChainComplex.single₀ (Rep ℚ G)).obj (Rep.trivial ℚ G ℚ) :=
  HomologicalComplex.truncGEMap P.π (finiteResolutionEmbedding d) ≫
    inv (((ChainComplex.single₀ (Rep ℚ G)).obj (Rep.trivial ℚ G ℚ)).πTruncGE
      (finiteResolutionEmbedding d))

instance finiteTruncationAugmentation_quasiIso :
    QuasiIso (finiteTruncationAugmentation P d) := by
  have : QuasiIso (HomologicalComplex.truncGEMap P.π (finiteResolutionEmbedding d)) :=
    (HomologicalComplex.quasiIso_truncGEMap_iff P.π (finiteResolutionEmbedding d)).mpr
      (fun _ _ _ => inferInstance)
  exact quasiIso_comp (HomologicalComplex.truncGEMap P.π (finiteResolutionEmbedding d))
    (inv (((ChainComplex.single₀ (Rep ℚ G)).obj (Rep.trivial ℚ G ℚ)).πTruncGE
      (finiteResolutionEmbedding d)))

def finiteProjectiveResolution [HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d] :
    ProjectiveResolution (Rep.trivial ℚ G ℚ) where
  complex := finiteTruncation P d
  projective := finiteTruncation_projective P d
  π := finiteTruncationAugmentation P d


theorem groupHomology_isZero_above_dimension (d : ℕ)
    [HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d]
    (A : Rep ℚ G) (i : ℕ) (hi : d < i) : IsZero (groupHomology A i) := by
  classical
  let P := finiteProjectiveResolution (Rep.standardResolution ℚ G) d
  have hP : IsZero (P.complex.X i) :=
    finiteTruncation_isZero (Rep.standardResolution ℚ G) d i hi
  have hX : IsZero ((P.complex.coinvariantsTensorObj A).X i) :=
    ((Rep.coinvariantsTensor ℚ G).obj A).map_isZero hP
  refine IsZero.of_iso ?_ (groupHomologyIso A i P)
  apply HomologicalComplex.ExactAt.isZero_homology
  apply ShortComplex.exact_of_isZero_X₂
  simpa only [HomologicalComplex.shortComplexFunctor_obj_X₂] using hX

end PolycyclicRecognition.RationalResolution

end

end OAI
