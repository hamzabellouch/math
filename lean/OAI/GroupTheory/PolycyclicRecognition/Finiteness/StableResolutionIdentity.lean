import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ProjectiveResolutionSyzygies

namespace OAI

/-! # The stable identity of a resolution syzygy

Maps factoring through projective representations form the image of a chosen
projective cover. The identity is zero in that quotient precisely when the
representation is projective. Applied to a resolution syzygy this detects
finite integral cohomological dimension, without assuming any stable
vanishing theorem.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2300] Submodule.Quotient.module
variable {G : Type} [Group G]

def projectiveCoverMap (B : Rep.{0} ℤ G) : (projectiveResolution B).complex.X 0 ⟶ B :=
  (projectiveResolution B).π.f 0

instance projectiveCoverMap_epi (B : Rep.{0} ℤ G) : Epi (projectiveCoverMap B) := by
  exact epi_of_isColimit_cofork (projectiveResolution B).isColimitCokernelCofork

def projectiveCoverPostcomp (A B : Rep.{0} ℤ G) :
    (A ⟶ (projectiveResolution B).complex.X 0) →ₗ[ℤ] (A ⟶ B) where
  toFun f := f ≫ projectiveCoverMap B
  map_add' f g := by simp only [Preadditive.add_comp]
  map_smul' r f := by simp only [RingHom.id_apply, Linear.smul_comp]

def projectiveFactorSubmodule (A B : Rep.{0} ℤ G) : Submodule ℤ (A ⟶ B) :=
  LinearMap.range (projectiveCoverPostcomp A B)

abbrev StableRepresentationHom (A B : Rep.{0} ℤ G) :=
  (A ⟶ B) ⧸ projectiveFactorSubmodule A B

def stableRepresentationClass (A B : Rep.{0} ℤ G) :
    (A ⟶ B) →ₗ[ℤ] StableRepresentationHom A B :=
  (projectiveFactorSubmodule A B).mkQ

theorem stableRepresentationClass_eq_zero_iff_projective_factor
    {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    stableRepresentationClass A B f = 0 ↔
      ∃ (P : Rep.{0} ℤ G), Projective P ∧
        ∃ (u : A ⟶ P) (v : P ⟶ B), u ≫ v = f := by
  change (projectiveFactorSubmodule A B).mkQ f = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨(projectiveResolution B).complex.X 0, inferInstance,
      u, projectiveCoverMap B, hu⟩
  · rintro ⟨P, hP, u, v, huv⟩
    let := hP
    refine ⟨u ≫ Projective.factorThru v (projectiveCoverMap B), ?_⟩
    change (u ≫ _) ≫ projectiveCoverMap B = f
    rw [Category.assoc, Projective.factorThru_comp, huv]

theorem stableRepresentationIdentity_eq_zero_iff (A : Rep.{0} ℤ G) :
    stableRepresentationClass A A (𝟙 A) = 0 ↔ Projective A := by
  rw [stableRepresentationClass_eq_zero_iff_projective_factor]
  constructor
  · rintro ⟨P, hP, u, v, huv⟩
    let := hP
    exact (show Retract A P from ⟨u, v, huv⟩).projective
  · intro hA
    exact ⟨A, hA, 𝟙 A, 𝟙 A, Category.id_comp _⟩

theorem stableRepresentationClass_eq_iff_projective_factor
    {A B : Rep.{0} ℤ G} (f g : A ⟶ B) :
    stableRepresentationClass A B f = stableRepresentationClass A B g ↔
      ∃ (P : Rep.{0} ℤ G), Projective P ∧
        ∃ (u : A ⟶ P) (v : P ⟶ B), u ≫ v = f - g := by
  rw [← sub_eq_zero, ← map_sub, stableRepresentationClass_eq_zero_iff_projective_factor]

theorem resolution_dimension_of_opcycles_dimension
    (P : ProjectiveResolution (trivialIntegral G)) (n d : ℕ)
    (h : HasProjectiveDimensionLE (P.complex.opcycles n) d) :
    HasProjectiveDimensionLE (trivialIntegral G) (n + d) := by
  induction n generalizing d with
  | zero =>
    let := h
    simpa only [Nat.zero_add] using
      hasProjectiveDimensionLT_of_iso (resolutionOpcyclesZeroIso P) (d + 1)
  | succ n ih =>
    have hprev : HasProjectiveDimensionLE (P.complex.opcycles n) (d + 1) :=
      (resolutionOpcyclesSequence_shortExact P n).hasProjectiveDimensionLT_X₃ (d + 1) h
        (hasProjectiveDimensionLT_of_ge (P.complex.X n) 1 (d + 2) (by omega))
    have hi := ih (d + 1) hprev
    simpa only [Nat.succ_add, Nat.add_succ] using hi

theorem stableResolutionIdentity_eq_zero_iff_dimension
    (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ) :
    stableRepresentationClass (P.complex.opcycles n) (P.complex.opcycles n)
      (𝟙 (P.complex.opcycles n)) = 0 ↔ HasProjectiveDimensionLE (trivialIntegral G) n := by
  rw [stableRepresentationIdentity_eq_zero_iff]
  constructor
  · intro h
    let := h
    simpa using resolution_dimension_of_opcycles_dimension P n 0 inferInstance
  · intro h
    let := h
    exact resolutionOpcycles_projective P n

end PolycyclicRecognition

end

end OAI
