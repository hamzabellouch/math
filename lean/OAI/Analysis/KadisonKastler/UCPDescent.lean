import OAI.Analysis.KadisonKastler.ConcreteUCP
import OAI.Analysis.KadisonKastler.CompleteConjugation

namespace OAI

/-! # Descending an amplified conjugacy through a UCP retraction

These are the operator-space estimates used when a character average or
an auxiliary tensor-factor average returns an amplified map to the base.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

section Abstract

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C]

/-- Composition of completely positive linear maps. -/
def completelyPositiveComp (E : B →CP C) (F : A →CP B) : A →CP C where
  toLinearMap := E.toLinearMap.comp F.toLinearMap
  map_cstarMatrix_nonneg' n X hX := by
    have h := E.map_cstarMatrix_nonneg (X.map F) (F.map_cstarMatrix_nonneg X hX)
    exact h

/-- Positivity at all matrix levels is reflected by a faithful embedding. -/
def completelyPositive_of_embedding (j : B →⋆ₐ[ℂ] C) (hj : Function.Injective j)
    (φ : A →CP C) (F : A →ₗ[ℂ] B) (hF : ∀ a, j (F a) = φ a) : A →CP B where
  toLinearMap := F
  map_cstarMatrix_nonneg' n X hX := by
    let jn := CStarMatrix.mapₙₐ (n := Fin n) j.toNonUnitalStarAlgHom
    have hpos : 0 ≤ jn (CStarMatrix.mapₗ F X) := by
      have he : jn (CStarMatrix.mapₗ F X) = CStarMatrix.mapₗ φ.toLinearMap X := by
        ext i k
        exact hF (X i k)
      rw [he]
      exact φ.map_cstarMatrix_nonneg X hX
    apply (NonUnitalStarAlgHom.map_le_map_iff jn (injective_starAlgHom_matrix j hj)).mp
    rw [map_zero]
    change 0 ≤ jn (CStarMatrix.mapₗ F X)
    exact hpos

/-- Complete contraction on the outside preserves a complete bound. -/
theorem completelyBoundedBy_comp_contraction (E : B →ₗ[ℂ] C) (F : A →ₗ[ℂ] B)
    (hE : CompletelyBoundedBy E 1) {c : ℝ} (hF : CompletelyBoundedBy F c) :
    CompletelyBoundedBy (E.comp F) c := by
  intro p q X
  have he : CStarMatrix.mapₗ (E.comp F) X =
      CStarMatrix.mapₗ E (CStarMatrix.mapₗ F X) := by ext i j; rfl
  rw [he]
  have h := hE p q (CStarMatrix.mapₗ F X)
  rw [one_mul] at h
  exact h.trans (hF p q X)

/-- Restriction along a complete isometry preserves the same complete bound. -/
theorem completelyBoundedBy_comp_completeIsometry (F : B →ₗ[ℂ] C)
    (j : A →ₗ[ℂ] B) {c : ℝ} (hF : CompletelyBoundedBy F c)
    (hj : CompletelyIsometric j) : CompletelyBoundedBy (F.comp j) c := by
  intro p q X
  have he : CStarMatrix.mapₗ (F.comp j) X =
      CStarMatrix.mapₗ F (CStarMatrix.mapₗ j X) := by ext i k; rfl
  rw [he]
  exact (hF p q _).trans_eq (by rw [hj])

/-- A UCP retraction of a faithful ambient embedding turns a nearby inner
conjugation into a map within twice the unitary displacement. -/
theorem retracted_conjugation_complete_bound
    (j : A →⋆ₐ[ℂ] B) (hj : Function.Injective j)
    (E : B →CP A) (hE : E 1 = 1) (hfix : ∀ a, E (j a) = a)
    (u : unitary B) :
    CompletelyBoundedBy
      (E.toLinearMap.comp ((unitaryConjugationLinear u).comp j.toAlgHom.toLinearMap) -
        LinearMap.id) (2 * ‖(u : B) - 1‖) := by
  have hconj := complete_unitaryConjugation_sub_id u
  have hjiso := injective_starAlgHom_completelyIsometric j hj
  have hEin := unital_completelyPositive_completelyBoundedBy E hE
  intro p q X
  let Y := CStarMatrix.mapₗ j.toAlgHom.toLinearMap X
  have he : CStarMatrix.mapₗ
      (E.toLinearMap.comp ((unitaryConjugationLinear u).comp j.toAlgHom.toLinearMap) -
        LinearMap.id) X = CStarMatrix.mapₗ E.toLinearMap
          (CStarMatrix.mapₗ (unitaryConjugationLinear u - LinearMap.id) Y) := by
    ext i k
    change E (unitaryConjugationLinear u (j (X i k))) - X i k =
      E (unitaryConjugationLinear u (j (X i k)) - j (X i k))
    rw [map_sub, hfix]
  rw [he]
  calc
    _ ≤ ‖CStarMatrix.mapₗ (unitaryConjugationLinear u - LinearMap.id) Y‖ := by
      simpa only [one_mul] using hEin p q
        (CStarMatrix.mapₗ (unitaryConjugationLinear u - LinearMap.id) Y)
    _ ≤ 2 * ‖(u : B) - 1‖ * ‖Y‖ := hconj p q Y
    _ = 2 * ‖(u : B) - 1‖ * ‖X‖ := by rw [hjiso p q X]

end Abstract

section Concrete

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M N : VonNeumannAlgebra H}

local instance descentOperatorOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance descentOperatorStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _
local instance descentFactorOrder (P : VonNeumannAlgebra H) : PartialOrder (Algebra P) :=
  CStarAlgebra.spectralOrder _
local instance descentFactorStarOrder (P : VonNeumannAlgebra H) : StarOrderedRing (Algebra P) :=
  CStarAlgebra.spectralOrderedRing _

/-- Descend an upstairs unitary through an actual UCP retraction. Range
membership and the original metric gap suffice for the final conjugacy. -/
theorem concrete_unitary_of_retracted_conjugation
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (j : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) (hj : Function.Injective j)
    (E : (K →L[ℂ] K) →CP (H →L[ℂ] H)) (hE : E 1 = 1)
    (hfix : ∀ x, E (j x) = x)
    (z : unitary (K →L[ℂ] K))
    (hmem : ∀ x : Algebra M,
      E ((z : K →L[ℂ] K) * j x * star (z : K →L[ℂ] K)) ∈ N)
    {g : ℝ} (hgap : kkDistance M N < g)
    (hsmall : 2 * ‖(z : K →L[ℂ] K) - 1‖ < 1 / 1000)
    (hge : g + 2 * ‖(z : K →L[ℂ] K) - 1‖ < 1) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ 256 * ‖(z : K →L[ℂ] K) - 1‖ := by
  let ρ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K) :=
    (Unitary.conjStarAlgAut ℂ (K →L[ℂ] K) z).toStarAlgHom.comp
      (j.comp (algebraInclusion M))
  let F : Algebra M →CP (H →L[ℂ] H) :=
    completelyPositiveComp E (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap ρ)
  let L : Algebra M →ₗ[ℂ] Algebra N :=
    F.toLinearMap.codRestrict N.toStarSubalgebra.toSubmodule (fun x => by
      change E (ρ x) ∈ N
      exact hmem x)
  let φ : Algebra M →CP Algebra N :=
    completelyPositive_of_embedding (algebraInclusion N) Subtype.val_injective F L
      (fun _ => rfl)
  have hφ : φ 1 = 1 := by
    apply Subtype.ext
    change E (ρ 1) = 1
    rw [map_one, hE]
  have hfull := retracted_conjugation_complete_bound j hj E hE hfix z
  have hrestricted := completelyBoundedBy_comp_completeIsometry _
    (algebraInclusion M).toAlgHom.toLinearMap hfull
    (injective_starAlgHom_completelyIsometric (algebraInclusion M) Subtype.val_injective)
  have hclose : CompletelyBoundedBy
      ((algebraInclusion N).toAlgHom.toLinearMap.comp φ.toLinearMap -
        (algebraInclusion M).toAlgHom.toLinearMap)
      (2 * ‖(z : K →L[ℂ] K) - 1‖) := by
    convert hrestricted using 1
    ext x
    rfl
  obtain ⟨u, hu, hnorm⟩ := concrete_ucp_unitary_of_published hCorrection hCommutant φ hφ
    (by positivity) hsmall hge hclose hgap
  refine ⟨u, hu, ?_⟩
  linarith

end Concrete

end

end KadisonKastler

end OAI
