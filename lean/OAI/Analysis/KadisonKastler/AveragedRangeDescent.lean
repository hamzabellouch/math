import OAI.Analysis.KadisonKastler.UCPDescent

namespace OAI

/-! # Descent when only the averaged conjugates lie in the embedded range

The averaging map acts on the upper ambient operator algebra. Its range
on other inputs need not lie in the embedded lower algebra. The map below
uses the inverse of a faithful embedding only on the averaged conjugates
of the source algebra, which is exactly the range condition in §8.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

section Linear

variable {A B C : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]

/-- Restrict a linear map to the range of an injection and invert there. -/
def linearDescendRange (j : B →ₗ[ℂ] C) (hj : Function.Injective j)
    (F : A →ₗ[ℂ] C) (hF : ∀ a, F a ∈ j.range) : A →ₗ[ℂ] B :=
  (LinearEquiv.ofInjective j hj).symm.toLinearMap.comp (F.codRestrict j.range hF)

theorem linearDescendRange_spec (j : B →ₗ[ℂ] C) (hj : Function.Injective j)
    (F : A →ₗ[ℂ] C) (hF : ∀ a, F a ∈ j.range) (a : A) :
    j (linearDescendRange j hj F hF a) = F a := by
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective j hj).apply_symm_apply ⟨F a, hF a⟩)

end Linear

section Abstract

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

/-- An upper UCP average fixes the embedding and retains the usual
twice-displacement complete bound, without a global range assumption. -/
theorem averaged_conjugation_complete_bound
    (j : A →⋆ₐ[ℂ] B) (hj : Function.Injective j)
    (E : B →CP B) (hE : E 1 = 1) (hfix : ∀ a, E (j a) = j a)
    (z : unitary B) :
    CompletelyBoundedBy
      (E.toLinearMap.comp ((unitaryConjugationLinear z).comp j.toAlgHom.toLinearMap) -
        j.toAlgHom.toLinearMap) (2 * ‖(z : B) - 1‖) := by
  have hconj := complete_unitaryConjugation_sub_id z
  have hjiso := injective_starAlgHom_completelyIsometric j hj
  have hEin := unital_completelyPositive_completelyBoundedBy E hE
  intro p q X
  let Y := CStarMatrix.mapₗ j.toAlgHom.toLinearMap X
  have he : CStarMatrix.mapₗ
      (E.toLinearMap.comp ((unitaryConjugationLinear z).comp j.toAlgHom.toLinearMap) -
        j.toAlgHom.toLinearMap) X = CStarMatrix.mapₗ E.toLinearMap
          (CStarMatrix.mapₗ (unitaryConjugationLinear z - LinearMap.id) Y) := by
    ext i k
    change E (unitaryConjugationLinear z (j (X i k))) - j (X i k) =
      E (unitaryConjugationLinear z (j (X i k)) - j (X i k))
    rw [map_sub, hfix]
  rw [he]
  calc
    _ ≤ ‖CStarMatrix.mapₗ (unitaryConjugationLinear z - LinearMap.id) Y‖ := by
      simpa only [one_mul] using hEin p q
        (CStarMatrix.mapₗ (unitaryConjugationLinear z - LinearMap.id) Y)
    _ ≤ 2 * ‖(z : B) - 1‖ * ‖Y‖ := hconj p q Y
    _ = 2 * ‖(z : B) - 1‖ * ‖X‖ := by rw [hjiso p q X]

end Abstract

section Concrete

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M N : VonNeumannAlgebra H}

local instance averagedDescentOperatorOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance averagedDescentOperatorStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _
local instance averagedDescentFactorOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance averagedDescentFactorStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

variable (j : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) (hj : Function.Injective j)
  (E : (K →L[ℂ] K) →CP (K →L[ℂ] K)) (z : unitary (K →L[ℂ] K))

/-- The averaged upper map, still valued in all upper ambient operators. -/
def averagedUpperMap : Algebra M →CP (K →L[ℂ] K) :=
  completelyPositiveComp E (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    ((Unitary.conjStarAlgAut ℂ (K →L[ℂ] K) z).toStarAlgHom.comp
      (j.comp (algebraInclusion M))))

theorem averagedUpperMap_apply (x : Algebra M) :
    averagedUpperMap j E z x =
      E ((z : K →L[ℂ] K) * j x * star (z : K →L[ℂ] K)) := rfl

variable (hmem : ∀ x : Algebra M,
  E ((z : K →L[ℂ] K) * j x * star (z : K →L[ℂ] K)) ∈
    j '' (N : Set (H →L[ℂ] H)))

include hmem in
theorem averagedUpperMap_mem_range (x : Algebra M) :
    averagedUpperMap j E z x ∈ j.toAlgHom.toLinearMap.range := by
  obtain ⟨y, _hy, he⟩ := hmem x
  exact ⟨y, he⟩

/-- The lower linear map is defined only by inversion on the embedded range. -/
def averagedRangeLinear : Algebra M →ₗ[ℂ] (H →L[ℂ] H) :=
  linearDescendRange j.toAlgHom.toLinearMap hj
    (averagedUpperMap j E z).toLinearMap (averagedUpperMap_mem_range j E z hmem)

theorem averagedRangeLinear_spec (x : Algebra M) :
    j (averagedRangeLinear j hj E z hmem x) = averagedUpperMap j E z x := by
  exact linearDescendRange_spec j.toAlgHom.toLinearMap hj
    (averagedUpperMap j E z).toLinearMap (averagedUpperMap_mem_range j E z hmem) x

theorem averagedRangeLinear_mem (x : Algebra M) :
    averagedRangeLinear j hj E z hmem x ∈ N := by
  obtain ⟨y, hy, he⟩ := hmem x
  have h : averagedRangeLinear j hj E z hmem x = y :=
    hj ((averagedRangeLinear_spec j hj E z hmem x).trans he.symm)
  rwa [h]

/-- Complete positivity is reflected through the faithful ambient embedding. -/
def averagedRangeMap : Algebra M →CP (H →L[ℂ] H) :=
  completelyPositive_of_embedding j hj (averagedUpperMap j E z)
    (averagedRangeLinear j hj E z hmem) (averagedRangeLinear_spec j hj E z hmem)

theorem averagedRangeMap_one (hE : E 1 = 1) :
    averagedRangeMap j hj E z hmem 1 = 1 := by
  apply hj
  change j (averagedRangeLinear j hj E z hmem 1) = j 1
  rw [averagedRangeLinear_spec]
  have he : averagedUpperMap j E z (1 : Algebra M) = 1 := by
    change E (((Unitary.conjStarAlgAut ℂ (K →L[ℂ] K) z).toStarAlgHom.comp
      (j.comp (algebraInclusion M))) 1) = 1
    rw [map_one, hE]
  rw [he, map_one]

theorem averagedRangeMap_complete_bound (hE : E 1 = 1) (hfix : ∀ x, E (j x) = j x) :
    CompletelyBoundedBy
      ((averagedRangeMap j hj E z hmem).toLinearMap -
        (algebraInclusion M).toAlgHom.toLinearMap) (2 * ‖(z : K →L[ℂ] K) - 1‖) := by
  have hfull := averaged_conjugation_complete_bound j hj E hE hfix z
  have hu := completelyBoundedBy_comp_completeIsometry _
    (algebraInclusion M).toAlgHom.toLinearMap hfull
    (injective_starAlgHom_completelyIsometric (algebraInclusion M) Subtype.val_injective)
  have hiso := injective_starAlgHom_completelyIsometric j hj
  intro p q X
  rw [← hiso p q (CStarMatrix.mapₗ
    ((averagedRangeMap j hj E z hmem).toLinearMap -
      (algebraInclusion M).toAlgHom.toLinearMap) X)]
  have he : CStarMatrix.mapₗ j.toAlgHom.toLinearMap
      (CStarMatrix.mapₗ ((averagedRangeMap j hj E z hmem).toLinearMap -
        (algebraInclusion M).toAlgHom.toLinearMap) X) =
      CStarMatrix.mapₗ
        ((E.toLinearMap.comp ((unitaryConjugationLinear z).comp j.toAlgHom.toLinearMap) -
          j.toAlgHom.toLinearMap).comp (algebraInclusion M).toAlgHom.toLinearMap) X := by
    apply CStarMatrix.ext
    intro i k
    change j (averagedRangeLinear j hj E z hmem (X i k) - (X i k : H →L[ℂ] H)) = _
    rw [map_sub, averagedRangeLinear_spec]
    rfl
  rw [he]
  exact hu p q X

include hj hmem in
theorem concrete_unitary_of_averaged_range
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (hE : E 1 = 1) (hfix : ∀ x, E (j x) = j x)
    {g : ℝ} (hgap : kkDistance M N < g)
    (hsmall : 2 * ‖(z : K →L[ℂ] K) - 1‖ < 1 / 1000)
    (hge : g + 2 * ‖(z : K →L[ℂ] K) - 1‖ < 1) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ 256 * ‖(z : K →L[ℂ] K) - 1‖ := by
  let F := averagedRangeMap j hj E z hmem
  let L : Algebra M →ₗ[ℂ] Algebra N := F.toLinearMap.codRestrict
    N.toStarSubalgebra.toSubmodule (averagedRangeLinear_mem j hj E z hmem)
  let φ : Algebra M →CP Algebra N := completelyPositive_of_embedding
    (algebraInclusion N) Subtype.val_injective F L (fun _ => rfl)
  have hφ : φ 1 = 1 := by
    apply Subtype.ext
    exact averagedRangeMap_one j hj E z hmem hE
  have hclose : CompletelyBoundedBy
      ((algebraInclusion N).toAlgHom.toLinearMap.comp φ.toLinearMap -
        (algebraInclusion M).toAlgHom.toLinearMap)
      (2 * ‖(z : K →L[ℂ] K) - 1‖) :=
    averagedRangeMap_complete_bound j hj E z hmem hE hfix
  obtain ⟨u, hu, hnorm⟩ := concrete_ucp_unitary_of_published hCorrection hCommutant φ hφ
    (by positivity) hsmall hge hclose hgap
  exact ⟨u, hu, by linarith⟩

end Concrete

end

end KadisonKastler

end OAI
