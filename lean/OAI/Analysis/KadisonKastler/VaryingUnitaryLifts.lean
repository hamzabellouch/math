import OAI.Analysis.KadisonKastler.VaryingQuotient
import OAI.Analysis.KadisonKastler.UnitaryLifts

namespace OAI

/-! # Unitary lifts in a varying finite product

Coordinate unitary polar decompositions produce an exact unitary lift
through any surjective star quotient of the bounded product.
-/

namespace KadisonKastler

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]

local instance varyingProductNontrivial : Nontrivial (VaryingBoundedSequence B) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have he := congrArg (fun x : VaryingBoundedSequence B => x 0) h
  exact zero_ne_one he

local instance varyingLiftOrder (j : ℕ) : PartialOrder (B j) := CStarAlgebra.spectralOrder _
local instance varyingLiftStarOrder (j : ℕ) : StarOrderedRing (B j) := CStarAlgebra.spectralOrderedRing _
local instance varyingProductLiftOrder : PartialOrder (VaryingBoundedSequence B) :=
  CStarAlgebra.spectralOrder _
local instance varyingProductLiftPreorder : Preorder (VaryingBoundedSequence B) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance varyingProductLiftLE : LE (VaryingBoundedSequence B) :=
  (CStarAlgebra.spectralOrder _).toLE
local instance varyingProductLiftStarOrder : StarOrderedRing (VaryingBoundedSequence B) :=
  CStarAlgebra.spectralOrderedRing _
local instance varyingProductLiftCFC :
    NonUnitalContinuousFunctionalCalculus ℝ (VaryingBoundedSequence B) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
local instance varyingProductLiftSpectrum : NonnegSpectrumClass ℝ (VaryingBoundedSequence B) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- A family of coordinate unitaries is bounded in the actual product. -/
def varyingUnitarySequence (v : ∀ j, unitary (B j)) :
    unitary (VaryingBoundedSequence B) := by
  let x : VaryingBoundedSequence B := ⟨fun j => (v j : B j),
    memℓp_infty ⟨1, by
      rintro _ ⟨j, rfl⟩
      exact (CStarRing.norm_coe_unitary (v j)).le⟩⟩
  refine ⟨x, ?_, ?_⟩ <;> apply lp.ext <;> funext j
  · exact (v j).property.1
  · exact (v j).property.2

@[simp]
theorem varyingUnitarySequence_apply (v : ∀ j, unitary (B j)) (j : ℕ) :
    (varyingUnitarySequence v : VaryingBoundedSequence B) j = (v j : B j) := rfl

variable {C : Type*} [CStarAlgebra C]

/-- Coordinate polar decompositions suffice for unitary quotient lifting;
no trace approximation or additional lifting axiom is needed. -/
theorem exists_varying_unitary_lift
    (hpolar : ∀ j (x : B j), ∃ v : unitary (B j), (v : B j) * CFC.abs x = x)
    (π : VaryingBoundedSequence B →⋆ₐ[ℂ] C) (hπ : Function.Surjective π)
    (u : unitary C) :
    ∃ v : unitary (VaryingBoundedSequence B), π (v : VaryingBoundedSequence B) = (u : C) := by
  let : PartialOrder C := CStarAlgebra.spectralOrder _
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing _
  obtain ⟨x, hx⟩ := hπ (u : C)
  choose w hw using (fun j => hpolar j (x j))
  let v := varyingUnitarySequence w
  have hmul : (v : VaryingBoundedSequence B) * CFC.abs x = x := by
    apply lp.ext
    funext j
    change (w j : B j) * (CFC.abs x) j = x j
    have he : (varyingSequenceEval B j) (CFC.abs x) = CFC.abs (x j) :=
      starAlgHom_map_abs (varyingSequenceEval B j) x
    exact (congrArg (fun z : B j => (w j : B j) * z) he).trans (hw j)
  have hmap := congrArg π hmul
  have habs : π (CFC.abs x) = CFC.abs (π x) := starAlgHom_map_abs π x
  rw [map_mul] at hmap
  have habs' : π (CFC.abs x) = CFC.abs (u : C) := habs.trans (congrArg CFC.abs hx)
  have huabs : CFC.abs (u : C) = 1 := by
    rw [CFC.abs, u.property.1, CFC.sqrt_one]
  rw [habs', huabs, mul_one, hx] at hmap
  exact ⟨v, hmap⟩

end

end KadisonKastler

end OAI
