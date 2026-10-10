import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.ProjectiveChartSections
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveLaurentTransitions
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinateFiniteRingEquiv_ratio (i : σ) (a : Finset (ChartVariables i)) (j : σ) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (coordinateRatioOn (s i) (s j)
        (show coordinateFiniteOpen M s i a ≤ SectionOpens.isoOpen (s i) from inf_le_left)) =
      algebraMap _ _ (chartToPoly (R := K) i (chartCoordinate i j)) :=
  coordinateFiniteRingEquiv_coordinate M s k hc f hf i a j

lemma coordinateFiniteTransition_X (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
    (l : ChartVariables i) :
    coordinateFiniteTransition M s k hc f hf i j a b h
      (algebraMap _ _ (MvPolynomial.X (R := K) l)) =
      coordinateFiniteRingEquiv M s k hc f hf j b
        (coordinateRatioOn (s i) (s l.val) (h.trans inf_le_left)) := by
  change coordinateFiniteRingEquiv M s k hc f hf j b
    (X.presheaf.map (homOfLE h).op
      ((coordinateFiniteRingEquiv M s k hc f hf i a).symm _)) = _
  rw [coordinateFiniteRingEquiv_symm_X]
  change coordinateFiniteRingEquiv M s k hc f hf j b
    (X.presheaf.map (homOfLE h).op (coordinateRatioOn (s i) (s l.val) inf_le_left)) = _
  erw [coordinateRatioOn_restrict]

variable [Fintype σ]

lemma coordinateFiniteRingEquiv_ratio_full (i : σ) (a : Finset (ChartVariables i)) (j : σ) :
    overlapToFull i a (coordinateFiniteRingEquiv M s k hc f hf i a
      (coordinateRatioOn (s i) (s j)
        (show coordinateFiniteOpen M s i a ≤ SectionOpens.isoOpen (s i) from inf_le_left))) =
      AddMonoidAlgebra.single (standardExponent j 1 - standardExponent i 1) 1 := by
  classical
  rw [coordinateFiniteRingEquiv_ratio, chartToPoly_coordinate]
  by_cases hji : j = i
  · subst j
    simp only [dite_true, map_one, sub_self]
    rfl
  · rw [dite_eq_right hji, overlapToFull_X]

lemma coordinateFiniteTransition_X_full (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
    (l : ChartVariables i) :
    overlapToFull j b (coordinateFiniteTransition M s k hc f hf i j a b h
      (algebraMap _ _ (MvPolynomial.X (R := K) l))) =
      AddMonoidAlgebra.single (standardExponent l.val 1 - standardExponent i 1) 1 := by
  let r := coordinateFiniteRingEquiv M s k hc f hf j b
  let hi : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s i) := h.trans inf_le_left
  let hj : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s j) := inf_le_left
  have hinv : r (coordinateRatioOn (s j) (s i) hj) *
      r (coordinateRatioOn (s i) (s j) hi) = 1 := by
    rw [← map_mul, coordinateRatioOn_reciprocal, map_one]
  calc
    _ = overlapToFull j b
        (r (coordinateRatioOn (s j) (s l.val) hj) *
          r (coordinateRatioOn (s i) (s j) hi)) := by
      rw [coordinateFiniteTransition_X,
        coordinateRatioOn_change (s j) (s i) (s l.val) hj hi, map_mul, mul_comm]
    _ = _ := overlapToFull_ratio i j l.val b _ _ _
      (coordinateFiniteRingEquiv_ratio_full M s k hc f hf j b l.val)
      (coordinateFiniteRingEquiv_ratio_full M s k hc f hf j b i) hinv

lemma coordinateFiniteTransition_full (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a) :
    (overlapToFull j b).comp (coordinateFiniteTransition M s k hc f hf i j a b h) =
      overlapToFull i a := by
  apply overlapToFull_natural_of_generators
  · intro r
    rw [coordinateFiniteTransition_constant, overlapToFull_C]
  · intro l
    exact coordinateFiniteTransition_X_full M s k hc f hf i j a b h l

end
end PiExponentSeshadri.Projective

end OAI
