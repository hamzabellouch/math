import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransportNaturality
import OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPowerRestriction
import OAI.NumberTheory.PiExponent.Approximation.AddEquivSignedSum
import OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase

namespace OAI

namespace PiExponent.ReesSheafCechNaturality
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
open PiExponent.ReesSheafCechBase PiExponent.ReesFrozenChart
open PiExponent.ReesFrozenPower
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
attribute [local irreducible] PiExponent.ExceptionalRepresentedTypes.Frame
  PiExponent.ExceptionalRepresentedTypes.Sections
  PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped
  PiExponent.ExceptionalRepresentedTypes.restrictSections
  PiExponent.ExceptionalRepresentedTypes.transportSections
  PiExponent.ReesFrozenPower.pieceEquiv PiExponent.ReesFrozenPower.powerEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

private abbrev chartMap {s : Finset J} (hs : s.Nonempty) :
    Spec (CommRingCat.of (coordinateRing I a s)) ⟶ affineBlowup I :=
  chart I a hs

private local instance frozenChartOpenImmersion {s : Finset J} (hs : s.Nonempty) :
    IsOpenImmersion (chartMap I a hs) :=
  ReesFrozenChart.instIsOpenImmersionChart I a hs

private abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

theorem chartOpen_le {s t : Finset J} (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t) :
    (chartOpen I a ht).1 ≤ (chartOpen I a hs).1 :=
  ExceptionalAffineChart.opensRange_le (chartMap I a hs) (chartMap I a ht)
    (restriction I a hst)
    (ReesFrozenChart.restriction_chart I a hs ht hst)

theorem chartHomEquiv_restrict {s t : Finset J} (hs : s.Nonempty) (ht : t.Nonempty)
    {p r : J} (hp : p ∈ s) (hr : r ∈ t) (hst : s ⊆ t) (n : ℕ)
    (b : ExceptionalRepresentedTypes.Sections (chartMap I a hs) (exceptionalLineBundle I) n) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    chartHomEquiv I a ht hr n
      (ExceptionalRepresentedTypes.restrictSections (chartMap I a hs) (chartMap I a ht)
        (restriction I a hst) (restriction_chart I a hs ht hst)
        (exceptionalLineBundle I) n b) =
      GradedCech.setRestriction (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem hst n (chartHomEquiv I a hs hp n b) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  apply (pieceEquiv I a hr n).injective
  apply Subtype.ext
  rw [chartHomEquiv_pieceEquiv, pieceEquiv_restriction I a hp hr hst n,
    chartHomEquiv_pieceEquiv]
  exact ExceptionalRepresentedTypes.representedSectionsTyped_restrict
    (chartMap I a hs) (chartMap I a ht) (restriction I a hst)
    (restriction_chart I a hs ht hst) I (projection I)
    (base I a s) (chart_projection I a hs) (exceptionalLineBundle I)
    (exceptionalInclusion I) (exceptional_presents I) (chartFrameTyped I a hs hp)
    (base I a t) (chart_projection I a ht) (chartFrameTyped I a ht hr) n b

theorem tupleHomEquiv_restrict (n q : ℕ) (t : Fin (q + 2) → J) (k : Fin (q + 2))
    (b : schemeFreeOpen (affineBlowup I)
      (CechHigher.intersection (opens I a) (t ∘ k.succAbove)) ⟶ exceptionalPower I n) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    tupleHomEquiv I a n (q+1) t
      (CechOne.restrictHom _ (CechHigher.faceLE (opens I a) t k) b) =
      GradedCech.setRestriction (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) n
        (tupleHomEquiv I a n q (t ∘ k.succAbove) b) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  change chartHomEquiv I a _ _ n
    (ExceptionalRepresentedTypes.transportSections
      (chartMap I a (tuple_nonempty (q+1) t)) (exceptionalLineBundle I) n
      (tupleOpen_eq I a (q+1) t)
      (freeOpenMap _ (homOfLE (CechHigher.faceLE (opens I a) t k)) ≫ b)) = _
  rw [ExceptionalRepresentedTypes.transportSections_restrict
    (chartMap I a (tuple_nonempty q (t ∘ k.succAbove)))
    (chartMap I a (tuple_nonempty (q+1) t))
    (restriction I a (tupleSet_comp_subset t k.succAbove))
    (restriction_chart I a (tuple_nonempty q (t ∘ k.succAbove))
      (tuple_nonempty (q+1) t) (tupleSet_comp_subset t k.succAbove))
    (exceptionalLineBundle I) n
    (tupleOpen_eq I a q (t ∘ k.succAbove)) (tupleOpen_eq I a (q+1) t)
    (CechHigher.faceLE (opens I a) t k) b]
  exact chartHomEquiv_restrict I a (tuple_nonempty q (t ∘ k.succAbove))
    (tuple_nonempty (q+1) t) (tuple_mem q (t ∘ k.succAbove) 0)
    (tuple_mem (q+1) t 0) (tupleSet_comp_subset t k.succAbove) n _

theorem cochainEquiv_differential (n q : ℕ)
    (c : CechHigher.Cochain (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    cochainEquiv I a n (q+1) (CechHigher.differential _ (opens I a) (exceptionalPower I n) c) =
      GradedCech.differential (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem n (cochainEquiv I a n q c) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  funext t
  let : AddCommGroup (ReesLocalizedIntersections.Piece I a (tupleSet t) n) :=
    AddSubgroup.toAddCommGroup _
  let : AddCommGroup
      (freeOpen (affineBlowup I).ringCatSheaf (CechHigher.intersection (opens I a) t) ⟶
        exceptionalPower I n) :=
    Preadditive.homGroup (C := (affineBlowup I).Modules) _ _
  change tupleHomEquiv I a n (q+1) t
    (∑ k : Fin (q+2), (-1 : ℤ)^k.val •
      CechOne.restrictHom _ (CechHigher.faceLE (opens I a) t k) (c (t ∘ k.succAbove))) = _
  exact AddEquivSignedSum.map_signed_sum_eq
    (A := (schemeFreeOpen (affineBlowup I)
      (CechHigher.intersection (opens I a) t) ⟶ exceptionalPower I n))
    (B := ReesLocalizedIntersections.Piece I a (tupleSet t) n)
    (tupleHomEquiv I a n (q+1) t) q
    (fun k => CechOne.restrictHom _ (CechHigher.faceLE (opens I a) t k)
      (c (t ∘ k.succAbove)))
    (fun k => GradedCech.setRestriction (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) n
      (tupleHomEquiv I a n q (t ∘ k.succAbove) (c (t ∘ k.succAbove))))
    (fun k => tupleHomEquiv_restrict I a n q t k (c (t ∘ k.succAbove)))

end
end PiExponent.ReesSheafCechNaturality

end OAI
