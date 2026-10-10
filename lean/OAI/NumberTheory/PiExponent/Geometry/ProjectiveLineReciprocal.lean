import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (F : Type u) [CommRing F]

private def inverseCoordinateUnit : (LaurentPolynomial F)ˣ where
  val := LaurentPolynomial.T (-1)
  inv := LaurentPolynomial.T 1
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num

private lemma zeroEvaluation_eq :
    (zeroPolynomialMap F).comp (lineEvaluation F false) =
      MvPolynomial.eval₂Hom LaurentPolynomial.C
        (fun j : Bool => if j = false then 1 else LaurentPolynomial.T 1) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [zeroPolynomialMap]
  · intro j
    cases j <;> simp [zeroPolynomialMap]

private lemma infinityEvaluation_eq :
    (infinityPolynomialMap F).comp (lineEvaluation F true) =
      MvPolynomial.eval₂Hom LaurentPolynomial.C
        (fun j : Bool => LaurentPolynomial.T (-1) *
          (if j = false then 1 else LaurentPolynomial.T 1)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, lineEvaluation_C, infinityPolynomialMap_C, MvPolynomial.eval₂Hom_C]
  · intro j
    simp only [RingHom.comp_apply, lineEvaluation_X, MvPolynomial.eval₂Hom_X']
    cases j with
    | false =>
      change infinityPolynomialMap F Polynomial.X = LaurentPolynomial.T (-1) * 1
      rw [infinityPolynomialMap_X, mul_one]
    | true =>
      change infinityPolynomialMap F 1 = LaurentPolynomial.T (-1) * LaurentPolynomial.T 1
      rw [map_one, ← LaurentPolynomial.T_add]
      norm_num

@[reassoc] theorem reciprocalChart_compatibility :
    zeroChartOverlap F ≫ chartMap F false =
      infinityChartOverlap F ≫ chartMap F true := by
  unfold zeroChartOverlap infinityChartOverlap
  rw [chartMap_eq_fromUnitCoordinate, chartMap_eq_fromUnitCoordinate,
    fromUnitCoordinate_natural, fromUnitCoordinate_natural]
  let f := (zeroPolynomialMap F).comp (lineEvaluation F false)
  let g := (infinityPolynomialMap F).comp (lineEvaluation F true)
  have hf : IsUnit (f (MvPolynomial.X false)) := by simp [f, zeroPolynomialMap]
  have hg : IsUnit (g (MvPolynomial.X false)) := by
    simpa [g, infinityPolynomialMap] using LaurentPolynomial.isUnit_T (R := F) (-1)
  have hg' : IsUnit (g (MvPolynomial.X true)) := by simp [g, infinityPolynomialMap]
  have H : ∀ n p, p ∈ PolyGrade F Bool n →
      g p = (inverseCoordinateUnit F : LaurentPolynomial F) ^ n * f p := by
    intro n p hp
    change ((infinityPolynomialMap F).comp (lineEvaluation F true)) p = _
    rw [infinityEvaluation_eq]
    change MvPolynomial.eval₂ _ _ p = _
    rw [homogeneous_eval₂_scale hp]
    congr 1
    exact (RingHom.congr_fun (zeroEvaluation_eq F) p).symm
  exact (fromUnitCoordinate_scale (𝒜 := PolyGrade F Bool) f (by decide)
    (poly_X_mem false) hf g hg (inverseCoordinateUnit F) H).trans
      (fromUnitCoordinate_eq (𝒜 := PolyGrade F Bool) g (by decide) (by decide)
        (poly_X_mem false) (poly_X_mem true) hg hg')

theorem reciprocalChart_isPullback :
    CategoryTheory.IsPullback (infinityChartOverlap F) (zeroChartOverlap F)
      (chartMap F true) (chartMap F false) := by
  apply IsOpenImmersion.isPullback
  · exact reciprocalChart_compatibility F
  · rw [← show (!false) = true from rfl, chartMap_preimage_other,
      zeroChartOverlap_opensRange]

def affineChartCover : (projectiveLine F).OpenCover where
  I₀ := Bool
  X _ := Spec (CommRingCat.of (Polynomial F))
  f := chartMap F
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun i => inferInstance⟩
    intro x
    have hx : x ∈ (⨆ i : Bool, (chartMap F i).opensRange) := by
      rw [chartMap_cover]
      trivial
    rcases TopologicalSpace.Opens.mem_iSup.mp hx with ⟨i, hi⟩
    exact ⟨i, hi⟩

end PiExponent.ProjectiveLine

end

end OAI
