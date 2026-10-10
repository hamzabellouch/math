import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree
import OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleCurveModel
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open AdmissibleBlowupGeometry CurveNormalizationModel
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

def degreeData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (r : ModelData d C) : AdmissibleBlowupMargin.AffineCurveDegreeData d C := by
  letI := r.field
  letI := r.algebra
  letI := r.essFiniteType
  letI := r.parameterFinite
  letI := r.normalizationFinite
  letI := r.chartIso
  let y := r.coordinates 0
  let x := fun i : Fin d.m => r.coordinates i.succ
  have htuple : (Fin.cases y x : Fin (d.m+1) → r.E) = r.coordinates := by
    funext i
    cases i using Fin.cases <;> rfl
  have hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → r.E)) = ⊤ := by
    rw [htuple]
    exact r.coordinates_generate
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ r.E r.trdeg_one
  have hA : (NumericalAmpleness.curveDegree (structureMap d) (A d) C : ℝ) =
      ((scale d).radius : ℝ) * BlowupCurveMargin.poleDegree d y x r.trdeg_one := by
    change _ = ((scale d).radius : ℝ) *
      CurveContactSum.weightedDegree hfinite (Fin.cases y x) d.curveDegreeWeights
    rw [htuple]
    exact CurveNormalizedDegreeTransfer.weighted_curveDegree
      (exponents d) r.coordinates (constantIndex d)
      ((scale d).exponents_constant d.curveDegreeWeights_pos)
      (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)
      (structureMap d) (H d) (H_ample d) C r.parameter r.parameter_transcendental
      r.normalization r.normalization_over r.chart r.chart_nonempty
      (projection d) r.generic_coordinates d.curveDegreeWeights d.curveDegreeWeights_pos
      (by exact_mod_cast (scale d).radius_pos) (scale d).degreePowers
      (scale d).degreePowers_eq (pureIndex d)
      ((scale d).exponents_pure d.curveDegreeWeights_pos)
      ((scale d).budget d.curveDegreeWeights_pos) hfinite
  have hgeneric : parameterCurveGenericPoint r.parameter r.parameter_transcendental ≫
      (r.normalization ≫ C.embedding) ≫ projection d =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (Fin.cases y x)).toRingHom) ≫
        affineChart d := by
    have heval : (MvPolynomial.aeval r.coordinates).toRingHom =
        MvPolynomial.eval₂Hom (algebraMap ℂ r.E) r.coordinates := by
      apply RingHom.ext
      intro P
      exact MvPolynomial.aeval_def r.coordinates P
    rw [htuple, heval]
    simpa only [Category.assoc, CurveMonomialMap.genericMonomialMap, affineChart] using
      r.generic_coordinates
  have hJ : (NumericalAmpleness.curveDegree (structureMap d) (J d) C : ℝ) =
      -((scale d).radius : ℝ) * BlowupCurveMargin.contactSum d y x hgen r.trdeg_one := by
    have hd := CurveNormalizedDegreeTransfer.curveDegree_eq_normalized
      (structureMap d) (H d) (H_ample d) C r.parameter r.parameter_transcendental
      r.normalization r.normalization_over r.chart r.chart_nonempty (J d)
    have hn := ExceptionalCurveDegree.admissible_degree_eq_neg_contactSum
      d y x hgen r.trdeg_one r.parameter r.parameter_transcendental
      (r.normalization ≫ C.embedding) hgeneric
    exact (congrArg (fun n : ℤ => (n : ℝ)) hd).trans hn
  exact { E := r.E
          field := r.field
          algebra := r.algebra
          essFiniteType := r.essFiniteType
          y := y
          x := x
          coordinates_generate := hgen
          trdeg_one := r.trdeg_one
          hyperplane_degree := hA
          exceptional_degree := hJ }

end PiExponent.AdmissibleCurveModel

end

end OAI
