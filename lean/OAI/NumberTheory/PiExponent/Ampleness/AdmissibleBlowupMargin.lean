import OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry
import OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupMargin
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
open AdmissibleBlowupGeometry BlowupCurveMargin
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

structure AffineCurveDegreeData (C : IntegralCurve (blowup d)) where
  E : Type
  [field : Field E]
  [algebra : Algebra ℂ E]
  [essFiniteType : Algebra.EssFiniteType ℂ E]
  y : E
  x : Fin d.m → E
  coordinates_generate : IntermediateField.adjoin ℂ
    (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤
  trdeg_one : Algebra.trdeg ℂ E = 1
  hyperplane_degree : (curveDegree (structureMap d) (A d) C : ℝ) =
    ((scale d).radius : ℝ) * poleDegree d y x trdeg_one
  exceptional_degree : (curveDegree (structureMap d) (J d) C : ℝ) =
    -((scale d).radius : ℝ) * contactSum d y x coordinates_generate trdeg_one

theorem uniform_margin_of_affine_curve_data
    (a : ℕ) (ha : 1 < a) (hample : (((A d).pow a).tensor (J d)).IsAmple)
    (hdata : ∀ C : IntegralCurve (blowup d),
      (¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ ({x} : Set _)) →
      (∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) →
      Nonempty (AffineCurveDegreeData d C)) :
    ∀ C : IntegralCurve (blowup d),
      marginCoefficient a d.sigma *
          (curveDegree (structureMap d) (((A d).pow a).tensor (J d)) C : ℝ) ≤
        (curveDegree (structureMap d) ((A d).tensor (J d)) C : ℝ) := by
  classical
  intro C
  by_cases hc : ∃ x : compactification d,
      Set.range (C.embedding ≫ projection d) ⊆ ({x} : Set _)
  · obtain ⟨x,hx⟩ := hc
    exact margin_of_contracted (structureMap d) (projection d) (hyperplane d) (J d)
      a ha hample d.sigma d.sigma_pos C x hx
  · by_cases hm : ∃ c : C.scheme,
        (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange
    · obtain ⟨r⟩ := hdata C hc hm
      let := r.field
      let := r.algebra
      let := r.essFiniteType
      exact margin_of_actual_contact_degrees d (structureMap d) (A d) (J d)
        a ha hample C r.y r.x r.coordinates_generate r.trdeg_one
        (scale d).radius (by exact_mod_cast (scale d).radius_pos)
        r.hyperplane_degree r.exceptional_degree
    · exact margin_of_image_outside_chart (structureMap d) (centerIdeal d)
        (projection d) (A d) (J d) (exceptionalInclusion d) (exceptional_presents d)
        a ha hample d.sigma d.sigma_pos C (affineChart d).opensRange
        (centerIdeal_support_subset_chart d) (fun c hh => hm ⟨c,hh⟩)

theorem exists_positive_uniform_margin_of_affine_curve_data
    (a : ℕ) (ha : 1 < a) (hample : (((A d).pow a).tensor (J d)).IsAmple)
    (hdata : ∀ C : IntegralCurve (blowup d),
      (¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ ({x} : Set _)) →
      (∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) →
      Nonempty (AffineCurveDegreeData d C)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : IntegralCurve (blowup d),
      ε * (curveDegree (structureMap d) (((A d).pow a).tensor (J d)) C : ℝ) ≤
        (curveDegree (structureMap d) ((A d).tensor (J d)) C : ℝ) :=
  ⟨marginCoefficient a d.sigma,marginCoefficient_pos ha d.sigma_pos,
    uniform_margin_of_affine_curve_data d a ha hample hdata⟩

end PiExponent.AdmissibleBlowupMargin

end

end OAI
