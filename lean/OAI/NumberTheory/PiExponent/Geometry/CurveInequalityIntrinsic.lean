import OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights
import OAI.NumberTheory.PiExponent.Geometry.CurveInequality
import OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight
import OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveInequality

open CurveValuationCenter PlaceValuationRing CurveContactFamily PersistentWeightComparison


variable {E : Type*} [Field E] [Algebra ℂ E]

theorem nonconstant_coordinates {n : ℕ} (z : Fin n → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ∃ i, Transcendental ℂ (z i) := by
  let : Algebra.Transcendental ℂ E := trdeg_ne_zero_iff.mp (by rw [htrdeg]; exact one_ne_zero)
  exact CurveCenters.exists_transcendental_coordinate z hgen
    (Algebra.Transcendental.transcendental (R := ℂ) (A := E))

variable [Algebra.EssFiniteType ℂ E]

theorem weighted_curve_inequality {m K : ℕ}
    (y : E) (x : Fin m → E) (c : Fin K → Fin m → ℂ)
    (hc : ∀ i, Function.Injective (fun j => c j i))
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hfibrevol : (K : ℝ) * (1+3*(sigma : ℝ))^m *
      (∏ i : Fin m, (w i.succ : ℝ)) / (∏ i : Fin m, (v i.succ : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ : ℝ) < v i.succ) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let z : Fin (m+1) → E := Fin.cases y x
    let hz := nonconstant_coordinates z hgen htrdeg
    (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz,
      (contact hres hfinite z c hz v p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z w := by
  dsimp only
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let z : Fin (m+1) → E := Fin.cases y x
  have hz := nonconstant_coordinates z hgen htrdeg
  change (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz,
    (contact hres hfinite z c hz v p : ℝ) ≤ CurveContactSum.weightedDegree hfinite z w
  by_contra h
  have hexcess := lt_of_not_ge h
  have hy := excess_implies_zeroth_eq_one hres hfinite z c hz
    (CurvePrimeHeight.kernel_height_succ_le z hgen htrdeg)
    w v hw hv sigma hsigma hvol hseparated hexcess
  change y = 1 at hy
  subst y
  have hgenx := CurveFieldRigidity.fibre_generates x hgen
  have hheight := CurvePrimeHeight.kernel_height_le x hgenx htrdeg
  have hconst := excess_implies_fibre_coordinate_constant hres hfinite x c hz hheight
    w v hw hv sigma hsigma hfibrevol hseparated hexcess
  exact no_fibre_excess_of_constant_coordinate hres hfinite x c hc hz
    w v hw hv sigma hsigma hratio hconst hexcess

theorem admissible_weighted_curve_inequality {nu Lambda C : ℝ}
    (d : AdmissibleParameters nu Lambda C)
    (y : E) (x : Fin d.m → E) (c : Fin d.K → Fin d.m → ℂ)
    (hc : ∀ i, Function.Injective (fun j => c j i))
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let z : Fin (d.m+1) → E := Fin.cases y x
    let hz := nonconstant_coordinates z hgen htrdeg
    (1+(d.sigma : ℝ)) * ∑ p ∈ places hfinite z c hz,
      (contact hres hfinite z c hz d.curveJetWeights p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z d.curveDegreeWeights :=
  weighted_curve_inequality y x c hc hgen htrdeg
    d.curveDegreeWeights d.curveJetWeights d.curveDegreeWeights_pos d.curveJetWeights_pos
    d.sigma (by exact_mod_cast d.sigma_pos) d.curve_volume d.curve_fibre_volume
    d.curve_separated_weight_products d.curve_coordinate_ratio

end PiExponent.CurveInequality
end

end OAI
