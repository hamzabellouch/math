import OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic
import OAI.NumberTheory.PiExponent.Geometry.CurveInequalityIntrinsic

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.AdmissibleParameters

variable {nu Lambda C : ℝ} (d : AdmissibleParameters nu Lambda C)

def curveCenters : Fin d.K → Fin d.m → ℂ :=
  fun j i => (j.val : ℂ) *
    MatrixArithmetic.rationalCenters (fun i : Fin d.m => d.p i.val)
      (fun i : Fin d.m => d.q i.val) i

theorem curveCenters_injective (i : Fin d.m) :
    Function.Injective (fun j => d.curveCenters j i) := by
  have hp : (d.p i.val : ℂ) ≠ 0 := by exact_mod_cast (d.approximations i.val).2.1
  have hq : (d.q i.val : ℂ) ≠ 0 := by
    exact_mod_cast (show d.q i.val ≠ 0 by have := (d.approximations i.val).1; omega)
  have hr : MatrixArithmetic.rationalCenters (fun i : Fin d.m => d.p i.val)
      (fun i : Fin d.m => d.q i.val) i ≠ 0 := by
    unfold MatrixArithmetic.rationalCenters
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hq
  intro j l h
  dsimp only [curveCenters] at h
  have he := (mul_right_cancel₀ hr h : (j.val : ℂ) = (l.val : ℂ))
  apply Fin.ext
  exact_mod_cast he

theorem exact_weighted_curve_inequality
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let z : Fin (d.m+1) → E := Fin.cases y x
    let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
    (1+(d.sigma : ℝ)) * ∑ p ∈ CurveContactFamily.places hfinite z d.curveCenters hz,
      (CurveContactFamily.contact hres hfinite z d.curveCenters hz d.curveJetWeights p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z d.curveDegreeWeights :=
  CurveInequality.admissible_weighted_curve_inequality d y x d.curveCenters
    d.curveCenters_injective hgen htrdeg

end PiExponent.AdmissibleParameters
end

end OAI
