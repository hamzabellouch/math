import OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive
import OAI.NumberTheory.PiExponent.Ampleness.NefAmple
import OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree
import OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveInequality
import OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway

namespace OAI

noncomputable section
namespace PiExponent.BlowupCurveMargin
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open NumericalAmpleness
variable {B X : Scheme.{0}}

theorem curve_degree_laws (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle B) (hH : H.IsAmple) (C : IntegralCurve B) :
    (∀ L M : LineBundle B, curveDegree p (L.tensor M) C =
      curveDegree p L C + curveDegree p M C) ∧
    (∀ (L : LineBundle B) (n : ℕ), curveDegree p (L.pow n) C =
      (n : ℤ) * curveDegree p L C) := by
  let HC := H.pullback C.embedding
  have hHC : HC.IsAmple := LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding
  have hfinite := CurveDegree.finite_line_cohomology_of_ample (C.embedding ≫ p) HC hHC
  have hH2 : CurveDegree.LineCohomologyTwoZero C.scheme := by
    intro M
    exact ⟨fun a b =>
      (lineBundle_cohomology_zero_of_dimension_le 1 (C.embedding ≫ p) HC hHC M
        C.dimension.le 2 (by omega) a).trans
      (lineBundle_cohomology_zero_of_dimension_le 1 (C.embedding ≫ p) HC hHC M
        C.dimension.le 2 (by omega) b).symm⟩
  exact ⟨fun L M => curveDegree_tensor p H hH L M C hfinite hH2,
    fun L n => curveDegree_pow p H hH L C hfinite hH2 n⟩

def marginCoefficient (a : ℕ) (σ : ℝ) : ℝ := σ / ((a : ℝ) * (1 + σ) - 1)

theorem marginCoefficient_pos {a : ℕ} (ha : 1 < a) {σ : ℝ} (hσ : 0 < σ) :
    0 < marginCoefficient a σ := by
  apply div_pos hσ
  exact NefAmple.combination_denominator_pos (by exact_mod_cast ha) hσ

theorem margin_of_nonnegative_degree
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (hn : 0 ≤ (curveDegree p A C : ℝ) + (1 + σ) * (curveDegree p J C : ℝ)) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) := by
  obtain ⟨ht,hp⟩ := curve_degree_laws p ((A.pow a).tensor J) hample C
  rw [ht, hp, ht]
  push_cast
  unfold marginCoefficient
  have ha' : 1 < (a : ℝ) := by exact_mod_cast ha
  have hd := NefAmple.combination_denominator_pos ha' hσ
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  have hn' := mul_nonneg (sub_pos.mpr ha').le hn
  nlinarith

theorem curveDegree_zero_of_frame (p : B ⟶ Spec (.of ℂ))
    (J : LineBundle B) (C : IntegralCurve B)
    (e : (J.pullback C.embedding).sheaf ≅ structureSheaf C.scheme) :
    curveDegree p J C = 0 := by
  unfold curveDegree
  change eulerCharacteristic (C.embedding ≫ p) 1 (J.pullback C.embedding).sheaf - _ = 0
  rw [eulerCharacteristic_iso (C.embedding ≫ p) e 1]
  exact sub_self _

theorem margin_of_exceptional_frame
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (e : (J.pullback C.embedding).sheaf ≅ structureSheaf C.scheme) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) := by
  have hj := curveDegree_zero_of_frame p J C e
  have hpos := curveDegree_pos_of_ample p ((A.pow a).tensor J) hample C
  obtain ⟨ht,hp⟩ := curve_degree_laws p ((A.pow a).tensor J) hample C
  rw [ht, hp, hj, add_zero] at hpos
  have ha' : (0 : ℤ) < a := by exact_mod_cast (Nat.zero_lt_of_lt ha)
  have hA := (mul_pos_iff_of_pos_left ha').mp hpos
  apply margin_of_nonnegative_degree p A J a ha hample σ hσ C
  rw [hj]
  simpa using (show (0 : ℝ) ≤ (curveDegree p A C : ℝ) by exact_mod_cast hA.le)

theorem margin_of_avoids_center
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (I : X.IdealSheafData) (π : B ⟶ X) (A J : LineBundle B)
    (ι : J.sheaf ⟶ structureSheaf B) (hJ : PresentsPullbackIdeal I π J ι)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (havoid : ∀ c : C.scheme, (C.embedding ≫ π) c ∉ I.support) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) :=
  margin_of_exceptional_frame p A J a ha hample σ hσ C
    (InvertibleIdealAway.pullbackIsoOfAvoids I π J ι hJ C.embedding havoid)

theorem margin_of_image_outside_chart
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (I : X.IdealSheafData) (π : B ⟶ X) (A J : LineBundle B)
    (ι : J.sheaf ⟶ structureSheaf B) (hJ : PresentsPullbackIdeal I π J ι)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (U : X.Opens) (hsupport : (I.support : Set X) ⊆ U)
    (hmiss : ∀ c : C.scheme, (C.embedding ≫ π) c ∉ U) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) :=
  margin_of_avoids_center p I π A J ι hJ a ha hample σ hσ C
    (fun c hc => hmiss c (hsupport hc))

theorem margin_of_contracted
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (π : B ⟶ X)
    (L : LineBundle X) (J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : (((L.pullback π).pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (x : X) (hc : Set.range (C.embedding ≫ π) ⊆ ({x} : Set X)) :
    marginCoefficient a σ * (curveDegree p (((L.pullback π).pow a).tensor J) C : ℝ) ≤
      (curveDegree p ((L.pullback π).tensor J) C : ℝ) := by
  have hA := ConstantPullbackDegree.curveDegree_eq_zero_of_contracted p L π C x hc
  have hpos := curveDegree_pos_of_ample p (((L.pullback π).pow a).tensor J) hample C
  obtain ⟨ht,hp⟩ := curve_degree_laws p (((L.pullback π).pow a).tensor J) hample C
  rw [ht, hp, hA, mul_zero, zero_add] at hpos
  apply margin_of_nonnegative_degree p (L.pullback π) J a ha hample σ hσ C
  rw [hA]
  exact add_nonneg (by norm_num) (mul_nonneg (by linarith)
    (by exact_mod_cast hpos.le))

variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)
variable {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]

def contactSum (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ℝ :=
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let z : Fin (d.m+1) → E := Fin.cases y x
  let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
  ∑ q ∈ CurveContactFamily.places hfinite z d.curveCenters hz,
    (CurveContactFamily.contact hres hfinite z d.curveCenters hz d.curveJetWeights q : ℝ)

def poleDegree (y : E) (x : Fin d.m → E) (htrdeg : Algebra.trdeg ℂ E = 1) : ℝ :=
  CurveContactSum.weightedDegree
    (CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg)
    (Fin.cases y x : Fin (d.m+1) → E) d.curveDegreeWeights

theorem actual_contact_bound (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    (1 + (d.sigma : ℝ)) * contactSum d y x hgen htrdeg ≤ poleDegree d y x htrdeg :=
  d.exact_weighted_curve_inequality y x hgen htrdeg

theorem margin_of_actual_contact_degrees
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (C : IntegralCurve B) (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) (R : ℚ) (hR : 0 < R)
    (hA : (curveDegree p A C : ℝ) = (R : ℝ) * poleDegree d y x htrdeg)
    (hJ : (curveDegree p J C : ℝ) = -(R : ℝ) * contactSum d y x hgen htrdeg) :
    marginCoefficient a d.sigma * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) := by
  apply margin_of_nonnegative_degree p A J a ha hample d.sigma d.sigma_pos C
  rw [hA, hJ]
  have hR' : (0 : ℝ) ≤ R := by exact_mod_cast hR.le
  have h := mul_le_mul_of_nonneg_left (actual_contact_bound d y x hgen htrdeg) hR'
  nlinarith


end PiExponent.BlowupCurveMargin

end

end OAI
