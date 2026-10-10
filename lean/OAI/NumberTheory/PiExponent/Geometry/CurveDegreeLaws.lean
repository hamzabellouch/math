import OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem curveLineCohomologyTwoZero_of_ample
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (C : IntegralCurve X) :
    CurveDegree.LineCohomologyTwoZero C.scheme := by
  intro M
  have hz := lineBundle_cohomology_zero_of_dimension_le 1 (C.embedding ≫ p)
    (H.pullback C.embedding) (hH.pullback_closedImmersion H C.embedding) M
    C.dimension.le 2 (by omega)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

theorem curveDegree_pow_of_ample
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (C : IntegralCurve X) (n : ℕ) :
    curveDegree p (L.pow n) C = (n : ℤ) * curveDegree p L C :=
  curveDegree_pow p H hH L C
    (CurveDegree.finite_line_cohomology_of_ample (C.embedding ≫ p) (H.pullback C.embedding)
      (hH.pullback_closedImmersion H C.embedding))
    (curveLineCohomologyTwoZero_of_ample p H hH C) n

theorem curveDegree_tensor_of_ample
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L M : LineBundle X) (C : IntegralCurve X) :
    curveDegree p (L.tensor M) C = curveDegree p L C + curveDegree p M C :=
  curveDegree_tensor p H hH L M C
    (CurveDegree.finite_line_cohomology_of_ample (C.embedding ≫ p) (H.pullback C.embedding)
      (hH.pullback_closedImmersion H C.embedding))
    (curveLineCohomologyTwoZero_of_ample p H hH C)

theorem curveDegree_inverse_of_ample
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (C : IntegralCurve X) :
    curveDegree p L.inverse C = -curveDegree p L C :=
  curveDegree_inverse p H hH L C
    (CurveDegree.finite_line_cohomology_of_ample (C.embedding ≫ p) (H.pullback C.embedding)
      (hH.pullback_closedImmersion H C.embedding))
    (curveLineCohomologyTwoZero_of_ample p H hH C)

theorem curveDegree_pos_of_uniform_margin
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (C : IntegralCurve X) : 0 < curveDegree p L C := by
  have hHpos : (0 : ℝ) < (curveDegree p H C : ℝ) := by
    exact_mod_cast curveDegree_pos_of_ample p H hH C
  have hpos : (0 : ℝ) < (curveDegree p L C : ℝ) := (mul_pos hε hHpos).trans_le (hmargin C)
  exact_mod_cast hpos

theorem uniform_margin_tensor_powers
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (ε : ℝ)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (a b : ℕ) (C : IntegralCurve X) :
    ((b:ℝ)*ε+a) * (curveDegree p H C : ℝ) ≤
      (curveDegree p ((L.pow b).tensor (H.pow a)) C : ℝ) := by
  rw [curveDegree_tensor_of_ample p H hH,
    curveDegree_pow_of_ample p H hH L C b, curveDegree_pow_of_ample p H hH H C a]
  push_cast
  have h := mul_le_mul_of_nonneg_left (hmargin C) (Nat.cast_nonneg b : (0:ℝ) ≤ b)
  nlinarith

end
end PiExponent.NumericalAmpleness

end OAI
