import OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra
import OAI.NumberTheory.PiExponent.Ampleness.NakaiInductionStep

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def LowerClosedNumericalCriterion (p : X ⟶ Spec (CommRingCat.of ℂ))
    (H : LineBundle X) (d : ℕ) : Prop :=
  ∀ (I : X.IdealSheafData), topologicalKrullDim I.subscheme ≤ d →
    ∀ (M : LineBundle I.subscheme) (δ : ℝ), 0 < δ →
      (∀ C : IntegralCurve I.subscheme,
        δ * (curveDegree (I.subschemeι ≫ p) (H.pullback I.subschemeι) C : ℝ) ≤
          (curveDegree (I.subschemeι ≫ p) M C : ℝ)) → M.IsAmple

theorem slope_lower_closed_ampleness
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hlower : LowerClosedNumericalCriterion p H d)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (a b : ℕ) (hb : 0 < b) :
    ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      ((slopeBundle L H a b).pullback I.subschemeι).IsAmple := by
  intro I hI
  have hδ : (0:ℝ) < (b:ℝ)*ε+a :=
    add_pos_of_pos_of_nonneg (mul_pos (by exact_mod_cast hb) hε) (Nat.cast_nonneg a)
  apply hlower I hI ((slopeBundle L H a b).pullback I.subschemeι) ((b:ℝ)*ε+a) hδ
  exact uniform_curve_margin_restrict p (slopeBundle L H a b) H ((b:ℝ)*ε+a)
    (uniform_margin_tensor_powers p H L hH ε hmargin a b) I.subschemeι

theorem ample_slope_of_topEuler_pos_of_lower_criterion [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : LowerClosedNumericalCriterion p H d)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (a b : ℕ) (hb : 0 < b)
    (htop : 0 < (fwdDiff (1:ℕ))^[d+1]
      (fun n => eulerCharacteristic p (d+1) ((slopeBundle L H a b).pow n).sheaf) 0) :
    (slopeBundle L H a b).IsAmple := by
  have hδ : (0:ℝ) < (b:ℝ)*ε+a :=
    add_pos_of_pos_of_nonneg (mul_pos (by exact_mod_cast hb) hε) (Nat.cast_nonneg a)
  exact isAmple_of_lower_ampleness_of_topEuler_pos_of_margin p r i hi H
    (slopeBundle L H a b) hH d hdim
    (slope_lower_closed_ampleness p H L hH d hlower ε hε hmargin a b hb)
    htop ((b:ℝ)*ε+a) hδ (uniform_margin_tensor_powers p H L hH ε hmargin a b)

theorem ample_slope_of_polynomial_pos_of_lower_criterion [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : LowerClosedNumericalCriterion p H d)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (P : Polynomial ℝ)
    (hP : ∀ a b : ℕ, 0 < b →
      (((fwdDiff (1:ℕ))^[d+1]
        (fun n => eulerCharacteristic p (d+1) ((slopeBundle L H a b).pow n).sheaf) 0 : ℤ):ℝ) =
        (b:ℝ)^(d+1) * P.eval ((a:ℝ)/b))
    (a b : ℕ) (hb : 0 < b) (hpos : 0 < P.eval ((a:ℝ)/b)) :
    (slopeBundle L H a b).IsAmple := by
  apply ample_slope_of_topEuler_pos_of_lower_criterion p r i hi H L hH d hdim hlower ε hε hmargin a b hb
  have hreal : (0:ℝ) <
      (((fwdDiff (1:ℕ))^[d+1]
        (fun n => eulerCharacteristic p (d+1) ((slopeBundle L H a b).pow n).sheaf) 0 : ℤ):ℝ) := by
    rw [hP a b hb]
    exact mul_pos (pow_pos (by exact_mod_cast hb) _) hpos
  exact_mod_cast hreal

end
end PiExponent.NumericalAmpleness

end OAI
