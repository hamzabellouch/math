import OAI.NumberTheory.PiExponent.Approximation.NumericalThresholdStep
import OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCurveMargin
import OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem eulerSlopePolynomial_pos_of_ample [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = d) (a b : ℕ) (hb : 0 < b)
    (hamp : (slopeBundle L H a b).IsAmple) :
    0 < (eulerSlopePolynomial p d L H).eval ((a:ℝ)/b) := by
  have hp : (0:ℝ) < (topEuler p d (slopeBundle L H a b) : ℝ) := by
    exact_mod_cast topEuler_pos_of_ample p (slopeBundle L H a b) hamp d hdim
  rw [topEuler_slopeBundle_eq p H hH L d hdim.le a b hb] at hp
  exact (mul_pos_iff_of_pos_left (pow_pos (by exact_mod_cast hb : (0:ℝ)<b) d)).mp hp

theorem eulerSlopePolynomial_derivative_margin [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = ((d+1:ℕ):WithBot ℕ∞))
    (ε : ℝ) (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (a b : ℕ) (hb : 0 < b) (hamp : (slopeBundle L H a b).IsAmple) :
    ((a:ℝ)/b+ε) * (eulerSlopePolynomial p (d+1) L H).derivative.eval ((a:ℝ)/b) ≤
      ((d+1:ℕ):ℝ) * (eulerSlopePolynomial p (d+1) L H).eval ((a:ℝ)/b) := by
  let M := slopeBundle L H a b
  let TL : ℝ := mixedEuler p (d+1) (L :: List.replicate d M)
  let TH : ℝ := mixedEuler p (d+1) (H :: List.replicate d M)
  let P := eulerSlopePolynomial p (d+1) L H
  have hdimle : topologicalKrullDim X ≤ d+1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hdim.le
  have hvolume := topEuler_slopeBundle_eq p H hH L (d+1) hdim.le a b hb
  have hsplit : (topEuler p (d+1) M : ℝ) = (b:ℝ)*TL+(a:ℝ)*TH := by
    dsimp only [M, TL, TH]
    exact_mod_cast topEuler_slopeBundle_split p H hH L d hdimle a b
  have heq : (b:ℝ)*TL+(a:ℝ)*TH = (b:ℝ)^(d+1)*P.eval ((a:ℝ)/b) :=
    hsplit.symm.trans hvolume
  have hderivative : (b:ℝ)^d * P.derivative.eval ((a:ℝ)/b) = ((d+1:ℕ):ℝ)*TH :=
    eulerSlopePolynomial_derivative_eval_nat_div p H hH L d hdimle a b hb
  have hmix : ε*TH ≤ TL := mixedTop_curve_margin p H L hH d hdim ε hmargin
    (List.replicate d M) (by simp) (by
      intro A hA
      obtain ⟨_,rfl⟩ := List.mem_replicate.mp hA
      exact hamp)
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hm : ((a:ℝ)+(b:ℝ)*ε)*TH ≤ (b:ℝ)*TL+(a:ℝ)*TH := by
    have h := mul_le_mul_of_nonneg_left hmix hbR.le
    nlinarith
  apply (mul_le_mul_iff_right₀ (pow_pos hbR (d+1))).mp
  change (b:ℝ)^(d+1) * (((a:ℝ)/b+ε)*P.derivative.eval ((a:ℝ)/b)) ≤
    (b:ℝ)^(d+1) * (((d+1:ℕ):ℝ)*P.eval ((a:ℝ)/b))
  calc
    _ = ((a:ℝ)+(b:ℝ)*ε) * ((b:ℝ)^d * P.derivative.eval ((a:ℝ)/b)) := by
      rw [pow_succ]
      field_simp [ne_of_gt hbR]
    _ = ((d+1:ℕ):ℝ) * (((a:ℝ)+(b:ℝ)*ε)*TH) := by rw [hderivative]; ring
    _ ≤ ((d+1:ℕ):ℝ) * ((b:ℝ)*TL+(a:ℝ)*TH) :=
      mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
    _ = _ := by rw [heq]; ring

theorem isAmple_of_lower_numerical_criterion [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = ((d+1:ℕ):WithBot ℕ∞))
    (hlower : LowerClosedNumericalCriterion p H d)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) : L.IsAmple := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  exact isAmple_of_lower_criterion_of_euler_slope_polynomial p r i hi H L hH d
    (by simpa only [Nat.cast_add, Nat.cast_one] using hdim.le) hlower ε hε hmargin
    (eulerSlopePolynomial p (d+1) L H)
    (fun a b hb => topEuler_slopeBundle_eq p H hH L (d+1) hdim.le a b hb)
    (eulerSlopePolynomial_pos_of_ample p H L hH (d+1) hdim)
    (eulerSlopePolynomial_derivative_margin p H L hH d hdim ε hmargin)

end
end PiExponent.NumericalAmpleness

end OAI
