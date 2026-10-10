import OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology
import OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial
import OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem isAmple_of_lower_criterion_of_euler_slope_polynomial [IsIntegral X]
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
    (hPample : ∀ a b : ℕ, 0 < b → (slopeBundle L H a b).IsAmple →
      0 < P.eval ((a:ℝ)/b))
    (hPderivative : ∀ a b : ℕ, 0 < b → (slopeBundle L H a b).IsAmple →
      ((a:ℝ)/b+ε) * P.derivative.eval ((a:ℝ)/b) ≤
        ((d+1:ℕ):ℝ) * P.eval ((a:ℝ)/b)) : L.IsAmple := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let t := ampleThreshold L H
  have ht : 0 ≤ t := ampleThreshold_nonneg L H hH
  have hrat (q : ℚ) (hq : t < (q:ℝ)) : ∃ a b : ℕ, 0 < b ∧
      (q:ℝ) = (a:ℝ)/b ∧ (slopeBundle L H a b).IsAmple := by
    have hqnonneg : (0:ℚ) ≤ q := by exact_mod_cast (ht.trans hq.le)
    obtain ⟨a,b,hb,hab⟩ := nonnegative_rat_nat_ratio q hqnonneg
    exact ⟨a,b,hb,hab,ample_of_threshold_lt L H hH a b hb (hab ▸ hq)⟩
  have hpositive : ∀ q : ℚ, t < (q:ℝ) → 0 < P.eval (q:ℝ) := by
    intro q hq
    obtain ⟨a,b,hb,hab,hamp⟩ := hrat q hq
    rw [hab]
    exact hPample a b hb hamp
  have hderivative : ∀ q : ℚ, t < (q:ℝ) →
      ((q:ℝ)+ε) * P.derivative.eval (q:ℝ) ≤ ((d+1:ℕ):ℝ)*P.eval (q:ℝ) := by
    intro q hq
    obtain ⟨a,b,hb,hab,hamp⟩ := hrat q hq
    rw [hab]
    exact hPderivative a b hb hamp
  have hPt : 0 < P.eval t :=
    polynomial_pos_at_boundary_of_rational_margin P (d+1) t ε ht hε hpositive hderivative
  by_cases htzero : t = 0
  · have hpzero : 0 < P.eval ((0:ℝ)/1) := by simpa only [htzero,zero_div] using hPt
    exact (slope_zero_isAmple_iff L H 1 (by decide)).mp
      (ample_slope_of_polynomial_pos_of_lower_criterion p r i hi H L hH d hdim hlower ε hε
        hmargin P hP 0 1 (by decide) (by simpa using hpzero))
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
    obtain ⟨q,hq0,hqt,hPq⟩ := exists_positive_rational_below_of_polynomial_pos P t htpos hPt
    have hqnonneg : (0:ℚ) ≤ q := by exact_mod_cast hq0.le
    obtain ⟨a,b,hb,hab⟩ := nonnegative_rat_nat_ratio q hqnonneg
    have ha : 0 < a := by
      have hnum : (0:ℝ) < a :=
        (div_pos_iff_of_pos_right (by exact_mod_cast hb : (0:ℝ)<b)).mp (hab ▸ hq0)
      exact_mod_cast hnum
    have hamp := ample_slope_of_polynomial_pos_of_lower_criterion p r i hi H L hH d hdim
      hlower ε hε hmargin P hP a b hb (hab ▸ hPq)
    have habove := threshold_lt_of_ample L H a b ha hb hamp
    have hbelow : (a:ℝ)/b < ampleThreshold L H := hab ▸ hqt
    exact False.elim (lt_asymm habove hbelow)

end
end PiExponent.NumericalAmpleness

end OAI
