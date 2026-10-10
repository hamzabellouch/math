import OAI.Probability.InvariantIsing.Fields.FieldAffineRecursion
import OAI.Probability.InvariantIsing.Fields.FieldSpinLinear

namespace OAI

/-! Compensation of the covariance derivative by the spatial generator.
The identity telescopes adjacent covariance increments; it uses the actual
Gaussian transition and does not require exchanging mixed derivatives. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma field_gaussianTiltAverage_const (s ζ : ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (c z : ℝ) :
    gaussianTiltAverage s ζ F (fun _ => c) z = c := by
  rw [field_gaussianTiltAverage_eq_transition s ζ hF measurable_const]
  exact fieldSpinTransition_const ζ (Real.toNNReal s) hF hg c z

lemma field_gaussianTiltAverage_const_mul (s ζ : ℝ) {F a : ℝ → ℝ}
    (hF : Measurable F) (ha : Measurable a) (c z : ℝ) :
    gaussianTiltAverage s ζ F (fun y => c * a y) z =
      c * gaussianTiltAverage s ζ F a z := by
  rw [field_gaussianTiltAverage_eq_transition s ζ hF (ha.const_mul c),
    field_gaussianTiltAverage_eq_transition s ζ hF ha]
  exact fieldSpinTransition_const_mul ζ (Real.toNNReal s) F a c z

lemma field_gaussianTiltAverage_add (s ζ : ℝ) {F a b : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (ha : Measurable a) (hb : Measurable b)
    {A B : ℝ} (haB : ∀ y, |a y| ≤ A) (hbB : ∀ y, |b y| ≤ B) (z : ℝ) :
    gaussianTiltAverage s ζ F (fun y => a y + b y) z =
      gaussianTiltAverage s ζ F a z + gaussianTiltAverage s ζ F b z := by
  have hm : Measurable (fun y => a y + b y) := ha.add hb
  rw [field_gaussianTiltAverage_eq_transition s ζ hF hm,
    field_gaussianTiltAverage_eq_transition s ζ hF ha,
    field_gaussianTiltAverage_eq_transition s ζ hF hb]
  exact fieldSpinTransition_add ζ (Real.toNNReal s) hF hg ha hb haB hbB z

namespace FieldSmoothFamily

theorem compensated_tangent {I : Set ℝ} (F : FieldSmoothFamily I)
    (a d dprev ζ η : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    F.tangent a (d - dprev) ζ p + dprev / 2 *
        (F.curvature a (d - dprev) ζ p + ζ * (F.mean a (d - dprev) ζ p) ^ 2) =
      gaussianTiltAverage (a + (d - dprev) * p.1) ζ (fun y => F.U (p.1, y))
        (fun y => F.T (p.1, y) + d / 2 * (F.XX (p.1, y) + η * (F.X (p.1, y)) ^ 2)) p.2 -
      d / 2 * (η - ζ) *
        gaussianTiltAverage (a + (d - dprev) * p.1) ζ (fun y => F.U (p.1, y))
          (fun y => (F.X (p.1, y)) ^ 2) p.2 := by
  let s := a + (d - dprev) * p.1
  have hU : Measurable (fun y => F.U (p.1, y)) := F.mU.comp (by fun_prop)
  have hT : Measurable (fun y => F.T (p.1, y)) := F.mT.comp (by fun_prop)
  have hXX : Measurable (fun y => F.XX (p.1, y)) := F.mXX.comp (by fun_prop)
  have hXsq : Measurable (fun y => (F.X (p.1, y)) ^ 2) :=
    (F.mX.comp (by fun_prop)).pow_const 2
  have hsq : ∀ y, |(F.X (p.1, y)) ^ 2| ≤ F.KX ^ 2 := fun y => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (F.bX (p.1, y)) 2
  have hm (r : ℝ) : Measurable (fun y => F.XX (p.1, y) + r * (F.X (p.1, y)) ^ 2) :=
    hXX.add (hXsq.const_mul r)
  have hb (r : ℝ) : ∀ y, |F.XX (p.1, y) + r * (F.X (p.1, y)) ^ 2| ≤
      F.KXX + |r| * F.KX ^ 2 :=
    bounded_generator (fun y => F.bX (p.1, y)) (fun y => F.bXX (p.1, y)) r
  have hexpand (r : ℝ) :
      gaussianTiltAverage s ζ (fun y => F.U (p.1, y))
          (fun y => F.XX (p.1, y) + r * (F.X (p.1, y)) ^ 2) p.2 =
        gaussianTiltAverage s ζ (fun y => F.U (p.1, y)) (fun y => F.XX (p.1, y)) p.2 +
          r * gaussianTiltAverage s ζ (fun y => F.U (p.1, y))
            (fun y => (F.X (p.1, y)) ^ 2) p.2 := by
    rw [field_gaussianTiltAverage_add s ζ hU (F.growth p.1) hXX (hXsq.const_mul r)
      (fun y => F.bXX (p.1, y)) (fun y => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hsq y) (abs_nonneg r)),
      field_gaussianTiltAverage_const_mul s ζ hU hXsq]
  have hfull :
      gaussianTiltAverage s ζ (fun y => F.U (p.1, y))
        (fun y => F.T (p.1, y) + d / 2 * (F.XX (p.1, y) + η * (F.X (p.1, y)) ^ 2)) p.2 =
      gaussianTiltAverage s ζ (fun y => F.U (p.1, y)) (fun y => F.T (p.1, y)) p.2 +
        d / 2 * gaussianTiltAverage s ζ (fun y => F.U (p.1, y))
          (fun y => F.XX (p.1, y) + η * (F.X (p.1, y)) ^ 2) p.2 := by
    rw [field_gaussianTiltAverage_add s ζ hU (F.growth p.1) hT ((hm η).const_mul (d / 2))
      (fun y => F.bT (p.1, y) hp) (fun y => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hb η y) (abs_nonneg (d / 2))),
      field_gaussianTiltAverage_const_mul s ζ hU (hm η)]
  change F.tangent a (d - dprev) ζ p + dprev / 2 *
      (F.curvature a (d - dprev) ζ p + ζ * (F.mean a (d - dprev) ζ p) ^ 2) = _
  rw [hfull, hexpand η]
  unfold tangent curvature
  rw [show a + (d - dprev) * p.1 = s from rfl, hexpand ζ]
  ring

end FieldSmoothFamily
end InvariantIsing

end

end OAI
