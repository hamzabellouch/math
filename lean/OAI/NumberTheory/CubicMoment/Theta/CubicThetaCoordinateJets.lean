import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateAxis
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKernelSecondBounds

namespace OAI

/-! Common relative bounds for the first and second coordinate jets.
They are preserved by scalar multiplication and horizontal translation. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaAxisFunction (F : ℝ → ℝ → ℝ → ℂ) (k : CubicThetaAxis)
    (x y v : ℝ) : ℝ → ℂ :=
  match k with
  | .x => fun t => F t y v
  | .y => fun t => F x t v
  | .height => fun t => F x y t

def cubicThetaFirstJetConstant (s : ℂ) : ℝ := 3*‖s‖

def cubicThetaSecondJetConstant (s : ℂ) : ℝ :=
  2*‖s‖+‖s*(s-1)‖+‖4*s^2+2*s‖+4*‖s‖*‖s+1‖

def CubicThetaCoordinateJetBound (F : ℝ → ℝ → ℝ → ℂ) (s : ℂ) (x y v : ℝ) : Prop :=
  ∀ k : CubicThetaAxis,
    ‖deriv (cubicThetaAxisFunction F k x y v) (cubicThetaCoordinateCenter k x y v)‖ ≤
      ‖F x y v‖*(cubicThetaFirstJetConstant s/v) ∧
    ‖deriv (deriv (cubicThetaAxisFunction F k x y v)) (cubicThetaCoordinateCenter k x y v)‖ ≤
      ‖F x y v‖*(cubicThetaSecondJetConstant s/v^2)

lemma cubicThetaJetConstants_nonneg (s : ℂ) :
    0 ≤ cubicThetaFirstJetConstant s ∧ 0 ≤ cubicThetaSecondJetConstant s := by
  unfold cubicThetaFirstJetConstant cubicThetaSecondJetConstant
  constructor <;> positivity

lemma cubicThetaCartesian_jetBound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    CubicThetaCoordinateJetBound (cubicThetaCartesianKernel s) s x y v := by
  have h1 : 2*‖s‖/v ≤ cubicThetaFirstJetConstant s/v := by
    apply div_le_div_of_nonneg_right _ hv.le
    unfold cubicThetaFirstJetConstant
    linarith [_root_.norm_nonneg s]
  have h2 : (2*‖s‖+4*‖s‖*‖s+1‖)/v^2 ≤ cubicThetaSecondJetConstant s/v^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg v)
    unfold cubicThetaSecondJetConstant
    linarith [_root_.norm_nonneg (s*(s-1)),_root_.norm_nonneg (4*s^2+2*s)]
  have h3 : (‖s*(s-1)‖+‖4*s^2+2*s‖+4*‖s‖*‖s+1‖)/v^2 ≤
      cubicThetaSecondJetConstant s/v^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg v)
    unfold cubicThetaSecondJetConstant
    linarith [_root_.norm_nonneg s]
  intro k
  cases k with
  | x => exact ⟨(cubicThetaCartesian_x_deriv_bound s x y hv).trans
        (mul_le_mul_of_nonneg_left h1 (_root_.norm_nonneg _)),
      (cubicThetaCartesian_x_second_bound s x y hv).trans
        (mul_le_mul_of_nonneg_left h2 (_root_.norm_nonneg _))⟩
  | y => exact ⟨(cubicThetaCartesian_y_deriv_bound s x y hv).trans
        (mul_le_mul_of_nonneg_left h1 (_root_.norm_nonneg _)),
      (cubicThetaCartesian_y_second_bound s x y hv).trans
        (mul_le_mul_of_nonneg_left h2 (_root_.norm_nonneg _))⟩
  | height => exact ⟨cubicThetaCartesian_v_deriv_bound s x y hv,
      (cubicThetaCartesian_v_second_bound s x y hv).trans
        (mul_le_mul_of_nonneg_left h3 (_root_.norm_nonneg _))⟩

lemma cubicThetaCoordinateJetBound_congr {F G : ℝ → ℝ → ℝ → ℂ}
    (hFG : ∀ x y v, 0<v → F x y v=G x y v) {s : ℂ} {x y v : ℝ} (hv : 0<v)
    (hG : CubicThetaCoordinateJetBound G s x y v) : CubicThetaCoordinateJetBound F s x y v := by
  intro k
  have he : cubicThetaAxisFunction F k x y v =ᶠ[𝓝 (cubicThetaCoordinateCenter k x y v)]
      cubicThetaAxisFunction G k x y v := by
    cases k with
    | x => exact Eventually.of_forall (fun t => hFG t y v hv)
    | y => exact Eventually.of_forall (fun t => hFG x t v hv)
    | height =>
      filter_upwards [eventually_gt_nhds hv] with t ht
      exact hFG x y t ht
  rw [he.deriv_eq,he.deriv.deriv_eq,hFG x y v hv]
  exact hG k

lemma cubicThetaCoordinateJetBound_translate {F : ℝ → ℝ → ℝ → ℂ} {s : ℂ}
    (C : ℂ) (a b x y v : ℝ) (hF : CubicThetaCoordinateJetBound F s (x+a) (y+b) v) :
    CubicThetaCoordinateJetBound (fun u w t => C*F (u+a) (w+b) t) s x y v := by
  intro k
  have hm (f : ℝ → ℂ) (t : ℝ) (h : ℝ) :
      ‖deriv (fun z => C*f (z+h)) t‖=‖C‖*‖deriv f (t+h)‖ ∧
      ‖deriv (deriv (fun z => C*f (z+h))) t‖=‖C‖*‖deriv (deriv f) (t+h)‖ := by
    simp [deriv_const_mul_field',cubicTheta_deriv_translate]
  have hmul (A B : ℝ) (h : A ≤ ‖F (x+a) (y+b) v‖*B) :
      ‖C‖*A ≤ ‖C*F (x+a) (y+b) v‖*B := by
    rw [norm_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left h (_root_.norm_nonneg _)
  cases k with
  | x =>
    have he := hm (fun t => F t (y+b) v) x a
    exact ⟨he.1.trans_le (hmul _ _ (hF .x).1),he.2.trans_le (hmul _ _ (hF .x).2)⟩
  | y =>
    have he := hm (fun t => F (x+a) t v) y b
    exact ⟨he.1.trans_le (hmul _ _ (hF .y).1),he.2.trans_le (hmul _ _ (hF .y).2)⟩
  | height =>
    have he := hm (fun t => F (x+a) (y+b) t) v 0
    simp only [add_zero] at he
    exact And.intro (he.1.trans_le (hmul _ _ (hF .height).1))
        (he.2.trans_le (hmul _ _ (hF .height).2))

end CubicFirstMoment

end

end OAI
