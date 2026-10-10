import OAI.NumberTheory.Ostmann.Tree.QuartetCrossBound
import OAI.NumberTheory.Ostmann.Tree.QuartetPairMeasure

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Tree.Quartet
open Density

theorem real_average_comm {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → ℝ) :
    average (fun a => average (f a)) = average (fun b => average (fun a => f a b)) := by
  unfold average
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

end Ostmann.Tree.Quartet
namespace Ostmann.FiniteField
open Ostmann.Tree.Density Ostmann.Tree.Quartet
variable {p : ℕ} [Fact p.Prime]

def heldPairValue (g : ZMod p → ℂ) (σ K : (ZMod p)ˣ) (d : ZMod p) (h : (ZMod p)ˣ) : ℂ :=
  pairTest g σ d (((K*h^2:(ZMod p)ˣ):ZMod p)*d)

theorem heldPair_moving_bound (g : ZMod p → ℂ) (σ K h : (ZMod p)ˣ)
    (d : ZMod p) (ρ : MulChar (ZMod p) ℂ) (hg0 : g 0=0) :
    ‖mellin (fun z : (ZMod p)ˣ => heldPairValue g σ K d (h/z)) ρ‖^2 ≤
      2*pairSquareEnergy g σ ρ⁻¹ d := by
  have he (z : (ZMod p)ˣ) : K*(h/z)^2 = (K*h^2)/z^2 := by rw [div_pow, mul_div_assoc]
  simpa only [heldPairValue, he] using pairTest_inverse_square_bound g σ (K*h^2) d ρ hg0

theorem mellin_mul_const_norm_sq (f : (ZMod p)ˣ → ℂ) (c : ℂ) (ρ : MulChar (ZMod p) ℂ) :
    ‖mellin (fun z => f z*c) ρ‖^2 = ‖mellin f ρ‖^2*‖c‖^2 := by
  have he : (fun z => f z*c) = fun z => c*f z := by funext z; ring
  rw [he, mellin_const_mul, norm_mul, mul_pow, mul_comm]

theorem twoPair_same_left_mean (g h : ZMod p → ℂ) (σ τ K L : (ZMod p)ˣ)
    (d e : ZMod p) (ρ : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hh0 : h 0=0) :
    average (fun x : (ZMod p)ˣ => average (fun y : (ZMod p)ˣ =>
      ‖mellin (fun z : (ZMod p)ˣ => heldPairValue g σ K d (x/z)*heldPairValue h τ L e y) ρ‖^2)) ≤
      4*pairSquareEnergy g σ ρ⁻¹ d*pairSecondMoment h τ e := by
  calc
    _ ≤ average (fun _x : (ZMod p)ˣ => average (fun y : (ZMod p)ˣ =>
        (2*pairSquareEnergy g σ ρ⁻¹ d)*‖heldPairValue h τ L e y‖^2)) := by
      apply average_mono
      intro x
      apply average_mono
      intro y
      rw [mellin_mul_const_norm_sq]
      exact mul_le_mul_of_nonneg_right (heldPair_moving_bound g σ K x d ρ hg0) (sq_nonneg _)
    _ = (2*pairSquareEnergy g σ ρ⁻¹ d)*average (fun y : (ZMod p)ˣ => ‖heldPairValue h τ L e y‖^2) := by
      simp_rw [average_const_mul, real_average_const]
    _ ≤ (2*pairSquareEnergy g σ ρ⁻¹ d)*(2*pairSecondMoment h τ e) := by
      exact mul_le_mul_of_nonneg_left (pairTest_square_mean h τ L e hh0)
        (mul_nonneg (by norm_num) (pairSquareEnergy_nonneg _ _ _ _))
    _ = _ := by ring

theorem twoPair_same_right_mean (g h : ZMod p → ℂ) (σ τ K L : (ZMod p)ˣ)
    (d e : ZMod p) (ρ : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hh0 : h 0=0) :
    average (fun x : (ZMod p)ˣ => average (fun y : (ZMod p)ˣ =>
      ‖mellin (fun z : (ZMod p)ˣ => heldPairValue g σ K d x*heldPairValue h τ L e (y/z)) ρ‖^2)) ≤
      4*pairSquareEnergy h τ ρ⁻¹ e*pairSecondMoment g σ d := by
  rw [real_average_comm]
  have he (x y z : (ZMod p)ˣ) :
      heldPairValue g σ K d x*heldPairValue h τ L e (y/z) =
      heldPairValue h τ L e (y/z)*heldPairValue g σ K d x := mul_comm _ _
  simp_rw [he]
  exact twoPair_same_left_mean h g τ σ L K e d ρ hh0 hg0

theorem twoPair_untouched_mean (g h : ZMod p → ℂ) (σ τ K L : (ZMod p)ˣ)
    (d e : ZMod p) (hg0 : g 0=0) (hh0 : h 0=0) :
    average (fun x : (ZMod p)ˣ => average (fun y : (ZMod p)ˣ =>
      ‖heldPairValue g σ K d x*heldPairValue h τ L e y‖^2)) ≤
      4*pairSecondMoment g σ d*pairSecondMoment h τ e := by
  simp only [norm_mul, mul_pow]
  simp_rw [average_const_mul]
  have he : (fun x : (ZMod p)ˣ => ‖heldPairValue g σ K d x‖^2*
      average (fun y : (ZMod p)ˣ => ‖heldPairValue h τ L e y‖^2)) =
      fun x => average (fun y : (ZMod p)ˣ => ‖heldPairValue h τ L e y‖^2)*‖heldPairValue g σ K d x‖^2 := by
    funext x
    ring
  rw [he, average_const_mul]
  calc
    _ ≤ (2*pairSecondMoment h τ e)*(2*pairSecondMoment g σ d) :=
      mul_le_mul (pairTest_square_mean h τ L e hh0) (pairTest_square_mean g σ K d hg0)
        (average_nonneg _ (fun _ => sq_nonneg _))
        (mul_nonneg (by norm_num) (pairSecondMoment_nonneg _ _ _))
    _ = _ := by ring

end Ostmann.FiniteField
end

end OAI
