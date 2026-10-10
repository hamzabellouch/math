import OAI.NumberTheory.Ostmann.Tree.QuartetBlockMoments

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.FiniteField
open Ostmann.Tree.Density Ostmann.Tree.Quartet
variable {p : ℕ} [Fact p.Prime]

theorem pairSquareEnergy_zero (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) : pairSquareEnergy g σ ρ 0=0 := by
  classical
  simp [pairSquareEnergy, deletedPairEnergy]

theorem block_difference_mean (A B : ZMod p → ℝ) (y K : (ZMod p)ˣ)
    (hA : ∀ d,0≤A d) (hB : ∀ d,0≤B d) (hA0 : A 0=0) (hB0 : B 0=0) :
    average (fun t : (ZMod p)ˣ => A (pairMobiusValue y (K/t^2 : (ZMod p)ˣ))*
      B (pairMobiusValue y (K/t^2 : (ZMod p)ˣ)-(y:ZMod p))) ≤
      2*nonnegativeDifference A B y := by
  exact mobius_inverse_square_mean y K (fun d => A d*B (d-(y:ZMod p)))
    (fun d => mul_nonneg (hA d) (hB _)) (by simp only [hA0,zero_mul])
    (by simp only [sub_self,hB0,mul_zero])

theorem nonnegativeDifference_swap (A B : ZMod p → ℝ) (y : ZMod p) :
    nonnegativeDifference A B y = nonnegativeDifference B A (-y) := by
  unfold nonnegativeDifference
  congr 1
  have he := (Equiv.subRight y).bijective.sum_comp (fun e : ZMod p => B e*A (e+y))
  change (∑ d : ZMod p,B (d-y)*A ((d-y)+y)) = _ at he
  simpa only [sub_add_cancel,sub_neg_eq_add,mul_comm] using he

theorem twoPair_same_left_root (g h : ZMod p → ℂ) (σ τ K L y R : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hh0 : h 0=0) :
    average (fun B : (ZMod p)ˣ => average (fun x : (ZMod p)ˣ => average (fun w : (ZMod p)ˣ =>
      ‖mellin (fun z : (ZMod p)ˣ =>
        heldPairValue g σ K (pairMobiusValue y (R/B^2 : (ZMod p)ˣ)) (x/z)*
        heldPairValue h τ L (pairMobiusValue y (R/B^2 : (ZMod p)ˣ)-(y:ZMod p)) w) ρ‖^2))) ≤
      8*samePairMajorant g h σ τ ρ⁻¹ y := by
  calc
    _ ≤ average (fun B : (ZMod p)ˣ => 4*(pairSquareEnergy g σ ρ⁻¹
        (pairMobiusValue y (R/B^2 : (ZMod p)ˣ))*pairSecondMoment h τ
        (pairMobiusValue y (R/B^2 : (ZMod p)ˣ)-(y:ZMod p)))) := by
      apply average_mono
      intro B
      simpa only [mul_assoc] using twoPair_same_left_mean g h σ τ K L
        (pairMobiusValue y (R/B^2 : (ZMod p)ˣ))
        (pairMobiusValue y (R/B^2 : (ZMod p)ˣ)-(y:ZMod p)) ρ hg0 hh0
    _ ≤ 4*(2*samePairMajorant g h σ τ ρ⁻¹ y) := by
      rw [average_const_mul]
      exact mul_le_mul_of_nonneg_left
        (block_difference_mean _ _ y R (pairSquareEnergy_nonneg _ _ _)
          (pairSecondMoment_nonneg _ _) (pairSquareEnergy_zero _ _ _)
          (pairSecondMoment_zero _ _ hh0)) (by norm_num)
    _ = _ := by ring

theorem twoPair_same_right_root (g h : ZMod p → ℂ) (σ τ K L y R : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hh0 : h 0=0) :
    average (fun B : (ZMod p)ˣ => average (fun x : (ZMod p)ˣ => average (fun w : (ZMod p)ˣ =>
      ‖mellin (fun z : (ZMod p)ˣ =>
        heldPairValue g σ K (pairMobiusValue y (R/B^2 : (ZMod p)ˣ)) x*
        heldPairValue h τ L (pairMobiusValue y (R/B^2 : (ZMod p)ˣ)-(y:ZMod p)) (w/z)) ρ‖^2))) ≤
      8*samePairMajorant h g τ σ ρ⁻¹ (-(y:ZMod p)) := by
  calc
    _ ≤ average (fun B : (ZMod p)ˣ => 4*(pairSecondMoment g σ
        (pairMobiusValue y (R/B^2 : (ZMod p)ˣ))*pairSquareEnergy h τ ρ⁻¹
        (pairMobiusValue y (R/B^2 : (ZMod p)ˣ)-(y:ZMod p)))) := by
      apply average_mono
      intro B
      simpa only [mul_assoc,mul_comm,mul_left_comm] using twoPair_same_right_mean g h σ τ K L
        (pairMobiusValue y (R/B^2 : (ZMod p)ˣ))
        (pairMobiusValue y (R/B^2 : (ZMod p)ˣ)-(y:ZMod p)) ρ hg0 hh0
    _ ≤ 4*(2*nonnegativeDifference (pairSecondMoment g σ) (pairSquareEnergy h τ ρ⁻¹) y) := by
      rw [average_const_mul]
      exact mul_le_mul_of_nonneg_left
        (block_difference_mean _ _ y R (pairSecondMoment_nonneg _ _)
          (pairSquareEnergy_nonneg _ _ _) (pairSecondMoment_zero _ _ hg0)
          (pairSquareEnergy_zero _ _ _)) (by norm_num)
    _ = _ := by rw [nonnegativeDifference_swap]; unfold samePairMajorant; ring

theorem twoPair_untouched_root (g h : ZMod p → ℂ) (σ τ K L y R : (ZMod p)ˣ)
    (hg0 : g 0=0) (hh0 : h 0=0) :
    average (fun B : (ZMod p)ˣ => average (fun x : (ZMod p)ˣ => average (fun w : (ZMod p)ˣ =>
      ‖heldPairValue g σ K (pairMobiusValue y (R/B^2 : (ZMod p)ˣ)) x*
        heldPairValue h τ L (pairMobiusValue y (R/B^2 : (ZMod p)ˣ)-(y:ZMod p)) w‖^2))) ≤
      8*untouchedMajorant g h σ τ y := by
  calc
    _ ≤ average (fun B : (ZMod p)ˣ => 4*(pairSecondMoment g σ
        (pairMobiusValue y (R/B^2 : (ZMod p)ˣ))*pairSecondMoment h τ
        (pairMobiusValue y (R/B^2 : (ZMod p)ˣ)-(y:ZMod p)))) := by
      apply average_mono
      intro B
      simpa only [mul_assoc] using twoPair_untouched_mean g h σ τ K L
        (pairMobiusValue y (R/B^2 : (ZMod p)ˣ))
        (pairMobiusValue y (R/B^2 : (ZMod p)ˣ)-(y:ZMod p)) hg0 hh0
    _ ≤ 4*(2*untouchedMajorant g h σ τ y) := by
      rw [average_const_mul]
      exact mul_le_mul_of_nonneg_left
        (block_difference_mean _ _ y R (pairSecondMoment_nonneg _ _)
          (pairSecondMoment_nonneg _ _) (pairSecondMoment_zero _ _ hg0)
          (pairSecondMoment_zero _ _ hh0)) (by norm_num)
    _ = _ := by ring

end Ostmann.FiniteField
end

end OAI
