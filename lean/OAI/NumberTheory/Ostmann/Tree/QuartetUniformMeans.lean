import OAI.NumberTheory.Ostmann.Tree.CorrelationSymmetry
import OAI.NumberTheory.Ostmann.Tree.QuartetFamilyPullback
import OAI.NumberTheory.Ostmann.Tree.SamePairMajorant
import OAI.NumberTheory.Ostmann.Tree.SquareMajorant

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators
open Ostmann.Tree.Quartet Ostmann.Tree.Quartet.NodeInput
variable {p : ℕ} [Fact p.Prime]

def treeError (g : ZMod p → ℂ) : ℝ :=
  (correlationBound g:ℝ)^2+Real.sqrt (3/(p:ℝ))

theorem treeError_nonneg (g : ZMod p → ℂ) : 0≤treeError g := by unfold treeError; positivity

theorem unitRatio_le_two : (p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ)≤2 := by
  have hp := (Fact.out : p.Prime).two_le
  have hcard : (Fintype.card (ZMod p)ˣ:ℝ)=(p:ℝ)-1 := by
    rw [ZMod.card_units,Nat.cast_sub (by omega),Nat.cast_one]
  rw [hcard]
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  apply (div_le_iff₀ (by linarith : 0<(p:ℝ)-1)).mpr
  linarith

theorem unitMean_const_mul (c : ℝ) (f : ZMod p → ℝ) :
    unitMean (fun y => c*f y)=c*unitMean f := by
  simp only [unitMean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem unitMean_neg (f : ZMod p → ℝ) : unitMean (fun y => f (-y))=unitMean f := by
  unfold unitMean
  congr 1
  simpa only [Equiv.neg_apply,Units.val_neg] using
    (Equiv.neg (ZMod p)ˣ).bijective.sum_comp (fun y : (ZMod p)ˣ => f y)

theorem l2Sq_signedFunction (g : ZMod p → ℂ) (c : Bool) : l2Sq (signedFunction g c)=l2Sq g := by
  cases c <;> simp [signedFunction,l2Sq]

theorem correlationBound_signedFunction (g : ZMod p → ℂ) (c : Bool) :
    correlationBound (signedFunction g c)=correlationBound g := by
  cases c
  · rfl
  · exact correlationBound_conj g

theorem orientation_sq (a : Bool) : ((orientation a : (ZMod p)ˣ):ZMod p)^2=1 := by
  cases a <;> simp [orientation]

def crossLocalMajorant (g : ZMod p → ℂ) (c d a b : Bool)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  8*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2*
    crossSquareMajorant (signedFunction g c) (signedFunction g d)
      (orientation a) (orientation b) (pairMode a) (pairMode b) ρ y

theorem crossLocalMajorant_nonneg (g : ZMod p → ℂ) (c d a b : Bool)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : 0≤crossLocalMajorant g c d a b ρ y :=
  mul_nonneg (by positivity) (crossSquareMajorant_nonneg _ _ _ _ _ _ _ _)

theorem crossLocalMajorant_mean_small (g : ZMod p → ℂ) (c d a b : Bool)
    (ρ : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    unitMean (crossLocalMajorant g c d a b ρ)≤25600*treeError g := by
  let C : ℝ := (p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ)
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hC2 : C≤2 := unitRatio_le_two
  have hc3 : C^3≤8 := by nlinarith [pow_le_pow_left₀ hC0 hC2 3]
  have hE := treeError_nonneg g
  have hs := crossSquareMajorant_mean_small (signedFunction g c) (signedFunction g d)
    (orientation a) (orientation b) (pairMode a) (pairMode b) ρ
    (orientation_sq a) (orientation_sq b) (signedFunction_zero g hg0 c)
    (by simpa only [l2Sq_signedFunction] using hg) (signedFunction_zero g hg0 d)
    (by simpa only [l2Sq_signedFunction] using hg)
  simp only [correlationBound_signedFunction] at hs
  unfold crossLocalMajorant
  rw [unitMean_const_mul]
  calc
    _ ≤ 8*C^2*(200*C*((correlationBound g:ℝ)^2+(correlationBound g:ℝ)^2+
        Real.sqrt (3/(p:ℝ)))) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ 3200*C^3*treeError g := by
      dsimp [treeError]
      nlinarith [mul_nonneg (pow_nonneg hC0 3) (Real.sqrt_nonneg (3/(p:ℝ)))]
    _ ≤ 25600*treeError g := by nlinarith [mul_le_mul_of_nonneg_right hc3 hE]

theorem crossLocalMajorant_mean_total (g : ZMod p → ℂ) (c d a b : Bool)
    (hg0 : g 0=0) (hg : l2Sq g≤1) :
    (∑ ρ : MulChar (ZMod p) ℂ,unitMean (crossLocalMajorant g c d a b ρ))≤128 := by
  classical
  let C : ℝ := (p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ)
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hC2 : C≤2 := unitRatio_le_two
  have hc4 : C^4≤16 := by nlinarith [pow_le_pow_left₀ hC0 hC2 4]
  have hs := crossSquareMajorant_mean_total (signedFunction g c) (signedFunction g d)
    (orientation a) (orientation b) (pairMode a) (pairMode b)
    (signedFunction_zero g hg0 c) (by simpa only [l2Sq_signedFunction] using hg)
    (signedFunction_zero g hg0 d) (by simpa only [l2Sq_signedFunction] using hg)
  unfold crossLocalMajorant
  simp_rw [unitMean_const_mul]
  rw [← Finset.mul_sum]
  calc
    _ ≤ 8*C^2*C^2 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ 128 := by nlinarith

end
end Ostmann.FiniteField

end OAI
