import OAI.NumberTheory.Ostmann.Tree.QuartetUniformMeans

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators
open Ostmann.Tree.Quartet Ostmann.Tree.Quartet.NodeInput
variable {p : ℕ} [Fact p.Prime]

def sameLocalMajorant (g : ZMod p → ℂ) (c d neg : Bool)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  8*samePairMajorant (signedFunction g c) (signedFunction g d) 1 1 ρ⁻¹
    (if neg then -y else y)

def untouchedLocalMajorant (g : ZMod p → ℂ) (c d : Bool) (y : ZMod p) : ℝ :=
  8*untouchedMajorant (signedFunction g c) (signedFunction g d) 1 1 y

theorem sameLocalMajorant_nonneg (g : ZMod p → ℂ) (c d neg : Bool)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : 0 ≤ sameLocalMajorant g c d neg ρ y :=
  mul_nonneg (by positivity) (samePairMajorant_nonneg _ _ _ _ _ _)

theorem untouchedLocalMajorant_nonneg (g : ZMod p → ℂ) (c d : Bool)
    (y : ZMod p) : 0≤untouchedLocalMajorant g c d y :=
  mul_nonneg (by positivity) (untouchedMajorant_nonneg _ _ _ _ _)

theorem sameLocalMajorant_mean_eq (g : ZMod p → ℂ) (c d neg : Bool)
    (ρ : MulChar (ZMod p) ℂ) :
    unitMean (sameLocalMajorant g c d neg ρ)=
      8*unitMean (samePairMajorant (signedFunction g c) (signedFunction g d) 1 1 ρ⁻¹) := by
  unfold sameLocalMajorant
  rw [unitMean_const_mul]
  cases neg
  · rfl
  · simp only [ite_true]
    rw [unitMean_neg]

theorem sameLocalMajorant_mean_small (g : ZMod p → ℂ) (c d neg : Bool)
    (ρ : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    unitMean (sameLocalMajorant g c d neg ρ)≤512*treeError g := by
  let C : ℝ := (p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ)
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hC2 : C≤2 := unitRatio_le_two
  have hc5 : C^5≤32 := by nlinarith [pow_le_pow_left₀ hC0 hC2 5]
  have hs := samePairMajorant_mean_small (signedFunction g c) (signedFunction g d)
    1 1 ρ⁻¹ (signedFunction_zero g hg0 c) (by simpa only [l2Sq_signedFunction] using hg)
    (signedFunction_zero g hg0 d) (by simpa only [l2Sq_signedFunction] using hg)
  simp only [correlationBound_signedFunction] at hs
  rw [sameLocalMajorant_mean_eq]
  calc
    _ ≤ 8*(2*C^5*(correlationBound g:ℝ)^2) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ 512*(correlationBound g:ℝ)^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hc5 (sq_nonneg (correlationBound g:ℝ))]
    _ ≤ 512*treeError g := by unfold treeError; nlinarith [Real.sqrt_nonneg (3/(p:ℝ))]

theorem sameLocalMajorant_mean_total (g : ZMod p → ℂ) (c d neg : Bool)
    (hg0 : g 0=0) (hg : l2Sq g≤1) :
    (∑ ρ : MulChar (ZMod p) ℂ,unitMean (sameLocalMajorant g c d neg ρ))≤256 := by
  classical
  let C : ℝ := (p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ)
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hC2 : C≤2 := unitRatio_le_two
  have hc4 : C^4≤16 := by nlinarith [pow_le_pow_left₀ hC0 hC2 4]
  have hs := samePairMajorant_mean_total (signedFunction g c) (signedFunction g d)
    1 1 (signedFunction_zero g hg0 c) (by simpa only [l2Sq_signedFunction] using hg)
    (signedFunction_zero g hg0 d) (by simpa only [l2Sq_signedFunction] using hg)
  simp_rw [sameLocalMajorant_mean_eq]
  rw [← Finset.mul_sum]
  have he := (Equiv.inv (MulChar (ZMod p) ℂ)).bijective.sum_comp
    (fun ρ => unitMean (samePairMajorant (signedFunction g c) (signedFunction g d) 1 1 ρ))
  simp only [Equiv.inv_apply] at he
  rw [he]
  calc
    _ ≤ 8*(2*C^4) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ 256 := by nlinarith

theorem untouchedLocalMajorant_mean (g : ZMod p → ℂ) (c d : Bool)
    (hg0 : g 0=0) (hg : l2Sq g≤1) : unitMean (untouchedLocalMajorant g c d)≤128 := by
  let C : ℝ := (p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ)
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hC2 : C≤2 := unitRatio_le_two
  have hc4 : C^4≤16 := by nlinarith [pow_le_pow_left₀ hC0 hC2 4]
  have hs := untouchedMajorant_mean (signedFunction g c) (signedFunction g d)
    1 1 (signedFunction_zero g hg0 c) (by simpa only [l2Sq_signedFunction] using hg)
    (signedFunction_zero g hg0 d) (by simpa only [l2Sq_signedFunction] using hg)
  unfold untouchedLocalMajorant
  rw [unitMean_const_mul]
  calc
    _ ≤ 8*C^4 := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ 128 := by nlinarith

end
end Ostmann.FiniteField

end OAI
