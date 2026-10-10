import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingPairBudget

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open InitialCharacterScale Filter

theorem exists_source_support_cost (k : ℕ) (β A : ℝ) (Z : ℕ) :
    ∃C : ℝ,0<C ∧ A≤C ∧ ∀L : ℝ,1≤L →
      (2^(k+1):ℝ)≤Real.exp (historyPolynomialCost C (depthScale k) 2 L) ∧
      (Z:ℝ)*((wordSize k L:ℝ)+1)≤Real.exp (historyPolynomialCost C (depthScale k) 2 L) ∧
      Real.exp ((β+1)*L)≤Real.exp (historyPolynomialCost C (depthScale k) 2 L) := by
  let C : ℝ := |A|+|β+1|+(Z:ℝ)+(2:ℝ)^(k+1)+1
  have hC : 0<C := by dsimp [C]; positivity
  have hA : A≤C := by dsimp [C]; linarith [le_abs_self A,abs_nonneg (β+1),Nat.cast_nonneg (α:=ℝ) Z,pow_nonneg (by norm_num : (0:ℝ)≤2) (k+1)]
  have hZ : (Z:ℝ)≤C := by dsimp [C]; linarith [abs_nonneg A,abs_nonneg (β+1),pow_nonneg (by norm_num : (0:ℝ)≤2) (k+1)]
  have htwo : (2:ℝ)^(k+1)≤C := by dsimp [C]; linarith [abs_nonneg A,abs_nonneg (β+1),Nat.cast_nonneg (α:=ℝ) Z]
  have hβ : |β+1|≤C := by dsimp [C]; linarith [abs_nonneg A,Nat.cast_nonneg (α:=ℝ) Z,pow_nonneg (by norm_num : (0:ℝ)≤2) (k+1)]
  refine ⟨C,hC,hA,?_⟩
  intro L hL
  have hL0 : 0≤L := by linarith
  have hm0 : 0≤(wordSize k L:ℝ) := Nat.cast_nonneg _
  have hm1 : 1≤(wordSize k L:ℝ)+1 := by linarith
  have hbase : L≤(wordSize k L:ℝ)+1 := by
    have hz := mul_le_mul_of_nonneg_right (one_le_depthScale k) hL0
    have hf := (wordSize_bounds k hL0).1
    nlinarith
  have hsq : (wordSize k L:ℝ)+1≤((wordSize k L:ℝ)+1)^2 := by nlinarith
  have he : historyPolynomialCost C (depthScale k) 2 L≤
      Real.exp (historyPolynomialCost C (depthScale k) 2 L) := by
    linarith [Real.add_one_le_exp (historyPolynomialCost C (depthScale k) 2 L)]
  have hcdef : historyPolynomialCost C (depthScale k) 2 L=C*((wordSize k L:ℝ)+1)^2 := by
    simp only [historyPolynomialCost,wordSize,add_comm]
  have hconst : C≤historyPolynomialCost C (depthScale k) 2 L := by
    rw [hcdef]
    nlinarith
  refine ⟨htwo.trans (hconst.trans he),?_,?_⟩
  · apply le_trans _ he
    rw [hcdef]
    exact (mul_le_mul_of_nonneg_right hZ (by positivity)).trans
      (mul_le_mul_of_nonneg_left hsq hC.le)
  · apply Real.exp_le_exp.mpr
    rw [hcdef]
    calc
      (β+1)*L≤|β+1| * L := mul_le_mul_of_nonneg_right (le_abs_self _) hL0
      _ ≤ C*((wordSize k L:ℝ)+1) := mul_le_mul hβ hbase hL0 hC.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq hC.le

theorem exists_source_support_error_cost (k : ℕ) (N : ℕ) :
    ∃K : ℝ,0<K ∧ ∀L α : ℝ,1≤L →
      (2*N:ℝ)*((wordSize k L:ℝ)+1)*Real.exp (-(1/4:ℝ)*Real.exp (α*L)) ≤
        Real.exp (K*L^2-(1/4:ℝ)*Real.exp (α*L)) := by
  let K : ℝ := 2*N*(depthScale k+1)+1
  have hK : 0<K := by
    have hz := depthScale_pos k
    dsimp [K]
    positivity
  refine ⟨K,hK,?_⟩
  intro L α hL
  have hL0 : 0≤L := by linarith
  have hm := (wordSize_bounds k hL0).2
  have hb : (wordSize k L:ℝ)+1≤(depthScale k+1)*L := by nlinarith
  have hlin : (2*N:ℝ)*((wordSize k L:ℝ)+1)≤K*L^2 := by
    have hmul := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ)≤2*N)
    have hsq : L≤L^2 := by nlinarith
    have hc : 2*(N:ℝ)*(depthScale k+1)≤K := by dsimp [K]; linarith
    exact (hmul.trans (by nlinarith)).trans (mul_le_mul_of_nonneg_left hsq hK.le)
  calc
    _ ≤ Real.exp (K*L^2)*Real.exp (-(1/4:ℝ)*Real.exp (α*L)) :=
      mul_le_mul_of_nonneg_right (hlin.trans (by linarith [Real.add_one_le_exp (K*L^2)])) (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

end Ostmann.Characters.DiagonalEstimate

end

end OAI
