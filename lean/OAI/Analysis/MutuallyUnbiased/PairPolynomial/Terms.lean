import OAI.Analysis.MutuallyUnbiased.PairTargets.Data
import OAI.Analysis.MutuallyUnbiased.PairMoments.PairCharges

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

def termPolynomial (H : CMatrix) (t : Term) : ℂ :=
  (t.coefficient : ℂ) * ∏ j, g H (fun i => t.charges i j)

private theorem charge0_0 :
    (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (0 : Fin 2)) = pairW := by decide +kernel

private theorem charge0_1 :
    (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (1 : Fin 2)) = -pairW := by decide +kernel

theorem termPolynomial0 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term0 = (3 : ℂ) * ((g H pairW) * (conj (g H pairW))) := by
  have hc : (term0.coefficient : ℂ) = (3 : ℂ) := by norm_num [term0]
  change (term0.coefficient : ℂ) * (∏ j : Fin 2, g H (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (0 : Fin 2)) * (g H (fun i => (term0.charges : Matrix Coord (Fin 2) ℤ) i (1 : Fin 2)) * 1)) = _
  rw [charge0_0, charge0_1]
  simp only [g_neg hH]
  ring

private theorem charge1_0 :
    (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge1_1 :
    (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 0) := by decide +kernel

private theorem charge1_2 :
    (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial1 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term1 = (-6 : ℂ) * ((g H pairW) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term1.coefficient : ℂ) = (-6 : ℂ) := by norm_num [term1]
  change (term1.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-6 : ℂ) * (g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term1.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge1_0, charge1_1, charge1_2]
  simp only [g_neg hH]
  ring

private theorem charge2_0 :
    (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge2_1 :
    (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 1) := by decide +kernel

private theorem charge2_2 :
    (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial2 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term2 = (-3 : ℂ) * ((g H pairW) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term2.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term2]
  change (term2.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term2.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge2_0, charge2_1, charge2_2]
  simp only [g_neg hH]
  ring

private theorem charge3_0 :
    (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge3_1 :
    (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 2) := by decide +kernel

private theorem charge3_2 :
    (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial3 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term3 = (-3 : ℂ) * ((g H pairW) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term3.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term3]
  change (term3.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term3.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge3_0, charge3_1, charge3_2]
  simp only [g_neg hH]
  ring

private theorem charge4_0 :
    (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = pairW := by decide +kernel

private theorem charge4_1 :
    (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = -(pairA 3) := by decide +kernel

private theorem charge4_2 :
    (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial4 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term4 = (-3 : ℂ) * ((g H pairW) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term4.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term4]
  change (term4.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term4.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge4_0, charge4_1, charge4_2]
  simp only [g_neg hH]
  ring

private theorem charge5_0 :
    (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 0) := by decide +kernel

private theorem charge5_1 :
    (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 0) := by decide +kernel

private theorem charge5_2 :
    (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial5 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term5 = (-6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H pairW))) := by
  have hc : (term5.coefficient : ℂ) = (-6 : ℂ) := by norm_num [term5]
  change (term5.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-6 : ℂ) * (g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term5.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge5_0, charge5_1, charge5_2]
  simp only [g_neg hH]
  ring

private theorem charge6_0 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge6_1 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge6_2 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge6_3 :
    (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial6 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term6 = (12 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term6.coefficient : ℂ) = (12 : ℂ) := by norm_num [term6]
  change (term6.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (12 : ℂ) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term6.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge6_0, charge6_1, charge6_2, charge6_3]
  simp only [g_neg hH]
  ring

private theorem charge7_0 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge7_1 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge7_2 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge7_3 :
    (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial7 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term7 = (6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term7.coefficient : ℂ) = (6 : ℂ) := by norm_num [term7]
  change (term7.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term7.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge7_0, charge7_1, charge7_2, charge7_3]
  simp only [g_neg hH]
  ring

private theorem charge8_0 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge8_1 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge8_2 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge8_3 :
    (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial8 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term8 = (6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term8.coefficient : ℂ) = (6 : ℂ) := by norm_num [term8]
  change (term8.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term8.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge8_0, charge8_1, charge8_2, charge8_3]
  simp only [g_neg hH]
  ring

private theorem charge9_0 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 0) := by decide +kernel

private theorem charge9_1 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 0) := by decide +kernel

private theorem charge9_2 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge9_3 :
    (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial9 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term9 = (6 : ℂ) * ((g H (pairA 0)) * (g H (pairW - pairA 0)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term9.coefficient : ℂ) = (6 : ℂ) := by norm_num [term9]
  change (term9.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term9.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge9_0, charge9_1, charge9_2, charge9_3]
  simp only [g_neg hH]
  ring

private theorem charge10_0 :
    (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 1) := by decide +kernel

private theorem charge10_1 :
    (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 1) := by decide +kernel

private theorem charge10_2 :
    (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial10 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term10 = (-3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H pairW))) := by
  have hc : (term10.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term10]
  change (term10.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term10.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge10_0, charge10_1, charge10_2]
  simp only [g_neg hH]
  ring

private theorem charge11_0 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge11_1 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge11_2 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge11_3 :
    (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial11 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term11 = (6 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term11.coefficient : ℂ) = (6 : ℂ) := by norm_num [term11]
  change (term11.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term11.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge11_0, charge11_1, charge11_2, charge11_3]
  simp only [g_neg hH]
  ring

private theorem charge12_0 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge12_1 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge12_2 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge12_3 :
    (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial12 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term12 = (3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term12.coefficient : ℂ) = (3 : ℂ) := by norm_num [term12]
  change (term12.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term12.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge12_0, charge12_1, charge12_2, charge12_3]
  simp only [g_neg hH]
  ring

private theorem charge13_0 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge13_1 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge13_2 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge13_3 :
    (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial13 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term13 = (3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term13.coefficient : ℂ) = (3 : ℂ) := by norm_num [term13]
  change (term13.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term13.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge13_0, charge13_1, charge13_2, charge13_3]
  simp only [g_neg hH]
  ring

private theorem charge14_0 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 1) := by decide +kernel

private theorem charge14_1 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 1) := by decide +kernel

private theorem charge14_2 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge14_3 :
    (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial14 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term14 = (3 : ℂ) * ((g H (pairA 1)) * (g H (pairW - pairA 1)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term14.coefficient : ℂ) = (3 : ℂ) := by norm_num [term14]
  change (term14.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term14.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge14_0, charge14_1, charge14_2, charge14_3]
  simp only [g_neg hH]
  ring

private theorem charge15_0 :
    (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 2) := by decide +kernel

private theorem charge15_1 :
    (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 2) := by decide +kernel

private theorem charge15_2 :
    (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial15 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term15 = (-3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H pairW))) := by
  have hc : (term15.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term15]
  change (term15.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term15.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge15_0, charge15_1, charge15_2]
  simp only [g_neg hH]
  ring

private theorem charge16_0 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge16_1 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge16_2 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge16_3 :
    (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial16 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term16 = (6 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term16.coefficient : ℂ) = (6 : ℂ) := by norm_num [term16]
  change (term16.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term16.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge16_0, charge16_1, charge16_2, charge16_3]
  simp only [g_neg hH]
  ring

private theorem charge17_0 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge17_1 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge17_2 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge17_3 :
    (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial17 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term17 = (3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term17.coefficient : ℂ) = (3 : ℂ) := by norm_num [term17]
  change (term17.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term17.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge17_0, charge17_1, charge17_2, charge17_3]
  simp only [g_neg hH]
  ring

private theorem charge18_0 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge18_1 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge18_2 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge18_3 :
    (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial18 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term18 = (3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term18.coefficient : ℂ) = (3 : ℂ) := by norm_num [term18]
  change (term18.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term18.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge18_0, charge18_1, charge18_2, charge18_3]
  simp only [g_neg hH]
  ring

private theorem charge19_0 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 2) := by decide +kernel

private theorem charge19_1 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 2) := by decide +kernel

private theorem charge19_2 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge19_3 :
    (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial19 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term19 = (3 : ℂ) * ((g H (pairA 2)) * (g H (pairW - pairA 2)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term19.coefficient : ℂ) = (3 : ℂ) := by norm_num [term19]
  change (term19.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term19.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge19_0, charge19_1, charge19_2, charge19_3]
  simp only [g_neg hH]
  ring

private theorem charge20_0 :
    (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) = (pairA 3) := by decide +kernel

private theorem charge20_1 :
    (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) = (pairW - pairA 3) := by decide +kernel

private theorem charge20_2 :
    (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) = -pairW := by decide +kernel

theorem termPolynomial20 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term20 = (-3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H pairW))) := by
  have hc : (term20.coefficient : ℂ) = (-3 : ℂ) := by norm_num [term20]
  change (term20.coefficient : ℂ) * (∏ j : Fin 3, g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (-3 : ℂ) * (g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (0 : Fin 3)) * (g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (1 : Fin 3)) * (g H (fun i => (term20.charges : Matrix Coord (Fin 3) ℤ) i (2 : Fin 3)) * 1))) = _
  rw [charge20_0, charge20_1, charge20_2]
  simp only [g_neg hH]
  ring

private theorem charge21_0 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge21_1 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge21_2 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 0) := by decide +kernel

private theorem charge21_3 :
    (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 0) := by decide +kernel

theorem termPolynomial21 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term21 = (6 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 0))) * (conj (g H (pairW - pairA 0)))) := by
  have hc : (term21.coefficient : ℂ) = (6 : ℂ) := by norm_num [term21]
  change (term21.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (6 : ℂ) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term21.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge21_0, charge21_1, charge21_2, charge21_3]
  simp only [g_neg hH]
  ring

private theorem charge22_0 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge22_1 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge22_2 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 1) := by decide +kernel

private theorem charge22_3 :
    (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 1) := by decide +kernel

theorem termPolynomial22 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term22 = (3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 1))) * (conj (g H (pairW - pairA 1)))) := by
  have hc : (term22.coefficient : ℂ) = (3 : ℂ) := by norm_num [term22]
  change (term22.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term22.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge22_0, charge22_1, charge22_2, charge22_3]
  simp only [g_neg hH]
  ring

private theorem charge23_0 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge23_1 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge23_2 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 2) := by decide +kernel

private theorem charge23_3 :
    (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 2) := by decide +kernel

theorem termPolynomial23 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term23 = (3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 2))) * (conj (g H (pairW - pairA 2)))) := by
  have hc : (term23.coefficient : ℂ) = (3 : ℂ) := by norm_num [term23]
  change (term23.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term23.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge23_0, charge23_1, charge23_2, charge23_3]
  simp only [g_neg hH]
  ring

private theorem charge24_0 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = (pairA 3) := by decide +kernel

private theorem charge24_1 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = (pairW - pairA 3) := by decide +kernel

private theorem charge24_2 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -(pairA 3) := by decide +kernel

private theorem charge24_3 :
    (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -(pairW - pairA 3) := by decide +kernel

theorem termPolynomial24 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term24 = (3 : ℂ) * ((g H (pairA 3)) * (g H (pairW - pairA 3)) * (conj (g H (pairA 3))) * (conj (g H (pairW - pairA 3)))) := by
  have hc : (term24.coefficient : ℂ) = (3 : ℂ) := by norm_num [term24]
  change (term24.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (3 : ℂ) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term24.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge24_0, charge24_1, charge24_2, charge24_3]
  simp only [g_neg hH]
  ring

private theorem charge25_0 :
    (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = alpha := by decide +kernel

private theorem charge25_1 :
    (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = qCross := by decide +kernel

private theorem charge25_2 :
    (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -alpha := by decide +kernel

private theorem charge25_3 :
    (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -qCross := by decide +kernel

theorem termPolynomial25 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term25 = (1 : ℂ) * ((g H alpha) * (g H qCross) * (conj (g H alpha)) * (conj (g H qCross))) := by
  have hc : (term25.coefficient : ℂ) = (1 : ℂ) := by norm_num [term25]
  change (term25.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (1 : ℂ) * (g H (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term25.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge25_0, charge25_1, charge25_2, charge25_3]
  simp only [g_neg hH]
  ring

private theorem charge26_0 :
    (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) = alpha := by decide +kernel

private theorem charge26_1 :
    (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) = qSame := by decide +kernel

private theorem charge26_2 :
    (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) = -alpha := by decide +kernel

private theorem charge26_3 :
    (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) = -qSame := by decide +kernel

theorem termPolynomial26 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H term26 = (1 : ℂ) * ((g H alpha) * (g H qSame) * (conj (g H alpha)) * (conj (g H qSame))) := by
  have hc : (term26.coefficient : ℂ) = (1 : ℂ) := by norm_num [term26]
  change (term26.coefficient : ℂ) * (∏ j : Fin 4, g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i j)) = _
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (1 : ℂ) * (g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (0 : Fin 4)) * (g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (1 : Fin 4)) * (g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (2 : Fin 4)) * (g H (fun i => (term26.charges : Matrix Coord (Fin 4) ℤ) i (3 : Fin 4)) * 1)))) = _
  rw [charge26_0, charge26_1, charge26_2, charge26_3]
  simp only [g_neg hH]
  ring

end MUB6.Certificate.PairTargetSemantics

end

end OAI
