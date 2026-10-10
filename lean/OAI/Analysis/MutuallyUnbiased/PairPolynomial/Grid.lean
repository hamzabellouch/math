import Mathlib.Tactic.FinCases
import OAI.Analysis.MutuallyUnbiased.PairPolynomial.Terms

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

def termGrid : Fin 5 → Fin 5 → Term :=
  ![![term0, term1, term2, term3, term4], ![term5, term6, term7, term8, term9], ![term10, term11, term12, term13, term14], ![term15, term16, term17, term18, term19], ![term20, term21, term22, term23, term24]]

def pairSummand (H : CMatrix) : Fin 5 → ℂ :=
  ![-g H pairW, 2 * g H (pairA 0) * g H (pairW - pairA 0),
    g H (pairA 1) * g H (pairW - pairA 1),
    g H (pairA 2) * g H (pairW - pairA 2),
    g H (pairA 3) * g H (pairW - pairA 3)]

theorem pairSummand_sum (H : CMatrix) : (∑ r, pairSummand H r) = pairL H := by
  simp [pairSummand, pairL, pairCoefficient, Fin.sum_univ_succ]

private theorem grid0 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 0) = 3 * (pairSummand H 0 * conj (pairSummand H 0)) := by
  change termPolynomial H term0 = _
  rw [termPolynomial0 hH]
  simp [pairSummand, map_neg]

private theorem grid1 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 1) = 3 * (pairSummand H 0 * conj (pairSummand H 1)) := by
  change termPolynomial H term1 = _
  rw [termPolynomial1 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid2 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 2) = 3 * (pairSummand H 0 * conj (pairSummand H 2)) := by
  change termPolynomial H term2 = _
  rw [termPolynomial2 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid3 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 3) = 3 * (pairSummand H 0 * conj (pairSummand H 3)) := by
  change termPolynomial H term3 = _
  rw [termPolynomial3 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid4 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 0 4) = 3 * (pairSummand H 0 * conj (pairSummand H 4)) := by
  change termPolynomial H term4 = _
  rw [termPolynomial4 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid5 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 0) = 3 * (pairSummand H 1 * conj (pairSummand H 0)) := by
  change termPolynomial H term5 = _
  rw [termPolynomial5 hH]
  simp [pairSummand, map_neg]
  ring

private theorem grid6 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 1) = 3 * (pairSummand H 1 * conj (pairSummand H 1)) := by
  change termPolynomial H term6 = _
  rw [termPolynomial6 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid7 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 2) = 3 * (pairSummand H 1 * conj (pairSummand H 2)) := by
  change termPolynomial H term7 = _
  rw [termPolynomial7 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid8 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 3) = 3 * (pairSummand H 1 * conj (pairSummand H 3)) := by
  change termPolynomial H term8 = _
  rw [termPolynomial8 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid9 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 1 4) = 3 * (pairSummand H 1 * conj (pairSummand H 4)) := by
  change termPolynomial H term9 = _
  rw [termPolynomial9 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid10 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 0) = 3 * (pairSummand H 2 * conj (pairSummand H 0)) := by
  change termPolynomial H term10 = _
  rw [termPolynomial10 hH]
  simp [pairSummand, map_neg]

private theorem grid11 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 1) = 3 * (pairSummand H 2 * conj (pairSummand H 1)) := by
  change termPolynomial H term11 = _
  rw [termPolynomial11 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid12 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 2) = 3 * (pairSummand H 2 * conj (pairSummand H 2)) := by
  change termPolynomial H term12 = _
  rw [termPolynomial12 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid13 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 3) = 3 * (pairSummand H 2 * conj (pairSummand H 3)) := by
  change termPolynomial H term13 = _
  rw [termPolynomial13 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid14 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 2 4) = 3 * (pairSummand H 2 * conj (pairSummand H 4)) := by
  change termPolynomial H term14 = _
  rw [termPolynomial14 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid15 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 0) = 3 * (pairSummand H 3 * conj (pairSummand H 0)) := by
  change termPolynomial H term15 = _
  rw [termPolynomial15 hH]
  simp [pairSummand, map_neg]

private theorem grid16 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 1) = 3 * (pairSummand H 3 * conj (pairSummand H 1)) := by
  change termPolynomial H term16 = _
  rw [termPolynomial16 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid17 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 2) = 3 * (pairSummand H 3 * conj (pairSummand H 2)) := by
  change termPolynomial H term17 = _
  rw [termPolynomial17 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid18 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 3) = 3 * (pairSummand H 3 * conj (pairSummand H 3)) := by
  change termPolynomial H term18 = _
  rw [termPolynomial18 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid19 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 3 4) = 3 * (pairSummand H 3 * conj (pairSummand H 4)) := by
  change termPolynomial H term19 = _
  rw [termPolynomial19 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid20 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 0) = 3 * (pairSummand H 4 * conj (pairSummand H 0)) := by
  change termPolynomial H term20 = _
  rw [termPolynomial20 hH]
  simp [pairSummand, map_neg]

private theorem grid21 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 1) = 3 * (pairSummand H 4 * conj (pairSummand H 1)) := by
  change termPolynomial H term21 = _
  rw [termPolynomial21 hH]
  simp [pairSummand, map_mul, map_ofNat]
  ring

private theorem grid22 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 2) = 3 * (pairSummand H 4 * conj (pairSummand H 2)) := by
  change termPolynomial H term22 = _
  rw [termPolynomial22 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid23 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 3) = 3 * (pairSummand H 4 * conj (pairSummand H 3)) := by
  change termPolynomial H term23 = _
  rw [termPolynomial23 hH]
  simp [pairSummand, map_mul]
  ring

private theorem grid24 {H : CMatrix} (hH : IsHadamard H) :
    termPolynomial H (termGrid 4 4) = 3 * (pairSummand H 4 * conj (pairSummand H 4)) := by
  change termPolynomial H term24 = _
  rw [termPolynomial24 hH]
  simp [pairSummand, map_mul]
  ring

theorem termGrid_polynomial {H : CMatrix} (hH : IsHadamard H) (r s : Fin 5) :
    termPolynomial H (termGrid r s) = 3 * (pairSummand H r * conj (pairSummand H s)) := by
  fin_cases r
  · fin_cases s
    · exact grid0 hH
    · exact grid1 hH
    · exact grid2 hH
    · exact grid3 hH
    · exact grid4 hH
  · fin_cases s
    · exact grid5 hH
    · exact grid6 hH
    · exact grid7 hH
    · exact grid8 hH
    · exact grid9 hH
  · fin_cases s
    · exact grid10 hH
    · exact grid11 hH
    · exact grid12 hH
    · exact grid13 hH
    · exact grid14 hH
  · fin_cases s
    · exact grid15 hH
    · exact grid16 hH
    · exact grid17 hH
    · exact grid18 hH
    · exact grid19 hH
  · fin_cases s
    · exact grid20 hH
    · exact grid21 hH
    · exact grid22 hH
    · exact grid23 hH
    · exact grid24 hH

end MUB6.Certificate.PairTargetSemantics

end

end OAI
