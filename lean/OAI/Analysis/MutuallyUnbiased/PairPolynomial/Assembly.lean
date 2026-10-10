import OAI.Analysis.MutuallyUnbiased.PairPolynomial.Grid

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.Certificate.PairTargetSemantics

theorem sum_grid_polynomial (x : Fin 5 → ℂ) :
    (∑ r, ∑ s, 3 * (x r * conj (x s))) = 3 * ((∑ r, x r) * conj (∑ s, x s)) := by
  simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

private theorem termGrid_at0 : termGrid 0 0 = term0 := rfl
private theorem termGrid_at1 : termGrid 0 1 = term1 := rfl
private theorem termGrid_at2 : termGrid 0 2 = term2 := rfl
private theorem termGrid_at3 : termGrid 0 3 = term3 := rfl
private theorem termGrid_at4 : termGrid 0 4 = term4 := rfl
private theorem termGrid_at5 : termGrid 1 0 = term5 := rfl
private theorem termGrid_at6 : termGrid 1 1 = term6 := rfl
private theorem termGrid_at7 : termGrid 1 2 = term7 := rfl
private theorem termGrid_at8 : termGrid 1 3 = term8 := rfl
private theorem termGrid_at9 : termGrid 1 4 = term9 := rfl
private theorem termGrid_at10 : termGrid 2 0 = term10 := rfl
private theorem termGrid_at11 : termGrid 2 1 = term11 := rfl
private theorem termGrid_at12 : termGrid 2 2 = term12 := rfl
private theorem termGrid_at13 : termGrid 2 3 = term13 := rfl
private theorem termGrid_at14 : termGrid 2 4 = term14 := rfl
private theorem termGrid_at15 : termGrid 3 0 = term15 := rfl
private theorem termGrid_at16 : termGrid 3 1 = term16 := rfl
private theorem termGrid_at17 : termGrid 3 2 = term17 := rfl
private theorem termGrid_at18 : termGrid 3 3 = term18 := rfl
private theorem termGrid_at19 : termGrid 3 4 = term19 := rfl
private theorem termGrid_at20 : termGrid 4 0 = term20 := rfl
private theorem termGrid_at21 : termGrid 4 1 = term21 := rfl
private theorem termGrid_at22 : termGrid 4 2 = term22 := rfl
private theorem termGrid_at23 : termGrid 4 3 = term23 := rfl
private theorem termGrid_at24 : termGrid 4 4 = term24 := rfl

private theorem terms0_at0 : terms0 0 = term0 := rfl
private theorem terms0_at1 : terms0 1 = term1 := rfl
private theorem terms0_at2 : terms0 2 = term2 := rfl
private theorem terms0_at3 : terms0 3 = term3 := rfl
private theorem terms0_at4 : terms0 4 = term4 := rfl
private theorem terms0_at5 : terms0 5 = term5 := rfl
private theorem terms0_at6 : terms0 6 = term6 := rfl
private theorem terms0_at7 : terms0 7 = term7 := rfl
private theorem terms0_at8 : terms0 8 = term8 := rfl
private theorem terms0_at9 : terms0 9 = term9 := rfl
private theorem terms0_at10 : terms0 10 = term10 := rfl
private theorem terms0_at11 : terms0 11 = term11 := rfl
private theorem terms0_at12 : terms0 12 = term12 := rfl
private theorem terms0_at13 : terms0 13 = term13 := rfl
private theorem terms0_at14 : terms0 14 = term14 := rfl
private theorem terms0_at15 : terms0 15 = term15 := rfl
private theorem terms0_at16 : terms0 16 = term16 := rfl
private theorem terms0_at17 : terms0 17 = term17 := rfl
private theorem terms0_at18 : terms0 18 = term18 := rfl
private theorem terms0_at19 : terms0 19 = term19 := rfl
private theorem terms0_at20 : terms0 20 = term20 := rfl
private theorem terms0_at21 : terms0 21 = term21 := rfl
private theorem terms0_at22 : terms0 22 = term22 := rfl
private theorem terms0_at23 : terms0 23 = term23 := rfl
private theorem terms0_at24 : terms0 24 = term24 := rfl
private theorem terms0_at25 : terms0 25 = term25 := rfl
theorem sum_terms0 (F : Term → ℂ) :
    (∑ i : Fin 26, F (terms0 i)) = (∑ r : Fin 5, ∑ s : Fin 5, F (termGrid r s)) + F term25 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F (terms0 0) + (F (terms0 1) + (F (terms0 2) + (F (terms0 3) + (F (terms0 4) + (F (terms0 5) + (F (terms0 6) + (F (terms0 7) + (F (terms0 8) + (F (terms0 9) + (F (terms0 10) + (F (terms0 11) + (F (terms0 12) + (F (terms0 13) + (F (terms0 14) + (F (terms0 15) + (F (terms0 16) + (F (terms0 17) + (F (terms0 18) + (F (terms0 19) + (F (terms0 20) + (F (terms0 21) + (F (terms0 22) + (F (terms0 23) + (F (terms0 24) + (F (terms0 25) + 0)))))))))))))))))))))))))) = ((F (termGrid 0 0) + (F (termGrid 0 1) + (F (termGrid 0 2) + (F (termGrid 0 3) + (F (termGrid 0 4) + 0))))) + ((F (termGrid 1 0) + (F (termGrid 1 1) + (F (termGrid 1 2) + (F (termGrid 1 3) + (F (termGrid 1 4) + 0))))) + ((F (termGrid 2 0) + (F (termGrid 2 1) + (F (termGrid 2 2) + (F (termGrid 2 3) + (F (termGrid 2 4) + 0))))) + ((F (termGrid 3 0) + (F (termGrid 3 1) + (F (termGrid 3 2) + (F (termGrid 3 3) + (F (termGrid 3 4) + 0))))) + ((F (termGrid 4 0) + (F (termGrid 4 1) + (F (termGrid 4 2) + (F (termGrid 4 3) + (F (termGrid 4 4) + 0))))) + 0))))) + F term25
  simp only [terms0_at0, terms0_at1, terms0_at2, terms0_at3, terms0_at4, terms0_at5, terms0_at6, terms0_at7, terms0_at8, terms0_at9, terms0_at10, terms0_at11, terms0_at12, terms0_at13, terms0_at14, terms0_at15, terms0_at16, terms0_at17, terms0_at18, terms0_at19, terms0_at20, terms0_at21, terms0_at22, terms0_at23, terms0_at24, terms0_at25, termGrid_at0, termGrid_at1, termGrid_at2, termGrid_at3, termGrid_at4, termGrid_at5, termGrid_at6, termGrid_at7, termGrid_at8, termGrid_at9, termGrid_at10, termGrid_at11, termGrid_at12, termGrid_at13, termGrid_at14, termGrid_at15, termGrid_at16, termGrid_at17, termGrid_at18, termGrid_at19, termGrid_at20, termGrid_at21, termGrid_at22, termGrid_at23, termGrid_at24, add_zero, add_assoc]

theorem pair_polynomial0 {H : CMatrix} (hH : IsHadamard H) :
    (∑ i : Fin 26, termPolynomial H (terms0 i)) =
      3 * (pairL H * conj (pairL H)) +
        (g H alpha * g H qCross) * conj (g H alpha * g H qCross) := by
  rw [sum_terms0]
  simp_rw [termGrid_polynomial hH]
  rw [sum_grid_polynomial, pairSummand_sum, termPolynomial25 hH]
  simp only [map_mul, one_mul]
  ring

private theorem terms1_at0 : terms1 0 = term0 := rfl
private theorem terms1_at1 : terms1 1 = term1 := rfl
private theorem terms1_at2 : terms1 2 = term2 := rfl
private theorem terms1_at3 : terms1 3 = term3 := rfl
private theorem terms1_at4 : terms1 4 = term4 := rfl
private theorem terms1_at5 : terms1 5 = term5 := rfl
private theorem terms1_at6 : terms1 6 = term6 := rfl
private theorem terms1_at7 : terms1 7 = term7 := rfl
private theorem terms1_at8 : terms1 8 = term8 := rfl
private theorem terms1_at9 : terms1 9 = term9 := rfl
private theorem terms1_at10 : terms1 10 = term10 := rfl
private theorem terms1_at11 : terms1 11 = term11 := rfl
private theorem terms1_at12 : terms1 12 = term12 := rfl
private theorem terms1_at13 : terms1 13 = term13 := rfl
private theorem terms1_at14 : terms1 14 = term14 := rfl
private theorem terms1_at15 : terms1 15 = term15 := rfl
private theorem terms1_at16 : terms1 16 = term16 := rfl
private theorem terms1_at17 : terms1 17 = term17 := rfl
private theorem terms1_at18 : terms1 18 = term18 := rfl
private theorem terms1_at19 : terms1 19 = term19 := rfl
private theorem terms1_at20 : terms1 20 = term20 := rfl
private theorem terms1_at21 : terms1 21 = term21 := rfl
private theorem terms1_at22 : terms1 22 = term22 := rfl
private theorem terms1_at23 : terms1 23 = term23 := rfl
private theorem terms1_at24 : terms1 24 = term24 := rfl
private theorem terms1_at25 : terms1 25 = term26 := rfl
theorem sum_terms1 (F : Term → ℂ) :
    (∑ i : Fin 26, F (terms1 i)) = (∑ r : Fin 5, ∑ s : Fin 5, F (termGrid r s)) + F term26 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F (terms1 0) + (F (terms1 1) + (F (terms1 2) + (F (terms1 3) + (F (terms1 4) + (F (terms1 5) + (F (terms1 6) + (F (terms1 7) + (F (terms1 8) + (F (terms1 9) + (F (terms1 10) + (F (terms1 11) + (F (terms1 12) + (F (terms1 13) + (F (terms1 14) + (F (terms1 15) + (F (terms1 16) + (F (terms1 17) + (F (terms1 18) + (F (terms1 19) + (F (terms1 20) + (F (terms1 21) + (F (terms1 22) + (F (terms1 23) + (F (terms1 24) + (F (terms1 25) + 0)))))))))))))))))))))))))) = ((F (termGrid 0 0) + (F (termGrid 0 1) + (F (termGrid 0 2) + (F (termGrid 0 3) + (F (termGrid 0 4) + 0))))) + ((F (termGrid 1 0) + (F (termGrid 1 1) + (F (termGrid 1 2) + (F (termGrid 1 3) + (F (termGrid 1 4) + 0))))) + ((F (termGrid 2 0) + (F (termGrid 2 1) + (F (termGrid 2 2) + (F (termGrid 2 3) + (F (termGrid 2 4) + 0))))) + ((F (termGrid 3 0) + (F (termGrid 3 1) + (F (termGrid 3 2) + (F (termGrid 3 3) + (F (termGrid 3 4) + 0))))) + ((F (termGrid 4 0) + (F (termGrid 4 1) + (F (termGrid 4 2) + (F (termGrid 4 3) + (F (termGrid 4 4) + 0))))) + 0))))) + F term26
  simp only [terms1_at0, terms1_at1, terms1_at2, terms1_at3, terms1_at4, terms1_at5, terms1_at6, terms1_at7, terms1_at8, terms1_at9, terms1_at10, terms1_at11, terms1_at12, terms1_at13, terms1_at14, terms1_at15, terms1_at16, terms1_at17, terms1_at18, terms1_at19, terms1_at20, terms1_at21, terms1_at22, terms1_at23, terms1_at24, terms1_at25, termGrid_at0, termGrid_at1, termGrid_at2, termGrid_at3, termGrid_at4, termGrid_at5, termGrid_at6, termGrid_at7, termGrid_at8, termGrid_at9, termGrid_at10, termGrid_at11, termGrid_at12, termGrid_at13, termGrid_at14, termGrid_at15, termGrid_at16, termGrid_at17, termGrid_at18, termGrid_at19, termGrid_at20, termGrid_at21, termGrid_at22, termGrid_at23, termGrid_at24, add_zero, add_assoc]

theorem pair_polynomial1 {H : CMatrix} (hH : IsHadamard H) :
    (∑ i : Fin 26, termPolynomial H (terms1 i)) =
      3 * (pairL H * conj (pairL H)) +
        (g H alpha * g H qSame) * conj (g H alpha * g H qSame) := by
  rw [sum_terms1]
  simp_rw [termGrid_polynomial hH]
  rw [sum_grid_polynomial, pairSummand_sum, termPolynomial26 hH]
  simp only [map_mul, one_mul]
  ring

end MUB6.Certificate.PairTargetSemantics

end

end OAI
