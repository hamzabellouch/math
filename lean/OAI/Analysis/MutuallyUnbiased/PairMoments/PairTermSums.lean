import OAI.Analysis.MutuallyUnbiased.PairTargets.Data

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6.Certificate.PairTargetSemantics

private theorem sumterms0_at0 : terms0 0 = term0 := rfl
private theorem sumterms0_at1 : terms0 1 = term1 := rfl
private theorem sumterms0_at2 : terms0 2 = term2 := rfl
private theorem sumterms0_at3 : terms0 3 = term3 := rfl
private theorem sumterms0_at4 : terms0 4 = term4 := rfl
private theorem sumterms0_at5 : terms0 5 = term5 := rfl
private theorem sumterms0_at6 : terms0 6 = term6 := rfl
private theorem sumterms0_at7 : terms0 7 = term7 := rfl
private theorem sumterms0_at8 : terms0 8 = term8 := rfl
private theorem sumterms0_at9 : terms0 9 = term9 := rfl
private theorem sumterms0_at10 : terms0 10 = term10 := rfl
private theorem sumterms0_at11 : terms0 11 = term11 := rfl
private theorem sumterms0_at12 : terms0 12 = term12 := rfl
private theorem sumterms0_at13 : terms0 13 = term13 := rfl
private theorem sumterms0_at14 : terms0 14 = term14 := rfl
private theorem sumterms0_at15 : terms0 15 = term15 := rfl
private theorem sumterms0_at16 : terms0 16 = term16 := rfl
private theorem sumterms0_at17 : terms0 17 = term17 := rfl
private theorem sumterms0_at18 : terms0 18 = term18 := rfl
private theorem sumterms0_at19 : terms0 19 = term19 := rfl
private theorem sumterms0_at20 : terms0 20 = term20 := rfl
private theorem sumterms0_at21 : terms0 21 = term21 := rfl
private theorem sumterms0_at22 : terms0 22 = term22 := rfl
private theorem sumterms0_at23 : terms0 23 = term23 := rfl
private theorem sumterms0_at24 : terms0 24 = term24 := rfl
private theorem sumterms0_at25 : terms0 25 = term25 := rfl
theorem sum_terms0_expand {R : Type*} [AddCommMonoid R] (F : Term → R) :
    (∑ i : Fin 26, F (terms0 i)) = F term0 + F term1 + F term2 + F term3 + F term4 + F term5 + F term6 + F term7 + F term8 + F term9 + F term10 + F term11 + F term12 + F term13 + F term14 + F term15 + F term16 + F term17 + F term18 + F term19 + F term20 + F term21 + F term22 + F term23 + F term24 + F term25 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F (terms0 0) + (F (terms0 1) + (F (terms0 2) + (F (terms0 3) + (F (terms0 4) + (F (terms0 5) + (F (terms0 6) + (F (terms0 7) + (F (terms0 8) + (F (terms0 9) + (F (terms0 10) + (F (terms0 11) + (F (terms0 12) + (F (terms0 13) + (F (terms0 14) + (F (terms0 15) + (F (terms0 16) + (F (terms0 17) + (F (terms0 18) + (F (terms0 19) + (F (terms0 20) + (F (terms0 21) + (F (terms0 22) + (F (terms0 23) + (F (terms0 24) + (F (terms0 25) + 0)))))))))))))))))))))))))) = F term0 + F term1 + F term2 + F term3 + F term4 + F term5 + F term6 + F term7 + F term8 + F term9 + F term10 + F term11 + F term12 + F term13 + F term14 + F term15 + F term16 + F term17 + F term18 + F term19 + F term20 + F term21 + F term22 + F term23 + F term24 + F term25
  simp only [sumterms0_at0, sumterms0_at1, sumterms0_at2, sumterms0_at3, sumterms0_at4, sumterms0_at5, sumterms0_at6, sumterms0_at7, sumterms0_at8, sumterms0_at9, sumterms0_at10, sumterms0_at11, sumterms0_at12, sumterms0_at13, sumterms0_at14, sumterms0_at15, sumterms0_at16, sumterms0_at17, sumterms0_at18, sumterms0_at19, sumterms0_at20, sumterms0_at21, sumterms0_at22, sumterms0_at23, sumterms0_at24, sumterms0_at25, add_zero, add_assoc]

private theorem sumterms1_at0 : terms1 0 = term0 := rfl
private theorem sumterms1_at1 : terms1 1 = term1 := rfl
private theorem sumterms1_at2 : terms1 2 = term2 := rfl
private theorem sumterms1_at3 : terms1 3 = term3 := rfl
private theorem sumterms1_at4 : terms1 4 = term4 := rfl
private theorem sumterms1_at5 : terms1 5 = term5 := rfl
private theorem sumterms1_at6 : terms1 6 = term6 := rfl
private theorem sumterms1_at7 : terms1 7 = term7 := rfl
private theorem sumterms1_at8 : terms1 8 = term8 := rfl
private theorem sumterms1_at9 : terms1 9 = term9 := rfl
private theorem sumterms1_at10 : terms1 10 = term10 := rfl
private theorem sumterms1_at11 : terms1 11 = term11 := rfl
private theorem sumterms1_at12 : terms1 12 = term12 := rfl
private theorem sumterms1_at13 : terms1 13 = term13 := rfl
private theorem sumterms1_at14 : terms1 14 = term14 := rfl
private theorem sumterms1_at15 : terms1 15 = term15 := rfl
private theorem sumterms1_at16 : terms1 16 = term16 := rfl
private theorem sumterms1_at17 : terms1 17 = term17 := rfl
private theorem sumterms1_at18 : terms1 18 = term18 := rfl
private theorem sumterms1_at19 : terms1 19 = term19 := rfl
private theorem sumterms1_at20 : terms1 20 = term20 := rfl
private theorem sumterms1_at21 : terms1 21 = term21 := rfl
private theorem sumterms1_at22 : terms1 22 = term22 := rfl
private theorem sumterms1_at23 : terms1 23 = term23 := rfl
private theorem sumterms1_at24 : terms1 24 = term24 := rfl
private theorem sumterms1_at25 : terms1 25 = term26 := rfl
theorem sum_terms1_expand {R : Type*} [AddCommMonoid R] (F : Term → R) :
    (∑ i : Fin 26, F (terms1 i)) = F term0 + F term1 + F term2 + F term3 + F term4 + F term5 + F term6 + F term7 + F term8 + F term9 + F term10 + F term11 + F term12 + F term13 + F term14 + F term15 + F term16 + F term17 + F term18 + F term19 + F term20 + F term21 + F term22 + F term23 + F term24 + F term26 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F (terms1 0) + (F (terms1 1) + (F (terms1 2) + (F (terms1 3) + (F (terms1 4) + (F (terms1 5) + (F (terms1 6) + (F (terms1 7) + (F (terms1 8) + (F (terms1 9) + (F (terms1 10) + (F (terms1 11) + (F (terms1 12) + (F (terms1 13) + (F (terms1 14) + (F (terms1 15) + (F (terms1 16) + (F (terms1 17) + (F (terms1 18) + (F (terms1 19) + (F (terms1 20) + (F (terms1 21) + (F (terms1 22) + (F (terms1 23) + (F (terms1 24) + (F (terms1 25) + 0)))))))))))))))))))))))))) = F term0 + F term1 + F term2 + F term3 + F term4 + F term5 + F term6 + F term7 + F term8 + F term9 + F term10 + F term11 + F term12 + F term13 + F term14 + F term15 + F term16 + F term17 + F term18 + F term19 + F term20 + F term21 + F term22 + F term23 + F term24 + F term26
  simp only [sumterms1_at0, sumterms1_at1, sumterms1_at2, sumterms1_at3, sumterms1_at4, sumterms1_at5, sumterms1_at6, sumterms1_at7, sumterms1_at8, sumterms1_at9, sumterms1_at10, sumterms1_at11, sumterms1_at12, sumterms1_at13, sumterms1_at14, sumterms1_at15, sumterms1_at16, sumterms1_at17, sumterms1_at18, sumterms1_at19, sumterms1_at20, sumterms1_at21, sumterms1_at22, sumterms1_at23, sumterms1_at24, sumterms1_at25, add_zero, add_assoc]

end MUB6.Certificate.PairTargetSemantics

end

end OAI
