import OAI.Analysis.Triangular.Construction.SpectralProduct
import OAI.Analysis.Triangular.Construction.FiniteCoordinates

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
attribute [local instance] Classical.propDecidable
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
lemma tailColumnSpectral_directJet (p q : TailNode × Fin 2) :
    (tailColumnSpectral q (directJetFunction 0 h p.1.val.val p.2)).re=if q=p then -1 else 0 := by
  unfold tailColumnSpectral
  by_cases hc : q.2.val=0
  · simp only [hc,↓reduceIte,spectralC_directJet]
    congr 1
    apply propext
    constructor
    · rintro ⟨hn,hd⟩
      apply Prod.ext
      · exact Subtype.ext (Subtype.ext hn.symm)
      · exact Fin.ext (hc.trans hd.symm)
    · intro he; subst q; exact ⟨rfl,hc⟩
  · simp only [hc,↓reduceIte,spectralD_directJet]
    have hc1 : q.2.val=1 := by omega
    congr 1
    apply propext
    constructor
    · rintro ⟨hn,hd⟩
      apply Prod.ext
      · exact Subtype.ext (Subtype.ext hn.symm)
      · exact Fin.ext (hc1.trans hd.symm)
    · intro he; subst q; exact ⟨rfl,hc1⟩
lemma tailSpectral_tail_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (p : TailNode × Fin 2) :
    (tailSpectral (coefficientInput C a w) (directJetFunction 0 h p.1.val.val p.2)).re= -w p := by
  rw [tailSpectral_product_apply,add_re,re_tsum (summable_tail_columns_apply _ _)]
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,←spectralPCLM_apply,
    spectralP_directJet,tailColumnSpectral_directJet,mul_zero,zero_add,mul_ite,mul_neg,mul_one,
    tsum_ite_eq]
lemma spectralC_other_directJet (q : Fin 2) (v : ℝ) (n m : Node) (hne : n.val≠m.val) (d : Fin 2) :
    (spectralCCLM m (directJetFunction q v n.val d)).re=0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralC_direct m _).1,(spectralC_direct m _).2,
    cBasis_other_node hne,deriv_cBasis_other_node hne]
  split_ifs <;> simp
lemma spectralD_other_directJet (q : Fin 2) (v : ℝ) (n m : Node) (hne : n.val≠m.val) (d : Fin 2) :
    (spectralDCLM m (directJetFunction q v n.val d)).re=0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralD_direct m _).1,(spectralD_direct m _).2,
    dBasis_other_node hne,deriv_dBasis_other_node hne]
  split_ifs <;> simp
lemma tailColumnSpectral_other_directJet (n : Node) (hn : n.val∈FiniteNodes)
    (q : TailNode × Fin 2) (v : ℝ) (d : Fin 2) :
    (tailColumnSpectral q (directJetFunction 0 v n.val d)).re=0 := by
  have hne : n.val≠q.1.val.val := fun he => q.1.property (he ▸ hn)
  unfold tailColumnSpectral
  split_ifs
  · exact spectralC_other_directJet _ _ _ _ hne _
  · exact spectralD_other_directJet _ _ _ _ hne _
lemma tailSpectral_finite_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (n : Node) (hn : n.val∈FiniteNodes) (v : ℝ) (d : Fin 2) :
    (tailSpectral (coefficientInput C a w) (directJetFunction 0 v n.val d)).re=0 := by
  rw [tailSpectral_product_apply,add_re,re_tsum (summable_tail_columns_apply _ _)]
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,←spectralPCLM_apply,
    spectralP_directJet,tailColumnSpectral_other_directJet n hn,mul_zero,zero_add,tsum_zero]
lemma inputJJet_direct_negative (a : InputCoefficients) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (inputJJet a 0 0 n) (inputJJet a 0 1 n)=
      tailSpectral a (directJetFunction 0 v n d)+finiteSpectral a (directJetFunction 1 v n d) := by
  unfold inputJJet
  rw [negativeJet_add,negativeJet_direct_linear,negativeJet_direct_linear]
lemma inputJJet_tail_direct_negative (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (p : TailNode × Fin 2) :
    (negativeJet h p.1.val.val p.2 (inputJJet (coefficientInput C a w) 0 0 p.1.val.val)
      (inputJJet (coefficientInput C a w) 0 1 p.1.val.val)).re= -w p-AallOperator a p := by
  rw [inputJJet_direct_negative,add_re,tailSpectral_tail_directJet,finiteSpectral_tail_directJet]
  ring
end AtomicTriangular.Construction
end

end OAI
