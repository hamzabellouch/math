import OAI.Analysis.Triangular.Construction.DirectCoordinates

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma atomC_directJet (a : Fin 15) (v : ℝ) (n : Node) (d : Fin 2) :
    (atomSpectral (FiniteCertificate.cCoefficient a) (directJetFunction 1 v n.val d)).re=
      if n.val%36=residue a then Real.exp (Real.pi*(v-H)*n.val)*
        (if d.val=0 then -1 else -Real.pi*(v-H)) else 0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(atomC_direct a _).1,(atomC_direct a _).2]
  simp only [damping,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  by_cases hm : n.val%36=residue a
  · rw [(finiteC_matching_jets a n.val hm).1,finiteC_deriv_re a n.val hm,ite_eq_left hm]
    split_ifs <;> field_simp [Q_node_ne n]
    ring
  · rw [(finiteC_other_jets a n hm).1,(finiteC_other_jets a n hm).2,ite_eq_right hm]
    split_ifs <;> simp
lemma atomD_directJet (a : Fin 15) (v : ℝ) (n : Node) (d : Fin 2) :
    (atomSpectral (FiniteCertificate.dCoefficient a) (directJetFunction 1 v n.val d)).re=
      if n.val%36=residue a then Real.exp (Real.pi*(v-H)*n.val)*
        (if d.val=0 then 0 else -1) else 0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(atomD_direct a _).1,(atomD_direct a _).2]
  simp only [damping,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  by_cases hm : n.val%36=residue a
  · rw [(finiteD_matching_jets a n.val hm).1,(finiteD_matching_jets a n.val hm).2,
      (finiteC_matching_jets a n.val hm).1,ite_eq_left hm]
    split_ifs <;> simp only [zero_re,neg_zero,mul_zero,zero_sub]
    field_simp [Q_node_ne n]
  · rw [(finiteD_other_jets a n hm).1,(finiteD_other_jets a n hm).2,ite_eq_right hm]
    split_ifs <;> simp
lemma finiteColumn_directJet (c : Fin 22) (v : ℝ) (n : Node) (d : Fin 2) :
    (atomSpectral (finiteColumn ⟨c.val,by omega⟩) (directJetFunction 1 v n.val d)).re=
      if n.val%36=residue ⟨c.val/2,by omega⟩ then Real.exp (Real.pi*(v-H)*n.val)*
        (if c.val%2=0 then (if d.val=0 then -1 else -Real.pi*(v-H))
         else (if d.val=0 then 0 else -1)) else 0 := by
  unfold finiteColumn
  simp only [show c.val<22 from c.isLt,↓reduceDIte]
  by_cases hc : c.val%2=0
  · simp only [hc,↓reduceIte]
    exact atomC_directJet _ _ _ _
  · simp only [hc,↓reduceIte]
    exact atomD_directJet _ _ _ _
lemma finiteColumn_tail_directJet (c : Fin 22) (p : TailNode × Fin 2) :
    (atomSpectral (finiteColumn ⟨c.val,by omega⟩) (directJetFunction 1 h p.1.val.val p.2)).re= -AallKernel p c := by
  rw [finiteColumn_directJet]
  unfold AallKernel repetitionKernel repetitionEntry
  have he : h-H= -eta := by norm_num [h,H,eta]
  simp only [he,mul_neg]
  split_ifs <;> ring_nf
lemma finiteSpectral_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (v : ℝ) (n : ℤ) (d : Fin 2) :
    (finiteSpectral (coefficientInput C a w) (directJetFunction 1 v n d)).re=
      ∑ c : Fin 22,a c*(atomSpectral (finiteColumn ⟨c.val,by omega⟩) (directJetFunction 1 v n d)).re := by
  rw [finiteSpectral_coefficient]
  simp only [sum_apply,smul_apply,smul_eq_mul,re_sum,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
lemma finiteSpectral_tail_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (p : TailNode × Fin 2) :
    (finiteSpectral (coefficientInput C a w) (directJetFunction 1 h p.1.val.val p.2)).re= -AallOperator a p := by
  rw [finiteSpectral_directJet]
  simp_rw [finiteColumn_tail_directJet,mul_neg]
  rw [Finset.sum_neg_distrib]
  congr 1
  unfold AallOperator
  erw [AtomicTriangular.L1Kernel.operator_apply,tsum_fintype]
end AtomicTriangular.Construction
end

end OAI
