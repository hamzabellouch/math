import OAI.Analysis.Triangular.Construction.TailCoordinates

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
def rowNode (i : Fin 20) : Node := ⟨finiteNode ⟨i.val/2,by omega⟩,by
  have hh : ∀ n : Fin 10,0<finiteNode n ∧ finiteNode n%36∈residues := by decide +kernel
  exact hh _⟩
def rowDerivative (i : Fin 20) : Fin 2 := ⟨i.val%2,by omega⟩
lemma rowNode_mem (i : Fin 20) : (rowNode i).val∈FiniteNodes := by
  have hh : ∀ n : Fin 10,finiteNode n∈FiniteNodes := by decide +kernel
  exact hh _
lemma finite_column_matching (i : Fin 20) (c : Fin 22) :
    ((rowNode i).val%36=residue ⟨c.val/2,by omega⟩ ∧ c.val%2=i.val%2) ↔ c.val=i.val+2 := by
  have hh : ∀ i : Fin 20, ∀ c : Fin 22,
      ((rowNode i).val%36=residue ⟨c.val/2,by omega⟩ ∧ c.val%2=i.val%2) ↔ c.val=i.val+2 := by decide +kernel
  exact hh i c
lemma finiteColumn_row_directJet (c : Fin 22) (i : Fin 20) :
    (atomSpectral (finiteColumn ⟨c.val,by omega⟩) (directJetFunction 1 H (rowNode i).val (rowDerivative i))).re=
      if c=⟨i.val+2,by omega⟩ then -1 else 0 := by
  rw [finiteColumn_directJet]
  simp only [sub_self,mul_zero,zero_mul,Real.exp_zero,one_mul,rowDerivative]
  have hh := finite_column_matching i c
  have hc0 : c.val%2<2 := Nat.mod_lt _ (by norm_num)
  have hi0 : i.val%2<2 := Nat.mod_lt _ (by norm_num)
  simp only [Fin.ext_iff]
  split_ifs <;> norm_num at * <;> (try omega)
  all_goals split_ifs <;> norm_num at * <;> try omega
  all_goals simp_all only [↓reduceIte]
  all_goals
    split_ifs <;> norm_num at *
    omega
lemma finiteSpectral_row_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (i : Fin 20) :
    (finiteSpectral (coefficientInput C a w) (directJetFunction 1 H (rowNode i).val (rowDerivative i))).re=
      -a ⟨i.val+2,by omega⟩ := by
  rw [finiteSpectral_directJet]
  simp only [finiteColumn_row_directJet,mul_ite,mul_neg,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
lemma inputJJet_row_direct_negative (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (i : Fin 20) :
    (negativeJet H (rowNode i).val (rowDerivative i) (inputJJet (coefficientInput C a w) 0 0 (rowNode i).val)
      (inputJJet (coefficientInput C a w) 0 1 (rowNode i).val)).re= -a ⟨i.val+2,by omega⟩ := by
  rw [inputJJet_direct_negative,add_re,tailSpectral_finite_directJet C a w _ (rowNode_mem i),
    finiteSpectral_row_directJet,zero_add]
end AtomicTriangular.Construction
end

end OAI
