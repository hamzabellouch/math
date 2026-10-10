import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GapPathCode

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ K : ℕ}
namespace TreePath
variable {w : NumericalLine D h ℓ} (P : TreePath w K)
def expression : SquarefreeExpression S.Index K :=
  PatternExpression.gap h (signBit w.line) w.linePrimeCode P.code

lemma expression_support {p : S.Index} (hp : p ∈ P.expression.support) :
    ∃ i,(p:ℕ) ∣ w.line.label (P.edge i) := by
  obtain ⟨i,hi,hp⟩ := mem_biUnion.mp hp
  split_ifs at hp with hc
  · simp at hp
  · change p ∈ (PatternExpression.gap h (signBit w.line) w.linePrimeCode P.code).factors i at hp
    rw [P.code_source_factors] at hp
    split_ifs at hp with hi
    · exact ⟨⟨i.val,hi⟩,(Nat.mem_primeFactors.mp ((mem_labelPrimeSet _ _ _).mp hp)).2.1⟩
    · simp at hp

lemma expression_term (i : Fin K) :
    P.expression.coefficient i * ∏ p ∈ P.expression.factors i,((p:ℕ):ℤ) =
      if hi : i.val<P.length then P.vertex (Fin.succ ⟨i.val,hi⟩)-P.vertex (Fin.castSucc ⟨i.val,hi⟩) else 0 := by
  change (PatternExpression.gap _ _ _ _).coefficient i * ∏ p ∈ (PatternExpression.gap _ _ _ _).factors i,_ = _
  rw [P.code_source_coefficient,P.code_source_factors]
  by_cases hi : i.val<P.length
  · simp only [Nat.zero_le,hi,and_self,ite_true,dite_true]
    have hp : (∏ p ∈ labelPrimeSet (w.line.label (P.edge ⟨i.val,hi⟩)) (w.labels _),((p:ℕ):ℤ)) =
        (w.line.label (P.edge ⟨i.val,hi⟩):ℤ) := by
      exact_mod_cast labelPrimeSet_product (w.line.label (P.edge ⟨i.val,hi⟩)) (w.labels _)
    rw [hp]
    exact (P.path_step ⟨i.val,hi⟩).symm
  · simp only [dite_eq_right hi,zero_mul]

lemma finite_telescoping {n : ℕ} (f : Fin (n+1) → ℤ) :
    (∑ i : Fin n,(f i.succ-f i.castSucc))=f (Fin.last n)-f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have ht := ih (fun i => f i.succ)
    simp only [Fin.succ_castSucc] at ht
    rw [ht]
    simp only [Fin.succ_last,Fin.castSucc_zero]
    ring

lemma expression_eval : P.expression.eval (fun p => ((p:ℕ):ℤ)) =
    P.vertex (Fin.last P.length)-P.vertex 0 := by
  unfold SquarefreeExpression.eval
  simp_rw [P.expression_term]
  have hb : (∑ i : Fin K,if hi : i.val<P.length then
      P.vertex (Fin.succ ⟨i.val,hi⟩)-P.vertex (Fin.castSucc ⟨i.val,hi⟩) else 0)=
      ∑ j : Fin P.length,(P.vertex j.succ-P.vertex j.castSucc) := by
    let f : ℕ → ℤ := fun n => if hn : n<P.length then
      P.vertex (Fin.succ ⟨n,hn⟩)-P.vertex (Fin.castSucc ⟨n,hn⟩) else 0
    change (∑ i : Fin K,f i.val)=_
    rw [Fin.sum_univ_eq_sum_range f K,sum_fin_eq_sum_range]
    change (∑ i ∈ range K,f i)=∑ i ∈ range P.length,f i
    symm
    apply sum_subset (range_mono P.length_le)
    intro i hi hn
    exact dite_eq_right (fun h => hn (mem_range.mpr h))
  exact hb.trans (finite_telescoping P.vertex)

end TreePath
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
