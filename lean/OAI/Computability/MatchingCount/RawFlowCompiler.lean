import OAI.Computability.MatchingCount.RawFlowSize

namespace OAI

section

namespace BinaryMatching.Raw
open StackCode Polynomial
abbrev FlowContext := ℕ×(Matrix ℕ×(ℕ×ℕ))
abbrev FlowState := FlowContext×Matrix ℤ

def flowStep (s : FlowState) : FlowState :=
  (s.1,augment s.1.1 s.1.2.1 s.1.2.2.1 s.1.2.2.2 s.2)
def flowInitial (z : FlowContext×ℕ) : FlowState :=
  (z.1,matrix z.1.1 (fun _ _ => 0))
lemma flowStep_iterate (z : FlowContext×ℕ) (j : ℕ) :
    flowStep^[j] (flowInitial z)=(z.1,flow z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply',ih,flowStep,flow]

namespace Compiler
open StackCode.Poly
@[fun_prop] theorem reached_poly : Poly (fun z : ℕ×Paths => reached z.1 z.2) := by
  unfold reached
  exact Poly.rawTab Prod.fst (fun z : (ℕ×Paths)×ℕ => (nth z.1.2 z.2).isSome)
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem pathFlow_poly : Poly (fun z : List ℕ×(ℕ×ℕ) => pathFlow z.1 z.2.1 z.2.2) := by
  unfold pathFlow
  have h : Poly (fun z : (List ℕ×(ℕ×ℕ))×(ℕ×ℕ) =>
      ((if decide (z.1.2.1=z.2.2) && decide (z.1.2.2=z.2.1) then 1 else 0)-
       (if decide (z.1.2.1=z.2.1) && decide (z.1.2.2=z.2.2) then 1 else 0):ℤ)) := by fun_prop
  have hm := Poly.mapWith (fun z : List ℕ×(ℕ×ℕ) => z.1.zip z.1.tail) _ (by fun_prop) h
  exact (Poly.comp List.sum _ Poly.listIntSum hm).congr (fun z => by simp only [Bool.and_eq_true,decide_eq_true_eq])
@[fun_prop] theorem augment_poly : Poly (fun z : FlowState =>
    augment z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  have hp : Poly (fun z : FlowState => nth (search z.1.1 z.1.2.1 z.2 z.1.2.2.1 z.1.1) z.1.2.2.2) := by
    apply Poly.rawNth
    · exact Poly.comp _ (fun z : FlowState => ((z.1.1,(z.1.2.1,(z.2,z.1.2.2.1))),z.1.1))
        search_poly (by fun_prop)
    · fun_prop
  have hm : Poly (fun z : FlowState×List ℕ => matrix z.1.1.1 (fun i j => get z.1.2 i j+pathFlow z.2 i j)) := by
    apply Poly.rawMatrix (fun z : FlowState×List ℕ => z.1.1.1)
      (fun z : ((FlowState×List ℕ)×ℕ)×ℕ => get z.1.1.1.2 z.1.2 z.2+pathFlow z.1.1.2 z.1.2 z.2)
    · fun_prop
    · have hp := Poly.comp _ (fun z : ((FlowState×List ℕ)×ℕ)×ℕ => (z.1.1.2,(z.1.2,z.2)))
        pathFlow_poly (by fun_prop)
      fun_prop
  have h := Poly.optionCasesWith
    (fun z : FlowState => nth (search z.1.1 z.1.2.1 z.2 z.1.2.2.1 z.1.1) z.1.2.2.2)
    Prod.snd
    (fun z => matrix z.1.1.1 (fun i j => get z.1.2 i j+pathFlow z.2 i j)) hp (by fun_prop) hm
  exact h.congr (fun z => by unfold augment; cases nth (search z.1.1 z.1.2.1 z.2 z.1.2.2.1 z.1.1) z.1.2.2.2 <;> rfl)
@[fun_prop] theorem flowStep_poly : Poly flowStep := Poly.pair _ _ (by fun_prop) augment_poly
@[fun_prop] theorem flowInitial_poly : Poly flowInitial := by
  unfold flowInitial
  apply Poly.pair
  · fun_prop
  · exact Poly.rawMatrix (fun z : FlowContext×ℕ => z.1.1) (fun _ => (0:ℤ)) (by fun_prop) (by fun_prop)
@[fun_prop] theorem flow_poly : Poly (fun z : FlowContext×ℕ =>
    flow z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  have hi := Poly.iterateFrom flowStep flowStep_poly Prod.snd flowInitial (by fun_prop)
    flowInitial_poly (1000*(X+1)^5) (by
      intro z j hj
      rw [flowStep_iterate]
      let N := (encode (z.2,flowInitial z)).length
      have hctx : (encode z.1).length≤N := by
        simp only [N,flowInitial,code_pair_length,code_nat_length]; omega
      have hn : z.1.1≤N := by
        have := (pair_left_le z.1).trans hctx
        simpa only [code_nat_length] using this
      have ha : z.1.2.2.1≤N := by
        have := (pair_left_le z.1.2.2).trans ((pair_right_le z.1.2).trans ((pair_right_le z.1).trans hctx))
        simpa only [code_nat_length] using this
      have hk : j≤N := by
        simp only [N,code_pair_length,code_nat_length]; omega
      have hb := flow_code_bound z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j
      have hm : z.1.1*(2*(z.1.1*(2*(j*(4*z.1.2.2.1+3+z.1.1*(4*z.1.1+2))+3)+1))+1)≤
          N*(2*(N*(2*(N*(4*N+3+N*(4*N+2))+3)+1))+1) := by gcongr
      simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
      change (encode (z.1,flow z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j)).length≤1000*(N+1)^5
      rw [code_pair_length]
      dsimp only
      have hbb := hb.trans hm
      calc
        _ ≤ 2*N+N*(2*(N*(2*(N*(4*N+3+N*(4*N+2))+3)+1))+1)+1 := by omega
        _ ≤ 1000*(N+1)^5 := by ring_nf; omega)
  exact (Poly.second _ hi).congr (fun z => by rw [flowStep_iterate])
@[fun_prop] theorem sourceCapacity_poly : Poly (fun z : ℕ×(Matrix ℕ×ℕ) => sourceCapacity z.1 z.2.1 z.2.2) := by
  unfold sourceCapacity
  apply Poly.comp List.sum _ Poly.listNatSum
  exact Poly.rawTab Prod.fst (fun z : (ℕ×(Matrix ℕ×ℕ))×ℕ => get z.1.2.1 z.1.2.2 z.2)
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem mincut_poly : Poly (fun z : FlowContext => mincut z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold mincut
  have hs : Poly (fun z : FlowContext => sourceCapacity z.1 z.2.1 z.2.2.1) :=
    Poly.comp _ (fun z : FlowContext => (z.1,(z.2.1,z.2.2.1))) sourceCapacity_poly (by fun_prop)
  have hf : Poly (fun z : FlowContext => flow z.1 z.2.1 z.2.2.1 z.2.2.2 (sourceCapacity z.1 z.2.1 z.2.2.1)) :=
    Poly.comp _ (fun z : FlowContext => (z,sourceCapacity z.1 z.2.1 z.2.2.1)) flow_poly (by fun_prop)
  have hsearch := Poly.comp _ (fun z : FlowContext =>
    ((z.1,(z.2.1,(flow z.1 z.2.1 z.2.2.1 z.2.2.2 (sourceCapacity z.1 z.2.1 z.2.2.1),z.2.2.1))),z.1)) search_poly (by fun_prop)
  exact Poly.comp _ (fun z : FlowContext =>
    (z.1,search z.1 z.2.1 (flow z.1 z.2.1 z.2.2.1 z.2.2.2 (sourceCapacity z.1 z.2.1 z.2.2.1)) z.2.2.1 z.1)) reached_poly (by fun_prop)
@[fun_prop] theorem cutCapacity_poly : Poly (fun z : ℕ×(Matrix ℕ×Cut) => cutCapacity z.1 z.2.1 z.2.2) := by
  unfold cutCapacity
  apply Poly.comp List.sum _ Poly.listNatSum
  apply Poly.rawTab Prod.fst (fun z : (ℕ×(Matrix ℕ×Cut))×ℕ =>
    (tab z.1.1 (fun j => if mem z.1.2.2 z.2 && !mem z.1.2.2 j then get z.1.2.1 z.2 j else 0)).sum)
  · fun_prop
  · apply Poly.comp List.sum _ Poly.listNatSum
    apply Poly.rawTab (fun z : (ℕ×(Matrix ℕ×Cut))×ℕ => z.1.1)
      (fun z : ((ℕ×(Matrix ℕ×Cut))×ℕ)×ℕ => if mem z.1.1.2.2 z.1.2 && !mem z.1.1.2.2 z.2 then
        get z.1.1.2.1 z.1.2 z.2 else 0)
    · fun_prop
    · fun_prop
@[fun_prop] theorem pairs_poly : Poly pairs := by
  unfold pairs
  apply Poly.flatMapWith List.range (fun z : ℕ×ℕ => (List.range z.1).map (fun j => (z.2,j))) (by fun_prop)
  exact Poly.mapWith (fun z : ℕ×ℕ => List.range z.1) (fun z : (ℕ×ℕ)×ℕ => (z.1.2,z.2)) (by fun_prop) (by fun_prop)
@[fun_prop] theorem pairCuts_poly : Poly (fun z : ℕ×(Matrix ℕ×Cut) => pairCuts z.1 z.2.1 z.2.2) := by
  unfold pairCuts
  apply Poly.mapWith _ (fun z : (ℕ×(Matrix ℕ×Cut))×(ℕ×ℕ) => mincut z.1.1 z.1.2.1 z.2.1 z.2.2)
  · apply Poly.filterWith _ (fun z : (ℕ×(Matrix ℕ×Cut))×(ℕ×ℕ) =>
      mem z.1.2.2 z.2.1 && mem z.1.2.2 z.2.2 && decide (z.2.1≠z.2.2))
    · fun_prop
    · have h : Poly (fun z : (ℕ×(Matrix ℕ×Cut))×(ℕ×ℕ) =>
        mem z.1.2.2 z.2.1 && mem z.1.2.2 z.2.2 && !decide (z.2.1=z.2.2)) := by fun_prop
      exact h.congr (fun z => by simp)
  · exact Poly.comp _ (fun z : (ℕ×(Matrix ℕ×Cut))×(ℕ×ℕ) => (z.1.1,(z.1.2.1,z.2))) mincut_poly (by fun_prop)
@[fun_prop] theorem terminalCut_poly : Poly (fun z : ℕ×(Matrix ℕ×Cut) => terminalCut z.1 z.2.1 z.2.2) := by
  unfold terminalCut
  have hf := Poly.listArgminParam Poly.natLT
    (fun z : (ℕ×Matrix ℕ)×Cut => cutCapacity z.1.1 z.1.2 z.2)
    (Poly.comp _ (fun z : (ℕ×Matrix ℕ)×Cut => (z.1.1,(z.1.2,z.2))) cutCapacity_poly (by fun_prop))
  have ha := Poly.comp _ (fun z : ℕ×(Matrix ℕ×Cut) => ((z.1,z.2.1),pairCuts z.1 z.2.1 z.2.2)) hf (by fun_prop)
  have h : Poly (fun z : ℕ×(Matrix ℕ×Cut) => if ((pairCuts z.1 z.2.1 z.2.2).argmin (cutCapacity z.1 z.2.1)).isSome then
      ((pairCuts z.1 z.2.1 z.2.2).argmin (cutCapacity z.1 z.2.1)).getD default else empty z.1) := by fun_prop
  exact h.congr (fun z => by cases (pairCuts z.1 z.2.1 z.2.2).argmin (cutCapacity z.1 z.2.1) <;> rfl)
end Compiler
end BinaryMatching.Raw
end

end OAI
