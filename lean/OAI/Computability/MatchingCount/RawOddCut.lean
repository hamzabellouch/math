import OAI.Computability.MatchingCount.OracleBounds

namespace OAI

section

namespace BinaryMatching.Raw
open RecursiveEval
abbrev OddArg := Matrix ℕ×Cut
abbrev OddJoin := Matrix ℕ×(Cut×(ℕ×ℕ))

def oddExpand (n : ℕ) (a : OddArg) : Branch OddArg Cut OddJoin :=
  let A := terminalCut n a.1 a.2
  if cardinal (inter n A a.2)%2=1 then .leaf A else
    match outside n A,outside n (compl n A) with
    | some r,some q => .fork (a.1,(A,(r,q)))
        (contract n a.1 A r,inter n A a.2)
        (contract n a.1 (compl n A) q,inter n (compl n A) a.2)
    | _,_ => .leaf (empty n)
def oddCombine (n : ℕ) (c : OddJoin) (X Y : Cut) : Cut :=
  cheaper n c.1 (lift n c.2.1 c.2.2.1 X) (lift n (compl n c.2.1) c.2.2.2 Y)
def oddValue (n k : ℕ) (a : OddArg) : Cut :=
  value (empty n) (oddExpand n) (oddCombine n) k a

theorem oddValue_rep {n : ℕ} (k : ℕ) (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) :
    oddValue n k (matrixRep c,cutRep U)=cutRep (OddMincut.recurse k c U) := by
  induction k generalizing c U with
  | zero => exact empty_rep _
  | succ k ih =>
    simp only [oddValue,value,oddExpand,terminalCut_rep,inter_rep,cardinal_rep,compl_rep,outside_rep,
      OddMincut.recurse,OddCutParity.OddSide,Nat.odd_iff]
    split_ifs with hodd
    · rfl
    · cases hr : OddMincut.outside (TerminalMincut.terminalCut c U) <;>
        cases hq : OddMincut.outside (TerminalMincut.terminalCut c U)ᶜ <;>
        simp only [Option.map_none,Option.map_some,contract_rep]
      · exact empty_rep _
      · exact empty_rep _
      · exact empty_rep _
      · rename_i r q
        change oddCombine n (matrixRep c,(cutRep (TerminalMincut.terminalCut c U),(r.val,q.val)))
          (oddValue n k (matrixRep _,cutRep _)) (oddValue n k (matrixRep _,cutRep _))=_
        rw [ih,ih]
        simp only [oddCombine,compl_rep,lift_rep,cheaper_rep]

theorem oddCalls_rep {n : ℕ} (k : ℕ) (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) :
    calls (oddExpand n) k (matrixRep c,cutRep U)=
      DenseOracle.calls k (DenseOracle.make c) U := by
  induction k generalizing c U with
  | zero => rfl
  | succ k ih =>
    simp only [calls,oddExpand,terminalCut_rep,inter_rep,cardinal_rep,compl_rep,outside_rep,
      DenseOracle.calls,DenseOracle.terminalCut_eq,DenseOracle.view_make,OddCutParity.OddSide,Nat.odd_iff]
    split_ifs with hodd
    · rfl
    · cases hr : OddMincut.outside (TerminalMincut.terminalCut c U) <;>
        cases hq : OddMincut.outside (TerminalMincut.terminalCut c U)ᶜ <;>
        simp only [Option.map_none,Option.map_some,contract_rep]
      all_goals simp only [ih,DenseOracle.contract,DenseOracle.view_make]

theorem oddCost_bound {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n))
    (he : Even U.card) (hU : 2≤U.card) :
    cost (oddExpand n) U.card (matrixRep c,cutRep U)≤2*n := by
  have hb := DenseOracle.calls_bound U.card (DenseOracle.make c) U he hU le_rfl
  rw [←oddCalls_rep] at hb
  have hc := cost_le_calls (oddExpand n) U.card (matrixRep c,cutRep U)
  have hu := Finset.card_le_univ U
  simp only [Fintype.card_fin] at hu
  omega
end BinaryMatching.Raw
end

end OAI
