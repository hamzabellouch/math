import Mathlib
import OAI.Combinatorics.ThinTrees.Encoding.CanonicalExpansion
import OAI.Combinatorics.ThinTrees.Encoding.InputArrays

namespace OAI

/-! Input expansion. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack GraphStack

def makeProblem {n m : ℕ} (G : MultiGraph n m) (hn : 0<n) (k : ℕ) : Problem where
  d := n-1
  m := m
  r := k
  G := {
    left e := Fin.cast (Nat.sub_add_cancel hn).symm (G.left e)
    right e := Fin.cast (Nat.sub_add_cancel hn).symm (G.right e)
    loopless e := by
      intro h
      apply G.loopless e
      apply Fin.ext
      exact congrArg (fun v : Fin (n-1+1) => v.val) h }

lemma makeProblem_n {n m : ℕ} (G : MultiGraph n m) (hn : 0<n) (k : ℕ) :
    (makeProblem G hn k).d+1=n := Nat.sub_add_cancel hn

lemma makeProblem_code {n m : ℕ} (G : MultiGraph n m) (hn : 0<n) (k : ℕ) :
    problemCode (makeProblem G hn k) =
      prodCode graphDataCode natCode ( (n,(List.ofFn (fun e => (G.left e).val),
        List.ofFn (fun e => (G.right e).val))),k) := by
  change prodCode graphDataCode natCode
    ((n-1+1,(List.ofFn (fun e => (G.left e).val), List.ofFn (fun e => (G.right e).val))),k)=_
  rw [Nat.sub_add_cancel hn]

lemma makeProblem_connected {n m : ℕ} (G : MultiGraph n m) (hn : 0<n) (k : ℕ)
    (hc : G.EdgeConnected k) : (makeProblem G hn k).G.EdgeConnected k := by
  cases n with
  | zero => omega
  | succ d => simpa [makeProblem] using hc
lemma makeProblem_thin {n m : ℕ} (G : MultiGraph n m) (hn : 0<n) (k : ℕ)
    {C : ℝ} {T : Finset (Fin m)} (h : ThinTree C k (makeProblem G hn k).G T) :
    ThinTree C k G T := by
  cases n with
  | zero => omega
  | succ d => simpa [makeProblem] using h

abbrev eProblem (x : E) : Problem := makeProblem x.val.graph (by have h:=x.property.1;omega) x.val.k
abbrev bProblem (x : B) : Problem := makeProblem x.val.reduced.expanded
  (show 0<x.val.n from by have h:=x.property.1;omega) (x.val.n^2)

def ePrepare : Realizes eCode problemCode eProblem :=
  ((eN.both (((eEndpoint false).tabulateFin eM).both ((eEndpoint true).tabulateFin eM))).both eK)
    |>.changeOutput problemCode eProblem (by
      intro x
      rw [makeProblem_code]
      rfl)
instance poly_ePrepare : PolyTime ePrepare := by unfold ePrepare;infer_instance

lemma eProblem_good (x : E) : 2 ≤ (eProblem x).d+1 ∧ 1 ≤ (eProblem x).r ∧
    (eProblem x).G.EdgeConnected (eProblem x).r := by
  refine ⟨by rw [makeProblem_n];exact x.property.1,x.property.2.1,?_⟩
  exact makeProblem_connected _ _ _ x.property.2.2

def bMultiplicityRat : Realizes bRecCode ratCode (fun x => (x.1.val.multiplicity x.2:ℚ)) :=
  ((bRecordBinary 2).then binaryToRat).congr (fun _ => rfl)
instance poly_bMultiplicityRat : PolyTime bMultiplicityRat := by unfold bMultiplicityRat;apply poly_congr

def bCountBinary : Realizes bRecCode binaryNatCode (fun x => x.1.val.reduced.multiplicity x.2) :=
  let k := brInput.then bKBinary |>.then binaryToRat
  let n := brInput.then bNBinary |>.then binaryToRat
  let c := bMultiplicityRat
  let capped := (c.le k).ite c k
  ((((constant bRecCode ratCode 2).mul (n.pow 2)).mul capped).div k |>.then ratNatFloorBinary)
    |>.congr (by
      intro x
      have he : (if decide ((x.1.val.multiplicity x.2:ℚ)≤(x.1.val.k:ℚ))
          then (x.1.val.multiplicity x.2:ℚ) else (x.1.val.k:ℚ)) =
          (min (x.1.val.multiplicity x.2) x.1.val.k:ℕ) := by
        simp only [Nat.cast_le,decide_eq_true_eq]
        split_ifs with h
        · rw [min_eq_left h]
        · rw [min_eq_right (le_of_not_ge h)]
      change ⌊2*(x.1.val.n:ℚ)^2*(if decide _ then _ else _)/(x.1.val.k:ℚ)⌋₊ = _
      have hex : (2:ℚ)*(x.1.val.n:ℚ)^2*(min (x.1.val.multiplicity x.2) x.1.val.k:ℕ) =
          (2*x.1.val.n^2*min (x.1.val.multiplicity x.2) x.1.val.k:ℕ) := by push_cast; rfl
      rw [he,hex,Nat.floor_div_natCast,Nat.floor_natCast])
instance poly_bCountBinary : PolyTime bCountBinary := by unfold bCountBinary;infer_instance

def bCount := bCountBinary.then binaryToNat
instance poly_bCount : PolyTime bCount := by
  apply poly_bounded_binary
  refine ⟨8*NaturalPolynomial.variable^2,?_⟩
  intro x
  have hv := bN_bound x.1
  have hl : (bCode x.1).length ≤ (bRecCode x).length :=
    le_prodCode_left (ea:=bCode) (eb:=natCode) (x.1,x.2.val)
  have hc := x.1.val.reduced_multiplicity_le x.1.property.2.1 x.2
  have hn : x.1.val.n ≤ 2*(bRecCode x).length := by omega
  have hn2 := Nat.pow_le_pow_left hn 2
  change x.1.val.reduced.multiplicity x.2 ≤ 8*(bRecCode x).length^2
  nlinarith

def bEndpointBlock (right : Bool) : Realizes bRecCode (listCode natCode)
    (fun x => List.replicate (x.1.val.reduced.multiplicity x.2)
      (if right then (x.1.val.right x.2).val else (x.1.val.left x.2).val)) :=
  ((bEndpoint right).both bCount).then (replicateList natCode)
instance poly_bEndpointBlock (right : Bool) : PolyTime (bEndpointBlock right) := by
  unfold bEndpointBlock;infer_instance

def bLefts : Realizes bCode (listCode natCode)
    (fun x => List.ofFn (fun e => (x.val.reduced.expanded.left e).val)) :=
  (((bEndpointBlock false).tabulateFin bP).then (joinList natCode)).congr
    (fun x => x.val.reduced.expanded_lefts.symm)
def bRights : Realizes bCode (listCode natCode)
    (fun x => List.ofFn (fun e => (x.val.reduced.expanded.right e).val)) :=
  (((bEndpointBlock true).tabulateFin bP).then (joinList natCode)).congr
    (fun x => x.val.reduced.expanded_rights.symm)
def bRecords : Realizes bCode (listCode natCode)
    (fun x => List.ofFn (fun e : Fin x.val.reduced.copies.length =>
      (x.val.reduced.copies.get e).1.val)) :=
  ((((brIndex.both bCount).then (replicateList natCode)).tabulateFin bP).then
    (joinList natCode)).congr (fun x => x.val.reduced.expanded_records.symm)
instance poly_bLefts : PolyTime bLefts := by unfold bLefts;infer_instance
instance poly_bRights : PolyTime bRights := by unfold bRights;infer_instance
instance poly_bRecords : PolyTime bRecords := by unfold bRecords;infer_instance

def bPrepare : Realizes bCode problemCode bProblem :=
  ((bN.both (bLefts.both bRights)).both (bN.nmul bN)).changeOutput problemCode bProblem (by
    intro x
    rw [makeProblem_code]
    simp only [pow_two]
    rfl)
instance poly_bPrepare : PolyTime bPrepare := by unfold bPrepare;infer_instance

lemma bProblem_good (x : B) : 2 ≤ (bProblem x).d+1 ∧ 1 ≤ (bProblem x).r ∧
    (bProblem x).G.EdgeConnected (bProblem x).r := by
  have hn : 0<x.val.n := by have h:=x.property.1;omega
  refine ⟨by rw [makeProblem_n];exact x.property.1,by change 1≤x.val.n^2;exact Nat.one_le_pow 2 _ hn,?_⟩
  exact makeProblem_connected _ _ _ (x.val.reduced.expanded_edgeConnected
    (x.val.reduced_edgeConnected hn x.property.2.1 x.property.2.2))

end AlgorithmicThinTrees.InputStack
end

end OAI
