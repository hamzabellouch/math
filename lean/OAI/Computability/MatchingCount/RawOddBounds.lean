import OAI.Computability.MatchingCount.RecursiveCompiler

namespace OAI

section

namespace BinaryMatching.Raw
open StackCode RecursiveEval

def ArgGood (n B : ℕ) (a : OddArg) : Prop :=
  ∃ (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)),a=(matrixRep c,cutRep U) ∧ DenseOracle.total c≤B
def CutGood (n : ℕ) (S : Cut) : Prop := ∃ U : Finset (Fin n),S=cutRep U
def JoinGood (n B : ℕ) (a : OddJoin) : Prop :=
  ∃ (c : Fin n → Fin n → ℕ) (A : Finset (Fin n)) (r q : Fin n),
    a=(matrixRep c,(cutRep A,(r.val,q.val))) ∧ DenseOracle.total c≤B

lemma oddExpand_good (n B : ℕ) (a : OddArg) (ha : ArgGood n B a) :
    match oddExpand n a with
    | .leaf S => CutGood n S
    | .fork c x y => JoinGood n B c ∧ ArgGood n B x ∧ ArgGood n B y := by
  obtain ⟨c,U,rfl,hc⟩ := ha
  simp only [oddExpand,terminalCut_rep,inter_rep,cardinal_rep,compl_rep,outside_rep]
  split_ifs
  · exact ⟨_,rfl⟩
  · cases hr : OddMincut.outside (TerminalMincut.terminalCut c U) <;>
      cases hq : OddMincut.outside (TerminalMincut.terminalCut c U)ᶜ <;>
      simp only [Option.map_none,Option.map_some,contract_rep]
    · exact ⟨_,empty_rep _⟩
    · exact ⟨_,empty_rep _⟩
    · exact ⟨_,empty_rep _⟩
    · rename_i r q
      refine ⟨⟨c,_,r,q,rfl,hc⟩,⟨_,_,rfl,?_⟩,⟨_,_,rfl,?_⟩⟩ <;>
        exact (DenseOracle.push_total_le _ _).trans hc

lemma oddCombine_good (n B : ℕ) (c : OddJoin) (hc : JoinGood n B c)
    (X : Cut) (hX : CutGood n X) (Y : Cut) (hY : CutGood n Y) : CutGood n (oddCombine n c X Y) := by
  obtain ⟨c,A,r,q,rfl,hc⟩ := hc
  obtain ⟨X,rfl⟩ := hX
  obtain ⟨Y,rfl⟩ := hY
  simp only [oddCombine,compl_rep,lift_rep,cheaper_rep]
  exact ⟨_,rfl⟩

lemma vectorRep_code_bound {α : Type} [Coding α] {n : ℕ} (f : Fin n → α) (M : ℕ)
    (h : ∀ i,(encode (f i)).length≤M) :
    (encode (vectorRep f)).length≤n*(2*M+1) := by
  have hh := list_code_bound (vectorRep f) M (by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact h i)
  simpa only [vectorRep,List.length_ofFn] using hh

lemma matrixRep_code_bound {n : ℕ} (c : Fin n → Fin n → ℕ) (B : ℕ)
    (h : DenseOracle.total c≤B) : (encode (matrixRep c)).length≤n*(2*(n*(2*B+1))+1) := by
  apply vectorRep_code_bound
  intro i
  apply vectorRep_code_bound
  intro j
  simpa only [code_nat_length] using (DenseOracle.entry_le_total c i j).trans h

lemma cutRep_code_length {n : ℕ} (S : Finset (Fin n)) : (encode (cutRep S)).length=3*n := by
  rw [cut_code_length]
  simp only [cutRep,vectorRep,List.length_ofFn]

def oddWordBound (n B : ℕ) : ℕ := 1000*(n+1)^2*(B+1)
def oddBudget (n B : ℕ) : ℕ := 100000*(n+1)^3*(B+1)

lemma arg_code_bound (n B : ℕ) (a : OddArg) (ha : ArgGood n B a) :
    (encode a).length≤100*(n+1)^2*(B+1) := by
  obtain ⟨c,U,rfl,hc⟩ := ha
  have hh := matrixRep_code_bound c B hc
  simp only [code_pair_length,cutRep_code_length]
  calc
    _ ≤ 2*(n*(2*(n*(2*B+1))+1))+3*n+1 := by omega
    _ ≤ _ := by ring_nf; omega
lemma join_code_bound (n B : ℕ) (a : OddJoin) (ha : JoinGood n B a) :
    (encode a).length≤100*(n+1)^2*(B+1) := by
  obtain ⟨c,A,r,q,rfl,hc⟩ := ha
  have hh := matrixRep_code_bound c B hc
  have hr := r.isLt
  have hq := q.isLt
  simp only [code_pair_length,cutRep_code_length,code_nat_length]
  calc
    _ ≤ 2*(n*(2*(n*(2*B+1))+1))+9*n+3 := by omega
    _ ≤ _ := by ring_nf; omega

lemma command_code_bound (n B : ℕ) (c : Command OddArg OddJoin)
    (hc : CommandGood n (ArgGood n B) (JoinGood n B) c) : (encode c).length≤oddWordBound n B := by
  cases c with
  | call k a =>
    obtain ⟨hk,ha⟩ := hc
    have hh := arg_code_bound n B a ha
    rw [code_call]
    unfold oddWordBound
    calc
      _ ≤ 8*n+4*(100*(n+1)^2*(B+1))+7 := by omega
      _ ≤ _ := by ring_nf; omega
  | join c =>
    have hh := join_code_bound n B c hc
    rw [code_join]
    unfold oddWordBound
    calc
      _ ≤ 2*(100*(n+1)^2*(B+1))+2 := by omega
      _ ≤ _ := by ring_nf; omega
lemma cut_code_bound (n B : ℕ) (S : Cut) (hS : CutGood n S) : (encode S).length≤oddWordBound n B := by
  obtain ⟨S,rfl⟩ := hS
  rw [cutRep_code_length]
  unfold oddWordBound
  ring_nf
  omega

lemma oddOrbit_bound {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n))
    (B : ℕ) (hB : DenseOracle.total c≤B) (j : ℕ) (hj : j≤2*n) :
    (encode ((paramStep empty oddExpand oddCombine)^[j]
      (n,([Command.call U.card (matrixRep c,cutRep U)],[])))).length≤oddBudget n B := by
  rw [paramStep_iterate]
  dsimp only
  have hz : CutGood n (empty n) := ⟨_,empty_rep _⟩
  have hU : U.card≤n := by simpa only [Fintype.card_fin] using Finset.card_le_univ U
  have hgood : StateGood n (ArgGood n B) (CutGood n) (JoinGood n B)
      ([Command.call U.card (matrixRep c,cutRep U)],[]) := by
    constructor
    · intro a ha
      obtain rfl := List.mem_singleton.mp ha
      exact ⟨hU,⟨c,U,rfl,hB⟩⟩
    · simp
  have hg := iterate_good (empty n) (oddExpand n) (oddCombine n) n (ArgGood n B) (CutGood n) (JoinGood n B)
    hz (fun a ha => by
      have hh := oddExpand_good n B a ha
      cases h : oddExpand n a <;> simpa only [h] using hh) (oddCombine_good n B) _ hgood j
  have hl := iterate_length (empty n) (oddExpand n) (oddCombine n)
    ([Command.call U.card (matrixRep c,cutRep U)],[]) j
  simp only [List.length_singleton,List.length_nil,Nat.add_zero] at hl
  have hs := state_code_bound _ (oddWordBound n B)
    (fun cmd hc => command_code_bound n B cmd (hg.1 cmd hc))
    (fun S hS => cut_code_bound n B S (hg.2 S hS))
  have hlen : ((step (empty n) (oddExpand n) (oddCombine n))^[j]
      ([Command.call U.card (matrixRep c,cutRep U)],[])).1.length+
    ((step (empty n) (oddExpand n) (oddCombine n))^[j]
      ([Command.call U.card (matrixRep c,cutRep U)],[])).2.length≤1+4*n := by omega
  have hm := Nat.add_le_add_right
    (Nat.mul_le_mul_right (2*oddWordBound n B+1) (Nat.mul_le_mul_left 2 hlen)) 1
  rw [code_pair_length,code_nat_length]
  dsimp only
  have hss := hs.trans hm
  calc
    _ ≤ 2*n+(2*(1+4*n)*(2*oddWordBound n B+1)+1)+1 := by omega
    _ ≤ oddBudget n B := by unfold oddWordBound oddBudget; ring_nf; omega
end BinaryMatching.Raw
end

end OAI
