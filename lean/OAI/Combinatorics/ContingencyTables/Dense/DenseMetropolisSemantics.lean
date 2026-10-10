import OAI.Combinatorics.ContingencyTables.Dense.DenseWordProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanStep

namespace OAI

/-! # The binary dense program realizes the exact finite transition -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits
open scoped Classical

noncomputable section

theorem flatMetropolisStep_pair {m n d p k : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8))
    (proposal : Fin p → Bool) (coins : Fin k → Bool) :
    flatMetropolisStep ((((marginCode R,marginCode P),gridNatCode a),d),
      (List.ofFn proposal,List.ofFn coins)) =
      gridNatCode (match axisCodeStep a (binaryWordEquiv p proposal) with
        | none => a
        | some b => if acceptDyadic
            (denseExponent R P d finProdFinEquiv b-denseExponent R P d finProdFinEquiv a)
            k (binaryWordEquiv k coins) then b else a) := by
  have hc : flatStepCandidate ((((marginCode R,marginCode P),gridNatCode a),d),
      (List.ofFn proposal,List.ofFn coins)) =
      (axisCodeStep a (binaryWordEquiv p proposal)).map gridNatCode :=
    axisWordStep_eq a proposal
  unfold flatMetropolisStep
  rw [hc]
  cases h : axisCodeStep a (binaryWordEquiv p proposal) with
  | none => rfl
  | some b =>
    simp only [Option.map_some,Option.elim_some,flatAcceptCandidate,replaceFlat]
    simp only [flatExponent_code,dyadicWordAccept_ofFn,decide_eq_true_eq]
    split_ifs <;> rfl

lemma ofFn_split_take {p k : ℕ} (bits : Fin (p+k) → Bool) :
    (List.ofFn bits).take p=List.ofFn ((splitWordEquiv p k bits).1) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,Nat.min_eq_left (Nat.le_add_right p k)]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn]
    rfl

lemma ofFn_split_drop {p k : ℕ} (bits : Fin (p+k) → Bool) :
    (List.ofFn bits).drop p=List.ofFn ((splitWordEquiv p k bits).2) := by
  apply List.ext_getElem
  · simp only [List.length_drop,List.length_ofFn,Nat.add_sub_cancel_left]
  · intro i hi hj
    simp only [List.getElem_drop,List.getElem_ofFn]
    apply congrArg bits
    apply Fin.ext
    change p+i=p+i
    rfl

/-- Exact pointwise agreement, hence every finite-word law and mixing
bound for `denseBitStep` applies to the polynomial list implementation. -/
theorem flatWordStep_code {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (a : Grid (I := Fin (m*n)) (4*d^8)) (bits : Fin (denseStepBits d) → Bool) :
    flatWordStep ((((marginCode R,marginCode P),gridNatCode a),d),List.ofFn bits)=
      gridNatCode (denseBitStep R P d finProdFinEquiv a bits) := by
  dsimp only [flatWordStep,proposalWidth]
  have ht := ofFn_split_take (p := Nat.clog 2 (8*d)) (k := 8*d^5) bits
  have hd := ofFn_split_drop (p := Nat.clog 2 (8*d)) (k := 8*d^5) bits
  have hp : ((List.ofFn bits).take (Nat.clog 2 (8*d)),
      (List.ofFn bits).drop (Nat.clog 2 (8*d))) =
      (List.ofFn (splitWordEquiv (Nat.clog 2 (8*d)) (8*d^5) bits).1,
        List.ofFn (splitWordEquiv (Nat.clog 2 (8*d)) (8*d^5) bits).2) := by
    apply Prod.ext
    · exact ht
    · exact hd
  have h := congrArg (fun z => flatMetropolisStep
    ((((marginCode R,marginCode P),gridNatCode a),d),z)) hp
  refine h.trans ((flatMetropolisStep_pair R P a
    (splitWordEquiv (Nat.clog 2 (8*d)) (8*d^5) bits).1
    (splitWordEquiv (Nat.clog 2 (8*d)) (8*d^5) bits).2).trans ?_)
  change gridNatCode (match axisCodeStep a (pairWordEquiv (Nat.clog 2 (8*d)) (8*d^5) bits).1 with
    | none => a
    | some b => if acceptDyadic
        (denseExponent R P d finProdFinEquiv b-denseExponent R P d finProdFinEquiv a)
        (8*d^5) (pairWordEquiv (Nat.clog 2 (8*d)) (8*d^5) bits).2 then b else a)=_
  unfold denseBitStep
  dsimp only
  cases axisCodeStep a (pairWordEquiv (Nat.clog 2 (8*d)) (8*d^5) bits).1 with
  | none => rfl
  | some b =>
    dsimp only

end
end ContingencyTables.DensePrograms

end OAI
