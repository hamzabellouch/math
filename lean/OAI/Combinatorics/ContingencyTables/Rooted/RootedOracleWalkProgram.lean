import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleWordProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseStepGrowth

namespace OAI

/-! # Polynomial execution of an oracle walk

The immutable graph and cell arrays are kept separately from the grid
coordinates. A coordinate changes by at most one per transition, which
bounds every accumulator reached by the binary list fold.
-/

namespace ContingencyTables.RootedOracleWalkProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial
open scoped Classical

abbrev Frame := ℕ×(RootedPenaltyEvaluateProgram.Parameters×RootedDemandProgram.Input)
abbrev State := Frame×List ℕ

def toData (z : State) : RootedOracleStepProgram.Data :=
  (z.1.1,(z.1.2.1,(z.1.2.2,z.2)))
def toDataRealizer : Realizer toData :=
  pair (composition first first)
    (pair (composition (composition first second) first)
      (pair (composition (composition first second) second) second))
lemma polynomial_toData : PolynomialTime toDataRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_first)
      (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
          polynomial_second) polynomial_second))

def advance (z : List Bool×State) : State :=
  (z.2.1,RootedOracleStepProgram.wordStep (toData z.2,z.1))
def advanceRealizer : Realizer advance :=
  pair (composition second first)
    (composition (f := fun z : List Bool×State => (toData z.2,z.1))
      (g := RootedOracleStepProgram.wordStep)
      (pair (composition (f := fun z : List Bool×State => z.2) (g := toData)
        second toDataRealizer) first) RootedOracleStepProgram.wordStepRealizer)
lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_toData) polynomial_first)
      RootedOracleStepProgram.polynomial_wordStep)

lemma step_growth (z : RootedOracleStepProgram.StepInput) (S : ℕ)
    (hx : ∀ a∈z.1.2.2.2,a.size≤S) :
    (RootedOracleStepProgram.step z).length=z.1.2.2.2.length ∧
      ∀ a∈RootedOracleStepProgram.step z,a.size≤S+2 := by
  have hstay : z.1.2.2.2.length=z.1.2.2.2.length ∧
      ∀ a∈z.1.2.2.2,a.size≤S+2 :=
    ⟨rfl,fun a ha => (hx a ha).trans (Nat.le_add_right _ _)⟩
  unfold RootedOracleStepProgram.step
  cases h : RootedOracleStepProgram.candidate z with
  | none => exact hstay
  | some ys =>
    have hy := axisListStep_growth
      (((z.1.1,z.1.2.2.2),MatchingFPRAS.StackAddition.value z.2.1/2),
        decide (MatchingFPRAS.StackAddition.value z.2.1%2=1)) ys S h hx
    simp only [Option.elim_some,RootedOracleStepProgram.acceptCandidate]
    split <;> assumption

lemma advance_growth (state : State) (bits : List Bool) (S : ℕ)
    (hx : ∀ a∈state.2,a.size≤S) :
    (advance (bits,state)).2.length=state.2.length ∧
      ∀ a∈(advance (bits,state)).2,a.size≤S+2 :=
  step_growth _ S hx

def walkWords (z : State×List (List Bool)) : State :=
  z.2.foldl (fun state bits => advance (bits,state)) z.1
def walkWordsRealizer : Realizer walkWords :=
  composition (pair second first) (fold advanceRealizer)

lemma fold_frame (bits : List (List Bool)) (state : State) :
    let out := bits.foldl (fun state bits => advance (bits,state)) state
    out.1=state.1 ∧ out.2.length=state.2.length := by
  induction bits generalizing state with
  | nil => exact ⟨rfl,rfl⟩
  | cons b bs ih =>
    have h := ih (advance (b,state))
    have hl : (advance (b,state)).2.length=state.2.length := by
      exact (advance_growth state b (state.2.map Nat.size).sum
        (fun a ha => List.single_le_sum (fun _ _ => Nat.zero_le _) a.size
          (List.mem_map.mpr ⟨a,ha,rfl⟩))).1
    exact ⟨h.1,h.2.trans hl⟩

lemma fold_sizes (bits : List (List Bool)) (state : State) (S : ℕ)
    (hx : ∀ a∈state.2,a.size≤S) :
    ∀ a∈(bits.foldl (fun state bits => advance (bits,state)) state).2,
      a.size≤S+2*bits.length := by
  induction bits generalizing state S with
  | nil => simpa using hx
  | cons b bs ih =>
    have hs := ih (advance (b,state)) (S+2) (advance_growth state b S hx).2
    intro a ha
    exact (hs a ha).trans_eq (by simp only [List.length_cons]; omega)

theorem polynomial_walkWords : PolynomialTime walkWordsRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_advance (20*(X+1)^2)
  intro bits state pre post he
  let S := weight (bits,state)
  let out := pre.foldl (fun state bits => advance (bits,state)) state
  have hd : weight state≤S := weight_snd (bits,state)
  have hp : pre.length≤S := (list_length_le_weight pre).trans
    ((weight_prefix he).trans (weight_fst (bits,state)))
  have hxs : weight state.2≤S := (weight_snd state).trans hd
  have hn : state.2.length≤S := (list_length_le_weight _).trans hxs
  have hi : ∀ a∈state.2,a.size≤S := fun a ha =>
    (size_le_weight a).trans ((weight_mem ha).trans hxs)
  have hs := fold_sizes pre state S hi
  have ht := fold_frame pre state
  have hw : weight out.2≤out.2.length*(4*(S+2*pre.length)+2)+1 := by
    have h := weight_map_bound (f := id) (as := out.2) (N := 4*(S+2*pre.length)+1)
      (fun a ha => (weight_nat_le a).trans (by have h := hs a ha; omega))
    simpa only [List.map_id_fun,id_eq,Nat.add_assoc] using h
  have hf : weight out.1≤S := by
    rw [ht.1]
    exact (weight_fst state).trans hd
  have hl : out.2.length≤S := ht.2.trans_le hn
  have hmul : out.2.length*(4*(S+2*pre.length)+2)≤S*(12*S+2) :=
    Nat.mul_le_mul hl (by omega)
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change weight out≤20*(S+1)^2
  have hweight : weight out=1+weight out.1+weight out.2 := by
    change weight (out.1,out.2)=1+weight out.1+weight out.2
    exact weight_prod _ _
  nlinarith

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FirstSuccess

noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : State :=
  ((K,(((A.d,A.W),(C,a)),
    RootedDemandProgram.data A (ForestCountIdentification.smallX A.small z)
      (fun i j => A.b i j-ForestCountIdentification.smallY A.small z i j))),gridNatCode v)

lemma advance_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (bits : Fin (CompanionOracleDensity.oracleStepBits A C) → Bool) :
    advance (List.ofFn bits,data A C a K z v)=
      data A C a K z (RootedCatalogGrid.bitStep A C a z v bits) := by
  unfold advance data
  apply Prod.ext
  · rfl
  · exact RootedOracleStepProgram.wordStep_data A C a K hC z v bits

theorem walkWords_ofFn (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (N : ℕ) (bits : Fin N → Fin (CompanionOracleDensity.oracleStepBits A C) → Bool) :
    walkWords (data A C a K z v,List.ofFn (fun i => List.ofFn (bits i)))=
      data A C a K z (wordWalk (RootedCatalogGrid.bitStep A C a z) v N bits) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    unfold walkWords at ih ⊢
    rw [List.ofFn_succ',List.concat_eq_append,List.foldl_append]
    change advance (List.ofFn (bits (Fin.last N)),
      (List.ofFn (fun i => List.ofFn ((Fin.init bits) i))).foldl
        (fun state bits => advance (bits,state)) (data A C a K z v))=_
    rw [ih (Fin.init bits)]
    exact advance_data A C a K hC z _ _

end
end ContingencyTables.RootedOracleWalkProgram

end OAI
