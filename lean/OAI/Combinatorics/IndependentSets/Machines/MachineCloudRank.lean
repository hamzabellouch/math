import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineCloudCount

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineCloudRank

open Turing MachineComposition MachineCloudCount

variable {σ : Type}

@[simp] theorem update_memory_spare (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .spare x = memory a b c d e x := by
  funext k
  cases k <;> rfl

inductive RankLabel
  | queryFirst | querySecond | querySkip | tableFirst | tableSecond
  | headerFirst | headerSecond | row | field | restore | done
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def rankSkip (i : Nat) : RankLabel :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .row

def rankProgram : RankLabel → TM2.Stmt Alphabet RankLabel (State σ)
  | .queryFirst => Reduction.MachineTransfer.loopAt
      .target .scratch id false .queryFirst (some .querySecond)
  | .querySecond => MachineCopy.forkLoop
      .scratch .target .spare false .querySecond (some .querySkip)
  | .querySkip => MachineLookup.discard .spare .querySkip .tableFirst
  | .tableFirst => Reduction.MachineTransfer.loopAt
      .original .scratch id false .tableFirst (some .tableSecond)
  | .tableSecond => MachineCopy.forkLoop
      .scratch .original .work false .tableSecond (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .row
  | .row => MachineUnaryCounter.guard .spare .field .done
  | .field => fieldLoop .field .restore
  | .restore => Reduction.MachineTransfer.loopAt
      .scratch .target id false .restore (some (rankSkip 0))
  | .skip i => MachineLookup.discard .work (.skip i) (rankSkip (i.val + 1))
  | .done => .halt

theorem rankProgram_skip {i : Nat} (hi : i < 4097) :
    rankProgram (σ := σ) (rankSkip i) =
      MachineLookup.discard .work (rankSkip i) (rankSkip (i + 1)) := by
  simp only [rankSkip, dite_eq_left hi, rankProgram]

theorem rowGuard_succ (original work target scratch count fuelSuffix : List Bool)
    (k : Nat) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (rankProgram (σ := σ))
      ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord (k + 1) ++ fuelSuffix)⟩ =
      some ⟨some .field, ((ambient, flag), none),
        memory original work target scratch count (encodeWord k ++ fuelSuffix)⟩ := by
  change some (TM2.stepAux (rankProgram .row) _ _) = _
  simp [rankProgram, MachineUnaryCounter.guard, TM2.stepAux, encodeWord,
    List.replicate_succ]

theorem rowGuard_zero (original work target scratch count fuelSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (rankProgram (σ := σ))
      ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ =
      some ⟨some .done, ((ambient, flag), none),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ := rfl

theorem zeroRowsTrace (original work target scratch count fuelSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[2]
      (some ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩) =
      some ⟨none, ((ambient, flag), none),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ := by
  rw [Function.iterate_succ_apply]
  change advance (TM2.step (rankProgram (σ := σ)))
    (TM2.step rankProgram ⟨some .row, ((ambient, flag), register),
      memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩) = _
  rw [rowGuard_zero]
  rfl

theorem rankRowTrace (r : Row) (hwidth : r.2.length = 4097) (v k : Nat)
    (original suffix targetSuffix fuelSuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[rowTime v r]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
          [] count (encodeWord (k + 1) ++ fuelSuffix)⟩) =
      some ⟨some .row, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if r.1 = v then 1 else 0) true ++ count)
          (encodeWord k ++ fuelSuffix)⟩ := by
  have hfield := preservingFieldTrace RankLabel.field RankLabel.restore (rankSkip 0)
    rankProgram rfl rfl original (encodeWords r.2 ++ suffix) targetSuffix count
    (encodeWord k ++ fuelSuffix) r.1 v ambient none
  have hskip := discardFieldsTrace rankSkip (rankProgram (σ := σ)) r.2 0
    (by intro i hi; simpa only [Nat.zero_add] using rankProgram_skip (hwidth ▸ hi))
    original suffix (encodeWord v ++ targetSuffix) []
    (List.replicate (if r.1 = v then 1 else 0) true ++ count)
    (encodeWord k ++ fuelSuffix) ambient false none
  have hnonempty : r.2 ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, rankSkip, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false] at hskip
  have htime : rowTime v r = (encodeWords r.2).length + (r.1 + min r.1 v + 2) + 1 := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [htime, Function.iterate_succ_apply]
  change (advance (TM2.step (rankProgram (σ := σ))))^[
      (encodeWords r.2).length + (r.1 + min r.1 v + 2)]
    (TM2.step rankProgram ⟨some .row, ((ambient, false), register),
      memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
        [] count (encodeWord (k + 1) ++ fuelSuffix)⟩) = _
  rw [rowGuard_succ, Function.iterate_add_apply]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hfield]
  exact hskip

def prefixTime (v : Nat) : List Row → Nat
  | [] => 2
  | r :: rs => prefixTime v rs + rowTime v r

theorem prefixTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097) (v : Nat)
    (original suffix targetSuffix fuelSuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[prefixTime v rs]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rs.flatMap rowWords) ++ suffix)
          (encodeWord v ++ targetSuffix) [] count (encodeWord rs.length ++ fuelSuffix)⟩) =
      some ⟨none, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) (encodeWord 0 ++ fuelSuffix)⟩ := by
  induction rs generalizing count register with
  | nil =>
      simpa only [prefixTime, List.flatMap_nil, encodeWords, List.nil_append,
        List.length_nil, rowsHits, List.replicate_zero] using
        zeroRowsTrace original suffix (encodeWord v ++ targetSuffix) [] count fuelSuffix
          ambient false register
  | cons r rs ih =>
      have hrow := rankRowTrace r (hwidth r (by simp)) v rs.length original
        (encodeWords (rs.flatMap rowWords) ++ suffix) targetSuffix fuelSuffix count ambient register
      have hrest := ih (by intro x hx; exact hwidth x (by simp [hx]))
        (List.replicate (if r.1 = v then 1 else 0) true ++ count) none
      simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.append_assoc,
        List.length_cons]
      rw [Function.iterate_add_apply, hrow]
      simpa only [rowsHits, ← List.append_assoc, List.replicate_append_replicate,
        Nat.add_comm] using hrest

theorem prefixTime_le (v : Nat) (rs : List Row) :
    prefixTime v rs ≤ 3 * (encodeWords (rs.flatMap rowWords)).length + 2 := by
  induction rs with
  | nil => simp only [prefixTime, List.flatMap_nil, encodeWords, List.length_nil,
      Nat.mul_zero, Nat.zero_add, le_refl]
  | cons r rs ih =>
      have hr := rowTime_le v r
      simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.length_append]
      omega

def queryWord (v k : Nat) (suffix : List Bool) : List Bool :=
  encodeWord v ++ (encodeWord k ++ suffix)

theorem encoded_rows_split (rs : List Row) (k : Nat) :
    encodeWords (rs.flatMap rowWords) =
      encodeWords ((rs.take k).flatMap rowWords) ++
        encodeWords ((rs.drop k).flatMap rowWords) := by
  have h := congrArg (fun xs : List Row => encodeWords (xs.flatMap rowWords))
    (List.take_append_drop k rs)
  simpa only [List.flatMap_append, encodeWords_append] using h.symm

def rankSteps (n m v k : Nat) (rs : List Row) (querySuffix : List Bool) : Nat :=
  2 * ((queryWord v k querySuffix).length + 1) + (v + 1) +
    2 * ((inputWord n m rs).length + 1) + (n + 1) + (m + 1) +
      prefixTime v (rs.take k)

theorem rankTrace (n m v k : Nat) (rs : List Row) (hk : k ≤ rs.length)
    (hwidth : ∀ r ∈ rs, r.2.length = 4097) (querySuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[rankSteps n m v k rs querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (inputWord n m rs) (encodeWords ((rs.drop k).flatMap rowWords))
          (queryWord v k querySuffix) []
          (List.replicate (rowsHits v (rs.take k)) true ++ count)
          (encodeWord 0 ++ querySuffix)⟩ := by
  have hquery := MachineCopy.copyTrace Tape.target Tape.spare Tape.scratch
    (by decide) (by decide) (by decide) false RankLabel.queryFirst RankLabel.querySecond
    (some RankLabel.querySkip) rankProgram rfl rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count [])
    rfl (ambient, false) register
  simp only [memory_target, memory_spare, List.append_nil, update_memory_spare] at hquery
  have hquerySkip := MachineLookup.discardTrace Tape.spare RankLabel.querySkip RankLabel.tableFirst
    rankProgram rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count (queryWord v k querySuffix))
    v (encodeWord k ++ querySuffix) rfl (ambient, false) none
  simp only [update_memory_spare] at hquerySkip
  have hcopy := MachineCopy.copyTrace Tape.original Tape.work Tape.scratch
    (by decide) (by decide) (by decide) false RankLabel.tableFirst RankLabel.tableSecond
    (some RankLabel.headerFirst) rankProgram rfl rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count
      (encodeWord k ++ querySuffix)) rfl (ambient, false) none
  simp only [memory_original, memory_work, List.append_nil, update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace Tape.work RankLabel.headerFirst RankLabel.headerSecond
    rankProgram rfl
    (memory (inputWord n m rs) (inputWord n m rs) (queryWord v k querySuffix) [] count
      (encodeWord k ++ querySuffix))
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (inputWord_eq n m rs) (ambient, false) none
  simp only [update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace Tape.work RankLabel.headerSecond RankLabel.row
    rankProgram rfl
    (memory (inputWord n m rs) (encodeWord m ++ encodeWords (rs.flatMap rowWords))
      (queryWord v k querySuffix) [] count (encodeWord k ++ querySuffix))
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [update_memory_work] at hsecond
  have hprefix := prefixTrace (rs.take k)
    (by intro r hr; exact hwidth r (List.mem_of_mem_take hr)) v
    (inputWord n m rs) (encodeWords ((rs.drop k).flatMap rowWords))
    (encodeWord k ++ querySuffix) querySuffix count ambient none
  have htake : (rs.take k).length = k := by
    simp only [List.length_take, Nat.min_eq_left hk]
  rw [htake, ← encoded_rows_split rs k] at hprefix
  rw [show rankSteps n m v k rs querySuffix = prefixTime v (rs.take k) +
      ((m + 1) + ((n + 1) + (2 * ((inputWord n m rs).length + 1) +
        ((v + 1) + 2 * ((queryWord v k querySuffix).length + 1))))) by
      unfold rankSteps; omega,
    Function.iterate_add_apply _ (prefixTime v (rs.take k)),
    Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
    Function.iterate_add_apply _ (2 * ((inputWord n m rs).length + 1)),
    Function.iterate_add_apply _ (v + 1), hquery, hquerySkip, hcopy, hfirst, hsecond]
  exact hprefix

theorem rankSteps_le (n m v k : Nat) (rs : List Row) (querySuffix : List Bool) :
    rankSteps n m v k rs querySuffix ≤
      5 * (inputWord n m rs).length + 3 * (queryWord v k querySuffix).length + 6 := by
  have hprefix := prefixTime_le v (rs.take k)
  have hsplit := congrArg List.length (encoded_rows_split rs k)
  simp only [List.length_append] at hsplit
  have hinput := inputWord_length n m rs
  have hquery : v + 1 ≤ (queryWord v k querySuffix).length := by
    simp only [queryWord, List.length_append, encodeWord_length]
    omega
  unfold rankSteps
  omega

theorem idxOf_filter_prefix {α : Type*} [BEq α] [LawfulBEq α]
    (p : α → Bool) (a : α) (hp : p a = true) :
    ∀ xs : List α, a ∈ xs →
      (xs.filter p).idxOf a = ((xs.take (xs.idxOf a)).filter p).length := by
  classical
  intro xs
  induction xs with
  | nil => intro ha; simp at ha
  | cons b xs ih =>
      intro ha
      by_cases hba : b = a
      · subst b
        simp [hp]
      · have ha' : a ∈ xs := by simpa [hba, Ne.symm hba] using ha
        cases hb : p b <;>
          simp [hba, hb, ih ha']

open IndependentSetsGames.Foundations.PCP

theorem tableRows_length (t : GraphTables.Table) : (tableRows t).length = t.darts := by
  simp only [tableRows, List.length_map, GraphTables.rowList_length]

theorem cloudRank_eq_prefix_count (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) :
    (PreprocessingCloudIndex.cloudRank t v e).val =
      rowsHits v.val ((tableRows t).take e.val.val) := by
  have hindex := idxOf_filter_prefix (fun x : Fin t.darts => decide (t.rows[x].tail = v))
    e.val (by simpa using e.property) (List.finRange t.darts) (List.mem_finRange e.val)
  simp only [List.idxOf_finRange] at hindex
  change (PreprocessingCloudIndex.cloudDarts t v).idxOf e.val = _
  unfold PreprocessingCloudIndex.cloudDarts
  rw [hindex, rowsHits_eq_filter]
  simp only [tableRows, rowList_eq_finRange_map, ← List.map_take, List.filter_map,
    List.length_map, Function.comp_def, Fin.val_inj]

theorem cloudRankTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v)
    (querySuffix countSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[
        rankSteps t.vertices t.darts v.val e.val.val (tableRows t) querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        memory (GraphTables.tableBits t) [] (queryWord v.val e.val.val querySuffix) []
          (encodeWord 0 ++ countSuffix) []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t)
          (encodeWords (((tableRows t).drop e.val.val).flatMap rowWords))
          (queryWord v.val e.val.val querySuffix) []
          (encodeWord (PreprocessingCloudIndex.cloudRank t v e).val ++ countSuffix)
          (encodeWord 0 ++ querySuffix)⟩ := by
  have hk : e.val.val ≤ (tableRows t).length := by
    rw [tableRows_length]
    exact e.val.isLt.le
  have h := rankTrace t.vertices t.darts v.val e.val.val (tableRows t) hk
    (tableRows_width t) querySuffix (encodeWord 0 ++ countSuffix) ambient register
  rw [tableRows_input, ← cloudRank_eq_prefix_count t v e, ← List.append_assoc,
    replicate_encodeWord, Nat.add_zero] at h
  exact h

def cloudRankInTime (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v)
    (querySuffix countSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (rankProgram (σ := σ)))
      ⟨some .queryFirst, ((ambient, false), register),
        memory (GraphTables.tableBits t) [] (queryWord v.val e.val.val querySuffix) []
          (encodeWord 0 ++ countSuffix) []⟩
      (some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t)
          (encodeWords (((tableRows t).drop e.val.val).flatMap rowWords))
          (queryWord v.val e.val.val querySuffix) []
          (encodeWord (PreprocessingCloudIndex.cloudRank t v e).val ++ countSuffix)
          (encodeWord 0 ++ querySuffix)⟩)
      (5 * (GraphTables.tableBits t).length +
        3 * (queryWord v.val e.val.val querySuffix).length + 6) where
  steps := rankSteps t.vertices t.darts v.val e.val.val (tableRows t) querySuffix
  evals_in_steps := cloudRankTrace t v e querySuffix countSuffix ambient register
  steps_le_m := by
    simpa only [tableRows_input] using
      rankSteps_le t.vertices t.darts v.val e.val.val (tableRows t) querySuffix

end IndependentSetsGames.Foundations.Complexity.MachineCloudRank

end OAI
