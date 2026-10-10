import Mathlib
import OAI.Combinatorics.KMedian.Hardness.Analysis
import OAI.Combinatorics.KMedian.Hardness.Encoding

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Binary Binary.Automatic Binary.Automatic.Poly

namespace Raw

def clients (r : Raw) : List ℕ := List.range (r.table.take r.m).length
def sets (r : Raw) : List ℕ := List.range (r.table.take r.n).length

@[fun_prop] theorem clients_poly : Poly clients := by
  unfold clients
  apply Poly.comp Poly.list_indices
  dsimp only [m, table]
  fun_prop

@[fun_prop] theorem sets_poly : Poly sets := by
  unfold sets
  apply Poly.comp Poly.list_indices
  dsimp only [n, table]
  fun_prop

def isCovered (r : Raw) (out : List Bool) (j : ℕ) : Bool :=
  !((r.sets.filter (fun i => (out[r.m+i]?).getD false &&
    (r.table[j*r.n+i]?).getD false)).isEmpty)

@[fun_prop] theorem isCovered_poly : Poly (fun x : (Raw × List Bool) × ℕ =>
    x.1.1.isCovered x.1.2 x.2) := by
  unfold isCovered
  apply Poly.comp Poly.bool_not
  apply Poly.comp Poly.list_empty
  apply Poly.list_filter
  · dsimp only [m, n, table]
    fun_prop
  · exact Poly.comp sets_poly (by fun_prop)

def coveredCount (r : Raw) (out : List Bool) : ℕ :=
  (r.clients.filter (r.isCovered out)).length

@[fun_prop] theorem coveredCount_poly : Poly (fun x : Raw × List Bool =>
    x.1.coveredCount x.2) := by
  unfold coveredCount
  apply Poly.comp Poly.list_length
  exact Poly.list_filter isCovered_poly (Poly.comp clients_poly Poly.fst)

def accepts (q : ℚ) (r : Raw) (out : List Bool) : Bool :=
  decide (3*(r.m : ℚ)-2*(r.coveredCount out : ℚ) < q*r.m)

@[fun_prop] theorem accepts_poly (q : ℚ) : Poly (fun x : Raw × List Bool =>
    accepts q x.1 x.2) := by
  unfold accepts
  dsimp only [m]
  fun_prop

end Raw

namespace Input

theorem clients_raw (C : Input) : C.raw.clients = List.range C.m := by
  have hm : C.m ≤ C.raw.table.length := by
    rw [C.table_length]; exact Nat.le_mul_of_pos_right _ C.n_pos
  simp only [Raw.clients, List.length_take, raw_m, Nat.min_eq_left hm]

theorem sets_raw (C : Input) : C.raw.sets = List.range C.n := by
  have hn : C.n ≤ C.raw.table.length := by
    rw [C.table_length]; exact Nat.le_mul_of_pos_left _ C.m_pos
  simp only [Raw.sets, List.length_take, raw_n, Nat.min_eq_left hn]

theorem mem_selectedMask_iff (C : Input) (out : List Bool) (i : Fin C.n) :
    i ∈ C.selectedMask out ↔ (out[C.m+i.val]?).getD false = true := by
  change i ∈ Finset.filter (fun i => (out[(C.facility i).val]?).getD false = true) Finset.univ ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, facility_val]

theorem isCovered_raw (C : Input) (out : List Bool) (j : Fin C.m) :
    C.raw.isCovered out j.val = decide (j ∈ C.covered (C.selectedMask out)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Raw.isCovered, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem,
    List.mem_filter, C.sets_raw, List.mem_range, Bool.and_eq_true, raw_m, raw_n,
    decide_eq_true_eq, mem_covered, mem_selectedMask_iff]
  constructor
  · rintro ⟨i, hi, hs, hc⟩
    exact ⟨⟨i,hi⟩, hs, by simpa only [← C.table_get j ⟨i,hi⟩] using hc⟩
  · rintro ⟨i,hs,hc⟩
    exact ⟨i.val,i.isLt,hs,by simpa only [C.table_get] using hc⟩

theorem coveredCount_raw (C : Input) (out : List Bool) :
    C.raw.coveredCount out = (C.covered (C.selectedMask out)).card := by
  unfold Raw.coveredCount
  rw [C.clients_raw, RoundingList.range_finRange]
  rw [List.filter_map]
  simp only [Function.comp_def, C.isCovered_raw]
  rw [List.length_map]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange C.m).filter _)]
  congr 1
  ext j
  simp

theorem accepts_raw (C : Input) (q : ℚ) (out : List Bool) :
    Raw.accepts q C.raw out = C.accepts q out := by
  simp only [Raw.accepts, C.coveredCount_raw, raw_m, accepts, comparisonCost]
  rfl

noncomputable def inputRawProgram : Binary.PolyProgram encode enc raw :=
  Raw.parsedProgram.recode encode (fun _ => rfl) (fun C => by rw [C.parse_encode])
attribute [irreducible] inputRawProgram

noncomputable def rawContextProgram :
    Binary.PolyProgram (Binary.encodePair id encode) (Binary.encodePair enc enc)
      (fun x : List Bool × Input => (x.2.raw,x.1)) := by
  let a : Binary.PolyProgram (Binary.encodePair id encode) enc
      (fun x : List Bool × Input => x.2.raw) :=
    (Binary.PolyProgram.snd id encode).comp inputRawProgram
  let b : Binary.PolyProgram (Binary.encodePair id encode) enc
      (fun x : List Bool × Input => x.1) :=
    (Binary.PolyProgram.fst id encode).comp BooleanLists.packProgram
  exact a.fanout b
attribute [irreducible] rawContextProgram

noncomputable def verdictProgram (q : ℚ) :
    Binary.PolyProgram (Binary.encodePair id encode) Complexity.encodeBit
      (fun x : List Bool × Input => x.2.accepts q x.1) :=
  (rawContextProgram.comp (Raw.accepts_poly q).program).congr _
    (fun x => x.2.accepts_raw q x.1)

end Input
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
