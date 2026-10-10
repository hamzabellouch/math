import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionInitialization
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredRowCells

namespace OAI

/-! # Constant live scratch for a compression row's three binary searches -/

namespace LowSpaceSubsetSum.CompressionRowCells

def low (x : ℤ) : (ℤ × ℕ) × ℕ := ((x%1,3),8)
def high (P x : ℤ) : (ℤ × ℕ) × ℕ := ((x%P,3),8)

def run (right : Array ℤ) (P : ℤ) (hs : FilteredRow.PrimarySorted right id 1)
    (mode : FilteredStream.Mode) (x : ℤ) : (PairCursor.State ℤ right.size × ℕ) × ℕ :=
  let k := FilteredStream.steps right.size
  let rr := MeasuredRowCells.range right low ((0-x)%1) k hs
    (FilteredStream.steps_sufficient right.size)
  let q := match mode with
    | .direct => MeasuredRowCells.start right rr.1.1 (high P) P (x%P) k false
    | .complementary t => MeasuredRowCells.start right rr.1.1 (high P) P ((t-x)%P) k true
  ((⟨x,q.1.1⟩,1+rr.1.2+q.1.2+4),rr.2+q.2+32)

theorem value (right : Array ℤ) (P : ℤ) (hs : FilteredRow.PrimarySorted right id 1)
    (mode : FilteredStream.Mode) (x : ℤ) :
    (run right P hs mode x).1 = CompressionInitialization.row right P hs mode x := by
  have h := MeasuredRowCells.range_value right low ((0-x)%1)
    (FilteredStream.steps right.size) hs (FilteredStream.steps_sufficient right.size)
  have hv := congrArg Prod.fst h
  have hw := congrArg Prod.snd h
  cases mode <;>
    simp only [run, MeasuredRowCells.start_value, hv, hw, Bool.false_eq_true, ↓reduceIte] <;> rfl

theorem cells (right : Array ℤ) (P : ℤ) (hs : FilteredRow.PrimarySorted right id 1)
    (mode : FilteredStream.Mode) (x : ℤ) : (run right P hs mode x).2 ≤ 200 := by
  let rr := MeasuredRowCells.range right low ((0-x)%1) (FilteredStream.steps right.size) hs
    (FilteredStream.steps_sufficient right.size)
  have hr := MeasuredRowCells.range_cells right low ((0-x)%1)
    (FilteredStream.steps right.size) 8 hs (FilteredStream.steps_sufficient right.size)
    (fun _ => le_rfl)
  change rr.2 ≤ 80 at hr
  cases mode with
  | direct =>
    have hq := MeasuredRowCells.start_cells right rr.1.1 (high P) P (x%P)
      (FilteredStream.steps right.size) 8 false (fun _ => le_rfl)
    change rr.2+(MeasuredRowCells.start right rr.1.1 (high P) P (x%P)
      (FilteredStream.steps right.size) false).2+32 ≤ _
    omega
  | complementary t =>
    have hq := MeasuredRowCells.start_cells right rr.1.1 (high P) P ((t-x)%P)
      (FilteredStream.steps right.size) 8 true (fun _ => le_rfl)
    change rr.2+(MeasuredRowCells.start right rr.1.1 (high P) P ((t-x)%P)
      (FilteredStream.steps right.size) true).2+32 ≤ _
    omega

end LowSpaceSubsetSum.CompressionRowCells

end OAI
