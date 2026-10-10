import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationWeightedReader
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionProgram

namespace OAI

/-! # Measured shared-array readers for the compression branch -/

namespace LowSpaceSubsetSum.CompressionReader

abbrev key (P : ℤ) (mode : FilteredStream.Mode) (p : ℤ × ℤ) : ℤ × ℕ :=
  (FilteredStream.key id id P mode p, 6)

abbrev State (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) (d : ℕ) :=
  MergedReader.State (FilteredStream.key id id P mode) (FilteredStream.view (α := ℤ) right) d

private theorem row_reader (right : Array ℤ) :
    RowMerge.IsReader (fun s => (FilteredStream.countedRead right s).1)
      (FilteredStream.view (α := ℤ) right) := by
  simpa only [FilteredStream.countedRead_value] using (FilteredStream.reader (α := ℤ) right)

def read (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : State P mode right d) : Option (ℤ × State P mode right d) × ℕ :=
  let out := MergedReader.measuredNext (key P mode) (FilteredStream.countedRead right)
    (FilteredStream.view right) (row_reader right) s
  (out.1.map (fun p => (p.1.1 + p.1.2, p.2)), out.2 + 2)

theorem read_value (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : State P mode right d) :
    (read P mode right s).1 =
      mapReader (fun p : ℤ × ℤ => p.1 + p.2)
        (MergedReader.next (FilteredStream.key id id P mode)
          (FilteredStream.read right) (FilteredStream.view right) (FilteredStream.reader right)) s := by
  have hr : (fun s => (FilteredStream.countedRead (α := ℤ) right s).1) =
      FilteredStream.read (α := ℤ) right :=
    funext (FilteredStream.countedRead_value right)
  have hv := MergedReader.measuredNext_value (key P mode) (FilteredStream.countedRead right)
    (FilteredStream.view right) (row_reader right) s
  change _ = MergedReader.next (FilteredStream.key id id P mode)
    (fun s => (FilteredStream.countedRead right s).1) (FilteredStream.view right) _ s at hv
  have hv' : (MergedReader.measuredNext (key P mode) (FilteredStream.countedRead right)
      (FilteredStream.view right) (row_reader right) s).1 =
      MergedReader.next (FilteredStream.key id id P mode) (FilteredStream.read right)
        (FilteredStream.view right) (FilteredStream.reader right) s := by
    simpa only [hr] using hv
  exact congrArg (Option.map (fun p => (p.1.1 + p.1.2, p.2))) hv'

theorem read_work (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : State P mode right d) : (read P mode right s).2 ≤ 20 * d + 36 := by
  have h := MergedReader.measuredNext_work (key P mode) (FilteredStream.countedRead right)
    (FilteredStream.view right) (row_reader right) s 6 24
    (fun _ => le_rfl) (FilteredStream.countedRead_work right)
  change _ + 2 ≤ _
  omega

theorem read_scale {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : State P mode right d) (hd : d ≤ n) :
    (read P mode right s).2 ≤ inputScale I ^ 2 := by
  have h := read_work P mode right s
  have hu : n ≤ inputScale I := by unfold inputScale; omega
  nlinarith only [h, hd, hn, hu]

def scalarKey (P : ℤ) (mode : FilteredStream.Mode) (x : ℤ) : ℤ × ℕ :=
  match mode with
  | .direct => (x % P, 2)
  | .complementary t => ((t - x) % P, 3)

theorem scalarKey_work (P : ℤ) (mode : FilteredStream.Mode) (x : ℤ) :
    (scalarKey P mode x).2 ≤ 3 := by cases mode <;> simp only [scalarKey] <;> omega

def snapshot (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : State P mode right d) : State P mode right d × ℕ :=
  let out := Tournament.countedCopy 10 s.tree
  have he : out.1 = s.tree := Tournament.countedCopy_value _ _
  (⟨out.1, he.symm ▸ s.valid, he.symm ▸ s.aligned, he.symm ▸ s.sorted⟩, out.2)

theorem snapshot_value (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : State P mode right d) : (snapshot P mode right s).1 = s := by
  cases s
  simp only [snapshot, Tournament.countedCopy_value]

theorem snapshot_work (P : ℤ) (mode : FilteredStream.Mode) (right : Array ℤ) {d : ℕ}
    (s : State P mode right d) : (snapshot P mode right s).2 ≤ 10 * 2 ^ (d + 1) := by
  have he := Tournament.nodes_exact s.tree
  simp only [snapshot, Tournament.countedCopy_cells]
  exact Nat.mul_le_mul_left _ (by omega)

theorem groupRead_value {n : ℕ} (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (i : Fin 4) (mode : FilteredStream.Mode)
    (s : D.GroupState e q i mode) :
    (read q.val mode (D.storedRightArray e q i) s).1 = D.groupRead e q i mode s :=
  read_value _ _ _ _

end LowSpaceSubsetSum.CompressionReader

end OAI
