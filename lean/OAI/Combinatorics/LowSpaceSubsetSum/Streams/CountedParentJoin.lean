import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedRepresentationEmit
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredDictionaryJoin

namespace OAI

/-! # Concrete stored-mask parent join

The readers, modular keys, validity tests, signed sums, dictionary encoding
and mutable snapshots below execute their counted implementations. The bound
uses the counters of that same stopped run, including invalid reported tuples.
-/

namespace LowSpaceSubsetSum.CountedParentJoin

variable {n : ℕ}

abbrev Child (n : ℕ) := LeafRecord n × LeafRecord n

def cells (x : Child n) : ℕ :=
  x.1.top.indices.length + x.1.localMask.indices.length + x.1.background.indices.length +
  x.2.top.indices.length + x.2.localMask.indices.length + x.2.background.indices.length + 4

theorem cells_le (x : Child n) : cells x ≤ 6 * n + 4 := by
  have h1 := x.1.top.length_le
  have h2 := x.1.localMask.length_le
  have h3 := x.1.background.length_le
  have h4 := x.2.top.length_le
  have h5 := x.2.localMask.length_le
  have h6 := x.2.background.length_le
  unfold cells
  omega

abbrev State (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (right : Array (LeafRecord n)) (d : ℕ) :=
  MergedReader.State (fun x => (RepresentationKeys.pairKey I F P mode x).1)
    (FilteredStream.view right) d

/-- Deep-copy the mutable tournament; the immutable right array is shared. -/
def snapshot (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (right : Array (LeafRecord n)) {d : ℕ}
    (s : State I F P mode right d) : State I F P mode right d × ℕ :=
  let out := Tournament.countedCopy (12 * n + 32) s.tree
  have he : out.1 = s.tree := Tournament.countedCopy_value _ _
  (⟨out.1, he.symm ▸ s.valid, he.symm ▸ s.aligned, he.symm ▸ s.sorted⟩, out.2)

theorem snapshot_value (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (right : Array (LeafRecord n)) {d : ℕ}
    (s : State I F P mode right d) : (snapshot I F P mode right s).1 = s := by
  cases s
  simp only [snapshot, Tournament.countedCopy_value]

theorem snapshot_work (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (right : Array (LeafRecord n)) {d : ℕ}
    (s : State I F P mode right d) :
    (snapshot I F P mode right s).2 ≤ (12 * n + 32) * 2 ^ (d + 1) := by
  have he := Tournament.nodes_exact s.tree
  simp only [snapshot, Tournament.countedCopy_cells]
  exact Nat.mul_le_mul_left _ (by omega)

private theorem report_polynomial {n u : ℕ} (hnu : n ≤ u) (hu : 10000 ≤ u) :
    u ^ 3 + 12 * u ^ 2 + (n + 2) + 2 * (3 * u + 1) + 19 ≤ u ^ 4 := by
  have hu1 : 1 ≤ u := by omega
  have h12 : u ≤ u ^ 2 := by simpa using Nat.pow_le_pow_right hu1 (by decide : 1 ≤ 2)
  have h23 : u ^ 2 ≤ u ^ 3 := Nat.pow_le_pow_right hu1 (by decide)
  have hlow : (n + 2) + 2 * (3 * u + 1) + 19 ≤ 30 * u ^ 3 := by omega
  have hscale : 43 * u ^ 3 ≤ u ^ 4 := by
    calc
      _ ≤ u * u ^ 3 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' u 3).symm
  omega

theorem report_work (I : Instance n) (F : IndexedMask n) (C : ℕ)
    (x y : Child n) (r : StoredEntry.Dictionary I C) (hn : 10000 ≤ n) :
    (StoredEntry.report I C (CountedRepresentationEmit.emit I F) x y r).2 ≤
      inputScale I ^ 4 := by
  have h := StoredEntry.report_work I C (inputScale I ^ 3)
    (CountedRepresentationEmit.emit I F)
    (fun x y => CountedRepresentationEmit.emit_scale I F x y hn) x y r
  have hw := (WeightEncoding.widths_le I).2
  have hnu : n ≤ inputScale I := by unfold inputScale; omega
  exact h.trans ((Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hw) _) 19).trans
      (report_polynomial hnu (hn.trans hnu)))

def run (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (fuel₁ fuel₂ control : ℕ) (s₁ : State I F P .direct right₁ d₁)
    (s₂ : State I F P (.complementary t) right₂ d₂) :=
  StoredDictionaryJoin.run I C
    (RepresentationKeys.read I F P .direct right₁) (RepresentationKeys.pairKey I F P .direct)
    (RepresentationKeys.read I F P (.complementary t) right₂)
    (RepresentationKeys.pairKey I F P (.complementary t)) cells
    (CountedRepresentationEmit.emit I F) (snapshot I F P (.complementary t) right₂)
    B fuel₁ fuel₂ control s₁ s₂

private theorem query_polynomial {n u : ℕ} (hnu : n ≤ u) (hu : 10000 ≤ u) :
    2 * (u ^ 5 + u ^ 5 + u ^ 3 + u ^ 3 + (6 * n + 4)) + 131 ≤ u ^ 6 := by
  have hu1 : 1 ≤ u := by omega
  have h15 : u ≤ u ^ 5 := by simpa using Nat.pow_le_pow_right hu1 (by decide : 1 ≤ 5)
  have h35 : u ^ 3 ≤ u ^ 5 := Nat.pow_le_pow_right hu1 (by decide)
  have hconst : 139 ≤ 139 * u ^ 5 := by
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hscale : 160 * u ^ 5 ≤ u ^ 6 := by
    calc
      _ ≤ u * u ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' u 5).symm
  omega

/-- Work is charged to the actual query/report/snapshot counters, on every
run, without a successful sampling or valid-record hypothesis. -/
theorem run_work (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (right₁ right₂ : Array (LeafRecord n)) {d₁ d₂ : ℕ}
    (fuel₁ fuel₂ control : ℕ) (s₁ : State I F P .direct right₁ d₁)
    (s₂ : State I F P (.complementary t) right₂ d₂)
    (hn : 10000 ≤ n) (hd₁ : d₁ ≤ n) (hd₂ : d₂ ≤ n)
    (hcopy : (12 * n + 32) * 2 ^ (d₂ + 1) ≤ B) :
    let out := run I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂
    out.2 ≤ inputScale I ^ 6 * (out.1.state.queries + out.1.state.reports + 1) +
      B * out.1.state.copies := by
  let read₁ := RepresentationKeys.read I F P .direct right₁ (d := d₁)
  let read₂ := RepresentationKeys.read I F P (.complementary t) right₂ (d := d₂)
  let key₁ := RepresentationKeys.pairKey I F P .direct
  let key₂ := RepresentationKeys.pairKey I F P (.complementary t)
  let report := StoredEntry.report I C (CountedRepresentationEmit.emit I F)
  let clone := snapshot I F P (.complementary t) right₂ (d := d₂)
  let out := run I F P t C B right₁ right₂ fuel₁ fuel₂ control s₁ s₂
  have hc : ∀ s, (clone s).1 = s := snapshot_value I F P (.complementary t) right₂
  have hw := CountedStreamJoin.run_work_queries read₁ key₁ read₂ key₂ cells report clone hc
    (inputScale I ^ 5) (inputScale I ^ 5) (inputScale I ^ 3) (inputScale I ^ 3)
    (6 * n + 4) (inputScale I ^ 4) B
    (fun s => RepresentationKeys.read_scale I F P .direct right₁ s hd₁ hn)
    (fun s => RepresentationKeys.read_scale I F P (.complementary t) right₂ s hd₂ hn)
    (fun x => RepresentationKeys.pairKey_scale I F P .direct x hn)
    (fun y => RepresentationKeys.pairKey_scale I F P (.complementary t) y hn)
    cells_le (fun x y a => report_work I F C x y a hn)
    (fun s => (snapshot_work I F P (.complementary t) right₂ s).trans hcopy)
    B fuel₁ fuel₂ control s₁ s₂ (StoredEntry.empty I C)
  have hv := congrArg StreamJoin.StoppedResult.state
    (CountedStreamJoin.runAcc_value read₁ key₁ read₂ key₂ cells report clone hc
      B fuel₁ fuel₂ control (StreamJoin.start s₁ s₂ (StoredEntry.empty I C)))
  rw [StreamJoin.stoppedAcc_eq] at hv
  change out.1.state = StreamJoin.run _ _ _ _ _ _ _ _ _ _ _ _ at hv
  rw [← hv] at hw
  change out.2 ≤ _ at hw
  change out.2 ≤ inputScale I ^ 6 * (out.1.state.queries + out.1.state.reports + 1) +
    B * out.1.state.copies
  have hnu : n ≤ inputScale I := by unfold inputScale; omega
  have hu : 10000 ≤ inputScale I := hn.trans hnu
  have hq := Nat.mul_le_mul_right out.1.state.queries (query_polynomial hnu hu)
  have hr := Nat.mul_le_mul_right out.1.state.reports
    (Nat.pow_le_pow_right (by omega : 0 < inputScale I) (by decide : 4 ≤ 6))
  have h1 : 1 ≤ inputScale I ^ 6 := Nat.one_le_pow _ _ (by omega)
  simp only [Nat.mul_add, Nat.mul_one]
  omega

end LowSpaceSubsetSum.CountedParentJoin

end OAI
