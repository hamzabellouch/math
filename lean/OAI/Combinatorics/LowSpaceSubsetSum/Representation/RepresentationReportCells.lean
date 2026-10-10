import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredEncodingCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationEmitCells

namespace OAI

/-! # The concrete parent reporter, including key and dictionary scratch -/

namespace LowSpaceSubsetSum.RepresentationReportCells

variable {n : ℕ}

def report (I : Instance n) (F : IndexedMask n) (C : ℕ)
    (x y : LeafRecord n × LeafRecord n) (r : StoredEntry.Dictionary I C) :
    ((StoredEntry.Dictionary I C × Bool) × ℕ) × ℕ :=
  let found := RepresentationEmitCells.emit I F x y
  match found.1.1 with
  | none => (((r, false), found.1.2 + 4), found.2 + 8)
  | some z =>
    let out := StoredEncodingCells.feed I C z r
    (((out.1.1, false), found.1.2 + out.1.2 + 5),
      max found.2 (out.2 + StoredEntry.cells z + 12))

theorem report_value (I : Instance n) (F : IndexedMask n) (C : ℕ)
    (x y : LeafRecord n × LeafRecord n) (r : StoredEntry.Dictionary I C) :
    (report I F C x y r).1 = StoredEntry.report I C (CountedRepresentationEmit.emit I F) x y r := by
  unfold report StoredEntry.report CountedDictionaryCallback.callback
  simp only [RepresentationEmitCells.emit_value, StoredEncodingCells.feed_value]
  cases he : (CountedRepresentationEmit.emit I F x y).1 <;> rfl

theorem report_cells (I : Instance n) (F : IndexedMask n) (C : ℕ)
    (x y : LeafRecord n × LeafRecord n) (r : StoredEntry.Dictionary I C) :
    (report I F C x y r).2 ≤ 200 * inputScale I + 2 * (C + 1) + 200 := by
  have he := RepresentationEmitCells.emit_cells I F x y
  have hn : n + 1 ≤ inputScale I := by unfold inputScale; omega
  unfold report
  dsimp only
  cases hout : (RepresentationEmitCells.emit I F x y).1.1 with
  | none => dsimp only; omega
  | some z =>
    have hf := StoredEncodingCells.feed_cells I C z r
    have hz := z.cells_le
    dsimp only
    omega

theorem report_scale (I : Instance n) (F : IndexedMask n) (C : ℕ)
    (x y : LeafRecord n × LeafRecord n) (r : StoredEntry.Dictionary I C) (hn : 10000 ≤ n) :
    (report I F C x y r).2 ≤ inputScale I ^ 2 * (C + 1) := by
  have h := report_cells I F C x y r
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have h₁ : 200 * inputScale I + 202 ≤ inputScale I ^ 2 := by nlinarith only [hu, hn]
  have h₂ := Nat.mul_le_mul_right (C + 1) h₁
  exact h.trans (by nlinarith only [h₂])

end LowSpaceSubsetSum.RepresentationReportCells

end OAI
