import OAI.Combinatorics.ProgressionColoring.BlockCoverage
import OAI.Combinatorics.ProgressionColoring.LiteralLabelRectangles
import OAI.Combinatorics.ProgressionColoring.AnchoredPatternDefinitions
import OAI.Combinatorics.ProgressionColoring.LongPeriodBlocks

namespace OAI

/-!
# Literal cyclic labels on full blocks

An actual cyclic progression is re-anchored at each full block's initial
position. Its two rational paths differ from the local realization only by
integers, so the literal uniform and adaptive labels agree exactly.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.CyclicBlockLabels

theorem fullBlock_end_le (k h : ℕ) (b : Fin (k / h)) : b.val * h + h ≤ k := by
  calc
    b.val * h + h = b.val.succ * h := (Nat.succ_mul _ _).symm
    _ ≤ (k / h) * h := Nat.mul_le_mul_right h (Nat.succ_le_of_lt b.isLt)
    _ ≤ k := Nat.div_mul_le_self k h

/-- The actual cyclic representatives at the beginning of a full block,
with the original displacement vectors retained. -/
def cyclicBlockRealization (q D lambda k h : ℕ)
    (a d : CyclicGroup q D) (u v : Fin D → ℝ) (b : Fin (k / h)) :
    AnchoredPatterns.Realization D where
  x := xRep q D (a + (b.val * h) • d)
  y := yRep q D lambda (a + (b.val * h) • d)
  u := u
  v := v

theorem xRep_block_integer_difference (q D lambda k h : ℕ) (hh : 0 < h)
    (a d : CyclicGroup q D) (u v : Fin D → ℝ) (t : Fin D → Fin h)
    (hX : ∀ j, j < k → ∀ i : Fin D, ∃ e : ℤ,
      xRep q D (a + j • d) i - xRep q D a i -
        (j : ℝ) / h * ((t i).val + u i) = e)
    (b : Fin (k / h)) (z : Fin h) (i : Fin D) :
    ∃ e : ℤ,
      xRep q D (a + (BlockCoverage.blockIndex k h b z).val • d) i -
        AnchoredPatterns.firstPath (cyclicBlockRealization q D lambda k h a d u v b)
          t z i = e := by
  obtain ⟨e, he⟩ := rational_full_block_reanchor
    (k := k) (h := h) (j₀ := b.val * h) (a := ((t i).val : ℤ))
    (y := xRep q D a i) (v := u i)
    (fun j => xRep q D (a + j • d) i) hh (fullBlock_end_le k h b)
    (by
      intro j hj
      simpa only [Int.cast_natCast] using hX j hj i) z
  refine ⟨e, ?_⟩
  simpa only [BlockCoverage.blockIndex_val, AnchoredPatterns.firstPath,
    cyclicBlockRealization, Int.cast_natCast, sub_add_eq_sub_sub] using he

theorem yRep_block_integer_difference (q D lambda k h : ℕ) (hh : 0 < h)
    (a d : CyclicGroup q D) (u v : Fin D → ℝ) (t : Fin D → Fin h)
    (hY : ∀ j, j < k → ∀ i : Fin D, ∃ e : ℤ,
      yRep q D lambda (a + j • d) i - yRep q D lambda a i -
        (j : ℝ) / h * ((lambda : ℝ) * (t i).val + v i) = e)
    (b : Fin (k / h)) (z : Fin h) (i : Fin D) :
    ∃ e : ℤ,
      yRep q D lambda (a + (BlockCoverage.blockIndex k h b z).val • d) i -
        AnchoredPatterns.secondPath (cyclicBlockRealization q D lambda k h a d u v b)
          lambda t z i = e := by
  obtain ⟨e, he⟩ := rational_full_block_reanchor
    (k := k) (h := h) (j₀ := b.val * h)
    (a := (lambda : ℤ) * ((t i).val : ℤ))
    (y := yRep q D lambda a i) (v := v i)
    (fun j => yRep q D lambda (a + j • d) i) hh (fullBlock_end_le k h b)
    (by
      intro j hj
      simpa only [Int.cast_mul, Int.cast_natCast] using hY j hj i) z
  refine ⟨e, ?_⟩
  simpa only [BlockCoverage.blockIndex_val, AnchoredPatterns.secondPath,
    cyclicBlockRealization, Int.cast_mul, Int.cast_natCast, sub_add_eq_sub_sub] using he

/-- The canonical literal cyclic label is exactly the full label of the
local block realization, including every mesh boundary. -/
theorem literalFullLabel_block_eq (mesh : AdaptiveMesh)
    (q D lambda meshN k h : ℕ) (hn : 0 < meshN) (hh : 0 < h)
    (a d : CyclicGroup q D) (u v : Fin D → ℝ) (t : Fin D → Fin h)
    (hX : ∀ j, j < k → ∀ i : Fin D, ∃ e : ℤ,
      xRep q D (a + j • d) i - xRep q D a i -
        (j : ℝ) / h * ((t i).val + u i) = e)
    (hY : ∀ j, j < k → ∀ i : Fin D, ∃ e : ℤ,
      yRep q D lambda (a + j • d) i - yRep q D lambda a i -
        (j : ℝ) / h * ((lambda : ℝ) * (t i).val + v i) = e)
    (b : Fin (k / h)) (z : Fin h) :
    literalFullLabel mesh q D lambda meshN hn
        (a + (BlockCoverage.blockIndex k h b z).val • d) =
      AnchoredPatterns.fullLabel meshN hn mesh
        (cyclicBlockRealization q D lambda k h a d u v b) lambda t z := by
  apply Prod.ext
  · funext i
    exact UniformMesh.label_eq_of_integer_difference meshN hn _ _
      (xRep_block_integer_difference q D lambda k h hh a d u v t hX b z i)
  · funext i
    obtain ⟨e, he⟩ := yRep_block_integer_difference q D lambda k h hh
      a d u v t hY b z i
    have heq : yRep q D lambda (a + (BlockCoverage.blockIndex k h b z).val • d) i =
        AnchoredPatterns.secondPath (cyclicBlockRealization q D lambda k h a d u v b)
          lambda t z i + e := by linarith
    change mesh.meshLabel (yRep q D lambda
      (a + (BlockCoverage.blockIndex k h b z).val • d) i) = _
    rw [heq]
    exact mesh.meshLabel_add_int _ _

/-- Counting a color in the literal positions of a full block is the same
as counting its pullback to the local indices `Fin h`. -/
theorem blockColorCount_eq_local (k h : ℕ)
    (color : Fin k → Bool) (c : Bool) (b : Fin (k / h)) :
    BlockCoverage.blockColorCount k h color c b =
      (Finset.univ.filter fun z : Fin h =>
        color (BlockCoverage.blockIndex k h b z) = c).card := by
  unfold BlockCoverage.blockColorCount BlockCoverage.blockPositions
  rw [Finset.filter_image]
  exact Finset.card_image_of_injective _ (BlockCoverage.blockIndex_injective k h b)

end QuantitativeVanDerWaerden.CyclicBlockLabels

end

end OAI
