import OAI.Combinatorics.Ryser.Geometry.ProjectiveTransformBasic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI

namespace RyserCoveringCounterexample.Incidence

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

def goodW (T : ProjectiveTransform F) (W : Finset (ProjectivePoint F)) :
    Finset (ProjectivePoint F) :=
  W.filter fun w =>
    ¬ ProjectiveIncidence w (T.lines.symm none) ∧
    ¬ ProjectiveIncidence w (T.lines.symm (some (some 0, 0))) ∧
    ¬ ProjectiveIncidence w (T.lines.symm (some (none, 0)))

def affinePart : ProjectivePoint F → Point F
  | Sum.inl z => z
  | Sum.inr _ => (0, 0)

@[simp] theorem affinePart_inl (z : Point F) :
    affinePart (Sum.inl z : ProjectivePoint F) = z := let _ := instDecidableEqF; rfl

@[simp] theorem affinePart_inr (d : Direction F) :
    affinePart (Sum.inr d : ProjectivePoint F) = (0, 0) := let _ := instDecidableEqF; rfl

def coordinateGraph (T : ProjectiveTransform F) (W : Finset (ProjectivePoint F)) :
    Finset (Point F) :=
  (goodW T W).image fun w => affinePart (T.points w)

@[simp] theorem mem_goodW (T : ProjectiveTransform F)
    (W : Finset (ProjectivePoint F)) (w : ProjectivePoint F) :
    w ∈ goodW T W ↔ w ∈ W ∧
      ¬ ProjectiveIncidence w (T.lines.symm none) ∧
      ¬ ProjectiveIncidence w (T.lines.symm (some (some 0, 0))) ∧
      ¬ ProjectiveIncidence w (T.lines.symm (some (none, 0))) := by
  exact Finset.mem_filter

theorem goodW_subset (T : ProjectiveTransform F)
    (W : Finset (ProjectivePoint F)) : goodW T W ⊆ W :=
  Finset.filter_subset _ _

theorem transformed_goodW_affine (T : ProjectiveTransform F)
    (W : Finset (ProjectivePoint F)) {w : ProjectivePoint F}
    (hw : w ∈ goodW T W) :
    T.points w = Sum.inl (affinePart (T.points w)) := by
  have hn : ¬ ProjectiveIncidence (T.points w) none := by
    intro h
    apply ((mem_goodW T W w).mp hw).2.1
    apply (T.incidence w (T.lines.symm none)).mp
    simpa only [Equiv.apply_symm_apply] using h
  cases htw : T.points w with
  | inl z => rfl
  | inr d =>
    exact (hn (by simp only [htw, ProjectiveIncidence])).elim

theorem mem_coordinateGraph_iff (T : ProjectiveTransform F)
    (W : Finset (ProjectivePoint F)) (z : Point F) :
    z ∈ coordinateGraph T W ↔
      ∃ w ∈ goodW T W, T.points w = Sum.inl z := by
  constructor
  · intro hz
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hz
    refine ⟨w, hw, ?_⟩
    simpa only [heq] using transformed_goodW_affine T W hw
  · rintro ⟨w, hw, heq⟩
    apply Finset.mem_image.mpr
    refine ⟨w, hw, ?_⟩
    rw [heq]
    rfl

theorem coordinateGraph_nonzero (T : ProjectiveTransform F)
    (W : Finset (ProjectivePoint F)) {z : Point F}
    (hz : z ∈ coordinateGraph T W) : z.1 ≠ 0 ∧ z.2 ≠ 0 := by
  obtain ⟨w, hw, heq⟩ := (mem_coordinateGraph_iff T W z).mp hz
  have hw' := (mem_goodW T W w).mp hw
  constructor
  · intro hx
    apply hw'.2.2.2
    apply (T.incidence w (T.lines.symm (some (none, 0)))).mp
    simpa [heq, ProjectiveIncidence, Incidence, projection] using hx
  · intro hy
    apply hw'.2.2.1
    apply (T.incidence w (T.lines.symm (some (some 0, 0)))).mp
    simpa [heq, ProjectiveIncidence, Incidence, projection] using hy

theorem card_coordinateGraph_eq_goodW (T : ProjectiveTransform F)
    (W : Finset (ProjectivePoint F)) :
    (coordinateGraph T W).card = (goodW T W).card := by
  apply Finset.card_image_of_injOn
  intro w hw v hv h
  change affinePart (T.points w) = affinePart (T.points v) at h
  apply T.points.injective
  rw [transformed_goodW_affine T W hw, transformed_goodW_affine T W hv]
  exact congrArg (fun z : Point F => (Sum.inl z : ProjectivePoint F)) h

theorem coordinateGraph_card_lower
    (P W : Finset (ProjectivePoint F)) (T : ProjectiveTransform F) (H : ℝ)
    (hWP : W ⊆ P)
    (hcap : ∀ l : ProjectiveLine F,
      ((P.filter fun p => ProjectiveIncidence p l).card : ℝ) ≤ H) :
    (W.card : ℝ) - 3 * H ≤ (coordinateGraph T W).card := by
  let A := P.filter fun p => ProjectiveIncidence p (T.lines.symm none)
  let B := P.filter fun p => ProjectiveIncidence p (T.lines.symm (some (some 0, 0)))
  let C := P.filter fun p => ProjectiveIncidence p (T.lines.symm (some (none, 0)))
  have hcover : W ⊆ ((goodW T W ∪ A) ∪ B) ∪ C := by
    intro w hw
    simp only [Finset.mem_union]
    by_cases hA : ProjectiveIncidence w (T.lines.symm none)
    · exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hWP hw, hA⟩)))
    by_cases hB : ProjectiveIncidence w (T.lines.symm (some (some 0, 0)))
    · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hWP hw, hB⟩))
    by_cases hC : ProjectiveIncidence w (T.lines.symm (some (none, 0)))
    · exact Or.inr (Finset.mem_filter.mpr ⟨hWP hw, hC⟩)
    exact Or.inl (Or.inl (Or.inl ((mem_goodW T W w).mpr ⟨hw, hA, hB, hC⟩)))
  have hnat : W.card ≤ (goodW T W).card + A.card + B.card + C.card := by
    calc
      W.card ≤ (((goodW T W ∪ A) ∪ B) ∪ C).card := Finset.card_le_card hcover
      _ ≤ ((goodW T W ∪ A) ∪ B).card + C.card := Finset.card_union_le _ _
      _ ≤ ((goodW T W ∪ A).card + B.card) + C.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (((goodW T W).card + A.card) + B.card) + C.card :=
        Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
  have hreal := (Nat.cast_le (α := ℝ)).mpr hnat
  simp only [Nat.cast_add] at hreal
  have hA : (A.card : ℝ) ≤ H := hcap (T.lines.symm none)
  have hB : (B.card : ℝ) ≤ H := hcap (T.lines.symm (some (some 0, 0)))
  have hC : (C.card : ℝ) ≤ H := hcap (T.lines.symm (some (none, 0)))
  rw [card_coordinateGraph_eq_goodW T W]
  linarith

end RyserCoveringCounterexample.Incidence

end OAI
