import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.AmbientDegree

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointMarginalSupport

open MatrixMultiplication.Foundation JointPopulation JointAmbientDegree
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ) (sum : H → ℕ)

omit [Fintype H] [DecidableEq H] in
theorem localAllowed_coordinate_witness (h : H) (w : Positions counts h → Shape)
    (hw : localAllowed counts sum h w) (s : Fin 3) (i : Positions counts h) :
    ∃ j : Positions counts h,
      shapeSide s ((canonicalTarget counts h).val j) = shapeSide s (w i) := by
  have hp : 0 < wordPopulation (shapeSide s ∘ w) (shapeSide s (w i)) := by
    unfold wordPopulation
    exact Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩
  rw [hw.2 s (shapeSide s (w i))] at hp
  obtain ⟨⟨j, hj⟩⟩ := Fintype.card_pos_iff.mp hp
  exact ⟨j, hj⟩

omit [Fintype H] [DecidableEq H] in
theorem localAllowed_coordinate_support (h : H) (w : Positions counts h → Shape)
    (hw : localAllowed counts sum h w) (allowed : Fin 3 → Fin 17 → Prop)
    (hallowed : ∀ u, 0 < counts h u → ∀ s, allowed s (shapeSide s u)) :
    ∀ i s, allowed s (shapeSide s (w i)) := by
  intro i s
  obtain ⟨j, hj⟩ := localAllowed_coordinate_witness counts sum h w hw s i
  rw [← hj]
  exact hallowed ((canonicalTarget counts h).val j)
    (symbol_count_pos counts (canonicalTarget counts) h j) s

omit [Fintype H] [DecidableEq H] in
theorem localAllowed_parent_bounds (h : H) (w : Positions counts h → Shape)
    (hw : localAllowed counts sum h w) (parent : Fin 3 → ℕ)
    (hparent : ∀ u, 0 < counts h u → ∀ s, (shapeSide s u).val ≤ parent s) :
    ∀ i s, (shapeSide s (w i)).val ≤ parent s :=
  localAllowed_coordinate_support counts sum h w hw
    (fun s a => a.val ≤ parent s) hparent

omit [Fintype H] [DecidableEq H] in
theorem localAllowed_positive_reference (h : H) (w : Positions counts h → Shape)
    (hw : localAllowed counts sum h w) (parent : Fin 3 → ℕ) (p : Shape → ℝ)
    (hparent : ∀ u, 0 < counts h u → ∀ s, (shapeSide s u).val ≤ parent s)
    (hp : ∀ u : Shape, u.1.val + u.2.1.val + u.2.2.val = sum h →
      (∀ s, (shapeSide s u).val ≤ parent s) → 0 < p u) :
    ∀ i, 0 < p (w i) := by
  intro i
  exact hp (w i) (hw.1 i) (localAllowed_parent_bounds counts sum h w hw parent hparent i)

end MatrixMultiplication.JointMarginalSupport

end

end OAI
