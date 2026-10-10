import OAI.NumberTheory.DukePrimeDegree.Dynamics.TwoBlockLocalNeutralMeasure
import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingularCentralizer

namespace OAI

/-!
# Transport of the two-block chart to the arithmetic matrix group

The partition is the actual partition induced by a chosen enumeration of
two coordinate blocks. Reindexing identifies its block matrix subgroup
with the concrete neutral subgroup used in the parabolic chart.
-/

noncomputable section
open Matrix Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def twoBlockIndexSetoid {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) : Setoid (Fin n) where
  r i j := (e i).isLeft = (e j).isLeft
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

def twoBlockReindex {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    G n ≃* TwoBlockSL a b where
  toFun M := ⟨Matrix.reindex e e M.val, by rw [Matrix.det_reindex_self]; exact M.prop⟩
  invFun M := ⟨Matrix.reindex e.symm e.symm M.val,
    by rw [Matrix.det_reindex_self]; exact M.prop⟩
  left_inv M := by
    apply Subtype.ext
    ext i j
    change M.val (e.symm (e i)) (e.symm (e j)) = M.val i j
    rw [e.symm_apply_apply, e.symm_apply_apply]
  right_inv M := by
    apply Subtype.ext
    ext i j
    change M.val (e (e.symm i)) (e (e.symm j)) = M.val i j
    rw [e.apply_symm_apply, e.apply_symm_apply]
  map_mul' M N := by
    apply Subtype.ext
    exact (Matrix.reindexRingEquiv ℝ e).map_mul M.val N.val

def twoBlockReindexHomeomorph {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    G n ≃ₜ TwoBlockSL a b where
  toEquiv := (twoBlockReindex e).toEquiv
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (e.symm j)).comp
        ((continuous_apply (e.symm i)).comp continuous_subtype_val)
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (e j)).comp
        ((continuous_apply (e i)).comp continuous_subtype_val)

theorem reindex_cross_blocks_zero_iff {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (M : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.reindex e e M).toBlocks₁₂ = 0 ∧
      (Matrix.reindex e e M).toBlocks₂₁ = 0 ↔
    ∀ i j, ¬ (twoBlockIndexSetoid e) i j → M i j = 0 := by
  constructor
  · rintro ⟨h12, h21⟩ i j hij
    have he : M i j = Matrix.reindex e e M (e i) (e j) := by
      change M i j = M (e.symm (e i)) (e.symm (e j))
      rw [e.symm_apply_apply, e.symm_apply_apply]
    rw [he]
    cases hi : e i with
    | inl u =>
      cases hj : e j with
      | inl v => exact (hij (by change (e i).isLeft = (e j).isLeft; rw [hi, hj]; rfl)).elim
      | inr v =>
        have hz := congrFun (congrFun h12 u) v
        change Matrix.reindex e e M (Sum.inl u) (Sum.inr v) = 0 at hz
        exact hz
    | inr u =>
      cases hj : e j with
      | inl v =>
        have hz := congrFun (congrFun h21 u) v
        change Matrix.reindex e e M (Sum.inr u) (Sum.inl v) = 0 at hz
        exact hz
      | inr v => exact (hij (by change (e i).isLeft = (e j).isLeft; rw [hi, hj]; rfl)).elim
  · intro h
    constructor
    · ext i j
      change M (e.symm (Sum.inl i)) (e.symm (Sum.inr j)) = 0
      exact h _ _ (by
        change ¬ (e (e.symm (Sum.inl i))).isLeft = (e (e.symm (Sum.inr j))).isLeft
        simp)
    · ext i j
      change M (e.symm (Sum.inr i)) (e.symm (Sum.inl j)) = 0
      exact h _ _ (by
        change ¬ (e (e.symm (Sum.inr i))).isLeft = (e (e.symm (Sum.inl j))).isLeft
        simp)

theorem twoBlockReindex_mem_neutral_iff {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (g : G n) :
    twoBlockReindex e g ∈ twoBlockNeutralGroup a b ↔
      g ∈ blockMatrixGroup (twoBlockIndexSetoid e) := by
  rw [mem_twoBlockNeutralGroup_iff]
  change (Matrix.reindex e e g.val).toBlocks₁₂ = 0 ∧
    (Matrix.reindex e e g.val).toBlocks₂₁ = 0 ↔ _
  rw [reindex_cross_blocks_zero_iff]
  exact ⟨fun h => mem_blockMatrixGroup_of_cross_zero _ _ h,
    fun h => cross_zero_of_mem_blockMatrixGroup _ _ h⟩

def twoBlockNeutralIndexEquiv {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    blockMatrixGroup (twoBlockIndexSetoid e) ≃* twoBlockNeutralGroup a b where
  toFun g := ⟨twoBlockReindex e g.val, (twoBlockReindex_mem_neutral_iff e g.val).mpr g.property⟩
  invFun g := ⟨(twoBlockReindex e).symm g.val, by
    apply (twoBlockReindex_mem_neutral_iff e _).mp
    simpa only [MulEquiv.apply_symm_apply] using g.property⟩
  left_inv g := Subtype.ext ((twoBlockReindex e).symm_apply_apply g.val)
  right_inv g := Subtype.ext ((twoBlockReindex e).apply_symm_apply g.val)
  map_mul' g h := Subtype.ext ((twoBlockReindex e).map_mul g.val h.val)

def twoBlockNeutralIndexHomeomorph {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    blockMatrixGroup (twoBlockIndexSetoid e) ≃ₜ twoBlockNeutralGroup a b where
  toEquiv := (twoBlockNeutralIndexEquiv e).toEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (twoBlockReindexHomeomorph e).continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (twoBlockReindexHomeomorph e).symm.continuous.comp continuous_subtype_val

end DukePrimeDegree

end

end OAI
