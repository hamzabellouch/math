import OAI.NumberTheory.DukePrimeDegree.Geometry.RootFactorHolonomy

namespace OAI

/-!
# Root charts preserving earlier Gaussian eliminations

A root translation preserves all previously eliminated entries when
each affected source entry is already zero. Restricting the actual root
chart gives the next coordinate chart without losing the earlier zeros
or the already chosen nonzero diagonal pivots.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def ZeroPattern {n : ℕ} (P : Finset (Fin n × Fin n)) (g : G n) : Prop :=
  ∀ p ∈ P, g.val p.1 p.2 = 0

def NonzeroPivots {n : ℕ} (D : Finset (Fin n)) (g : G n) : Prop :=
  ∀ r ∈ D, g.val r r ≠ 0

abbrev EliminationSlice {n : ℕ} (P : Finset (Fin n × Fin n)) (D : Finset (Fin n)) :=
  {g : G n // ZeroPattern P g ∧ NonzeroPivots D g}

theorem zeroPattern_root_translate {n : ℕ} (P : Finset (Fin n × Fin n))
    {a b : Fin n} (hab : a ≠ b)
    (hP : ∀ r, (r, b) ∈ P → (r, a) ∈ P)
    {g : G n} (hg : ZeroPattern P g) (t : ℝ) :
    ZeroPattern P (g * Matrix.SpecialLinearGroup.transvection hab t) := by
  intro p hp
  rw [root_mul_entry, hg p hp]
  by_cases hb : p.2 = b
  · have hs : g.val p.1 a = 0 :=
      hg (p.1, a) (hP p.1 (by simpa only [← hb, Prod.mk.eta] using hp))
    simp only [hb, ite_true, hs, zero_mul, add_zero]
  · simp only [hb, ite_false, add_zero]

theorem nonzeroPivots_root_translate {n : ℕ} (D : Finset (Fin n))
    {a b : Fin n} (hab : a ≠ b) (hb : b ∉ D)
    {g : G n} (hg : NonzeroPivots D g) (t : ℝ) :
    NonzeroPivots D (g * Matrix.SpecialLinearGroup.transvection hab t) := by
  intro r hr
  have hrb : r ≠ b := fun h => hb (h ▸ hr)
  simpa only [root_mul_entry, hrb, ite_false, add_zero] using hg r hr

lemma elimination_pivot_isOpen {n : ℕ} (P : Finset (Fin n × Fin n))
    (D : Finset (Fin n)) (a : Fin n) :
    IsOpen {g : EliminationSlice P D | g.val.val a a ≠ 0} :=
  (rootPivot_isOpen a a).preimage continuous_subtype_val

/-- One Gaussian coordinate, restricted to the already eliminated
entries and nonzero pivots. The new transverse slice records the next
zero and pivot exactly. -/
def eliminationRootHomeomorph {n : ℕ} (P : Finset (Fin n × Fin n))
    (D : Finset (Fin n)) {a b : Fin n} (hab : a ≠ b)
    (hP : ∀ r, (r, b) ∈ P → (r, a) ∈ P) (hb : b ∉ D) :
    {g : EliminationSlice P D // g.val.val a a ≠ 0} ≃ₜ
      EliminationSlice (insert (a, b) P) (insert a D) × ℝ where
  toFun g :=
    let q : RootPivot a a := ⟨g.val.val, g.prop⟩
    let s := PrimeDegreePackets.rootSliceRepresentative hab q
    (⟨s.val, by
      constructor
      · intro p hp
        rcases Finset.mem_insert.mp hp with he | hp
        · subst p
          exact s.prop.2
        · exact zeroPattern_root_translate P hab hP g.val.prop.1 _ p hp
      · intro r hr
        rcases Finset.mem_insert.mp hr with he | hr
        · subst r
          exact s.prop.1
        · exact nonzeroPivots_root_translate D hab hb g.val.prop.2 _ r hr⟩,
      rootParameter a b a g.val.val)
  invFun z :=
    let s : RootSlice a b a := ⟨z.1.val,
      z.1.prop.2 a (Finset.mem_insert_self _ _),
      z.1.prop.1 (a, b) (Finset.mem_insert_self _ _)⟩
    let q := rootPivotTranslate hab ⟨s.val, s.prop.1⟩ z.2
    ⟨⟨q.val, by
      constructor
      · apply zeroPattern_root_translate P hab hP
        intro p hp
        exact z.1.prop.1 p (Finset.mem_insert_of_mem hp)
      · apply nonzeroPivots_root_translate D hab hb
        intro r hr
        exact z.1.prop.2 r (Finset.mem_insert_of_mem hr)⟩, q.prop⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : RootPivot a a => q.val) ((rootPivotHomeomorph (k := a) hab).left_inv
      ⟨g.val.val, g.prop⟩)
  right_inv z := by
    let s : RootSlice a b a := ⟨z.1.val,
      z.1.prop.2 a (Finset.mem_insert_self _ _),
      z.1.prop.1 (a, b) (Finset.mem_insert_self _ _)⟩
    have H := (rootPivotHomeomorph (k := a) hab).right_inv (s, z.2)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun p : RootSlice a b a × ℝ => p.1.val) H
    · exact congrArg (fun p : RootSlice a b a × ℝ => p.2) H
  continuous_toFun := by
    have hq : Continuous (fun g : {g : EliminationSlice P D // g.val.val a a ≠ 0} =>
        (⟨g.val.val, g.prop⟩ : RootPivot a a)) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (((continuous_rootSliceRepresentative hab).comp hq).subtype_val.subtype_mk _).prodMk
      (continuous_rootParameter.comp hq)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_rootTransvection hab).comp continuous_snd)

end DukePrimeDegree

end

end OAI
