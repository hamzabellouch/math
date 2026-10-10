import OAI.NumberTheory.DukePrimeDegree.Geometry.RowTimeSplit
import OAI.NumberTheory.DukePrimeDegree.Geometry.PositiveRootHolonomy
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootStableHolonomy

namespace OAI

/-!
# Intrinsic root leaves are constant in the other row coordinates

A diagonal flow can be neutral on one row root and contract all other
row roots simultaneously, regardless of their index ordering. Neutral
holonomy therefore identifies the selected intrinsic leaf at every pair
of row-coordinate points with the same selected coordinate, off one null
set. This supplies the geometric input for the abelian product step.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_neutral_row_contracting_weights (d : ℕ) {i j : Fin (d + 1)} (_hij : i ≠ j) :
    ∃ ell : Fin (d + 1) → ℝ, ∃ _hell : ∑ r, ell r = 0,
      ell i = ell j ∧ ∀ l, l ≠ i → l ≠ j → ell i < ell l := by
  let w : Fin (d + 1) → ℝ := fun r => if r = i ∨ r = j then 0 else 1
  refine ⟨centerWeights d w, centerWeights_sum d w, ?_, ?_⟩
  · simp [centerWeights, w]
  · intro l hli hlj
    simp [centerWeights, w, hli, hlj]

lemma rowRoot_neutral_root_limit (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) (hneut : ell i = ell j)
    (hdecay : ∀ l, l ≠ i → l ≠ j → ell i < ell l)
    (a : RowTime i) :
    Tendsto (fun t : ℝ => diagonalOneParameter ell hell t * rowRoot i a *
      diagonalOneParameter ell hell (-t)) atTop
      (𝓝 (Matrix.SpecialLinearGroup.transvection hij (a.val j))) := by
  let S := Finset.univ.filter (fun p : Fin (d + 1) × Fin (d + 1) => p.1 = i ∧ p.2 ≠ i)
  have hd : ∀ r, (r, r) ∉ S := by
    intro r
    simp [S]
  have hp : PositiveRootPattern S (rowRoot i a) := by
    intro r s hrs
    by_cases hr : r = i
    · subst r
      have hs : s = i := by
        by_contra hsi
        exact hrs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hsi⟩)
      subst s
      simp [rowRoot, rootRowElement_entry, rowTime_self]
    · simp [rowRoot, rootRowElement_entry, hr]
  have hh : ∀ p ∈ S, p ≠ (i, j) → ell p.1 < ell p.2 := by
    intro p hp hne
    obtain ⟨hpi, hpli⟩ := (Finset.mem_filter.mp hp).2
    have hplj : p.2 ≠ j := by
      intro he
      exact hne (Prod.ext hpi he)
    simpa only [hpi] using hdecay p.2 hpli hplj
  have H := rootPattern_isolated_limit d S hd hij ell hell hneut hh (rowRoot i a) hp
  have he : (rowRoot i a).val i j = a.val j := by
    simp [rowRoot, rootRowElement_entry, hij]
  simpa only [he] using H

lemma rowRoot_neutral_limit (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) (hneut : ell i = ell j)
    (hdecay : ∀ l, l ≠ i → l ≠ j → ell i < ell l)
    (a : RowTime i) (ha : a.val j = 0) :
    Tendsto (fun t : ℝ => diagonalOneParameter ell hell t * rowRoot i a *
      diagonalOneParameter ell hell (-t)) atTop (𝓝 1) := by
  simpa only [ha, Matrix.SpecialLinearGroup.transvection_coeff_zero] using
    rowRoot_neutral_root_limit d hij ell hell hneut hdecay a

theorem exists_nullset_row_leaf_holonomy
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ (x : X (d + 1)) (a b : RowTime i),
        rightAction x (rowRoot i a) ∉ N → rightAction x (rowRoot i b) ∉ N →
        intrinsicRootLeaf hij μ (rightAction x (rowRoot i b)) =
          basedRealMeasure (intrinsicRootLeaf hij μ (rightAction x (rowRoot i a)))
            (b.val j - a.val j) := by
  obtain ⟨ell, hell, hneutral, hdecay⟩ := exists_neutral_row_contracting_weights d hij
  obtain ⟨N, hN, hN0, hhol⟩ := exists_nullset_neutral_root_holonomy d hij μ hA ell hell hneutral
  refine ⟨N, hN, hN0, ?_⟩
  intro x a b ha hb
  have hrel : rightAction (rightAction x (rowRoot i a)) (rowRoot i (b - a)) =
      rightAction x (rowRoot i b) := by
    rw [rightAction_mul, ← rowRoot_add]
    congr 2
    abel
  exact hhol _ ha _ hb (rowRoot i (b - a)) hrel (b.val j - a.val j)
    (rowRoot_neutral_root_limit d hij ell hell hneutral hdecay (b - a))

theorem exists_nullset_row_leaf_constancy
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ (x : X (d + 1)) (a b : RowTime i), a.val j = b.val j →
        rightAction x (rowRoot i a) ∉ N → rightAction x (rowRoot i b) ∉ N →
        intrinsicRootLeaf hij μ (rightAction x (rowRoot i a)) =
          intrinsicRootLeaf hij μ (rightAction x (rowRoot i b)) := by
  obtain ⟨ell, hell, hneutral, hdecay⟩ := exists_neutral_row_contracting_weights d hij
  obtain ⟨N, hN, hN0, hhol⟩ := exists_nullset_neutral_root_holonomy d hij μ hA ell hell hneutral
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  obtain ⟨E, hbad, hE, hE0⟩ := exists_measurable_superset_of_null
    (ae_iff.mp ((ae_intrinsicRootLeaf_spec hij μ hfree).mono fun _ h => h.2))
  refine ⟨N ∪ E, hN.union hE, measure_union_null hN0 hE0, ?_⟩
  intro x a b hab ha hb
  have hj : (b - a).val j = 0 := by
    change b.val j - a.val j = 0
    exact sub_eq_zero.mpr hab.symm
  have hrel : rightAction (rightAction x (rowRoot i a)) (rowRoot i (b - a)) =
      rightAction x (rowRoot i b) := by
    rw [rightAction_mul, ← rowRoot_add]
    congr 2
    abel
  have hunit : intrinsicRootLeaf hij μ (rightAction x (rowRoot i a)) (Metric.ball 0 1) = 1 := by
    by_contra h
    exact ha (Or.inr (hbad h))
  have H := hhol _ (fun h => ha (Or.inl h)) _ (fun h => hb (Or.inl h))
    (rowRoot i (b - a)) hrel 0 (by
      simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero] using
        rowRoot_neutral_limit d hij ell hell hneutral hdecay (b - a) hj)
  rw [basedRealMeasure_zero_of_unit _ hunit] at H
  exact H.symm

end DukePrimeDegree

end

end OAI
