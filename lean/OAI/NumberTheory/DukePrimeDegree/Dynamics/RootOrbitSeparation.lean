import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafBoxSeparation

namespace OAI

/-!
# Root-orbit separation outside one null set

Countably many long root boxes cover every finite segment of every free
root orbit. Removing their exceptional sets turns the chartwise
separation theorem into separation for all root translations at once.
This proves the one-dimensional part of EKL Lemma 4.4(2), without a
pointwise rebasing assumption.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_nullset_root_orbit_leaf_separation
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hnot : ¬ ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧ ∀ x ∉ N, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∉ N →
      intrinsicRootLeaf hij μ x =
        intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) →
      t = 0 := by
  let C := fun (k : Fin (d + 1)) (m : ℕ) => rootLongBoxFamily hij k 1 m
  let (k : Fin (d + 1)) (m : ℕ) : Countable (C k m) :=
    (rootLongBoxFamily_countable hij k 1 m).to_subtype
  let I := Σ k : Fin (d + 1), Σ m : ℕ, C k m
  let box := fun q : I => q.2.2.val
  have htime (q : I) : (box q).time ⊆ rootLeafWindow (1 + (q.2.1 : ℝ)) 0 := by
    rw [rootLongBoxFamily_time hij q.1 1 q.2.1 (box q) q.2.2.property]
    simp only [rootLeafWindow, Nat.cast_zero, add_zero, subset_refl]
  have hlocal (q : I) := rootBox_leaf_separates_fibers_outside_nullset
    d hij μ hnot (box q) (1 + (q.2.1 : ℝ)) (htime q)
  choose N hN hzero hsep using hlocal
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  obtain ⟨M, hbad, hM, hMzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hfree)
  let E := M ∪ ⋃ q : I, N q
  have hEzero : μ E = 0 := measure_union_null hMzero (measure_iUnion_null hzero)
  refine ⟨E, hM.union (MeasurableSet.iUnion hN), hEzero, ?_⟩
  intro x hx t hy heq
  have hxfree : ∀ u : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij u) = x → u = 0 := by
    by_contra h
    exact hx (Or.inl (hbad h))
  obtain ⟨k, B, z, hz⟩ := exists_rootBox_at hij x
  let s := z.val.1
  let v := z.val.2
  have hxparam : rootQuotientParametrization hij (s, v) = x := hz
  have hyparam : rootQuotientParametrization hij (s, v + t) =
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) := by
    rw [rootQuotientParametrization_add, hxparam]
  have hsfree := root_time_injective_of_free hij s v (by rwa [hxparam])
  obtain ⟨m, hm⟩ := exists_nat_gt (max |v| |v + t|)
  have hv : v ∈ rootLeafWindow 1 m := by
    apply abs_lt.mp
    exact (lt_of_le_of_lt (le_max_left _ _) hm).trans (by linarith)
  have hvt : v + t ∈ rootLeafWindow 1 m := by
    apply abs_lt.mp
    exact (lt_of_le_of_lt (le_max_right _ _) hm).trans (by linarith)
  obtain ⟨D, hD, hsD⟩ := rootLongBoxFamily_covers hij k 1 m s hsfree
  let q : I := ⟨k, m, ⟨D, hD⟩⟩
  have htD : D.time = rootLeafWindow 1 m := rootLongBoxFamily_time hij k 1 m D hD
  have hzD : (s, v) ∈ (box q).domain := ⟨hsD, htD.symm ▸ hv⟩
  have hwD : (s, v + t) ∈ (box q).domain := ⟨hsD, htD.symm ▸ hvt⟩
  have hNx : rootQuotientParametrization hij (s, v) ∉ N q := by
    rw [hxparam]
    exact fun h => hx (Or.inr (mem_iUnion.mpr ⟨q, h⟩))
  have hNy : rootQuotientParametrization hij (s, v + t) ∉ N q := by
    rw [hyparam]
    exact fun h => hy (Or.inr (mem_iUnion.mpr ⟨q, h⟩))
  have hzw := hsep q (s, v) hzD (s, v + t) hwD hNx hNy rfl (by
    rwa [hxparam, hyparam])
  have hvv := congrArg Prod.snd hzw
  dsimp only at hvv
  linarith

end DukePrimeDegree

end

end OAI
