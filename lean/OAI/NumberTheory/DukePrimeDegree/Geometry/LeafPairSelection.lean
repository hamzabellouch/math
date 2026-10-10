import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafGoodSet

namespace OAI

/-!
# Simultaneous compact returns on equal root leaves

The all-radius good-set estimate controls both exceptional time sets
with the same leaf measure. A third small forbidden set can be removed
while retaining a common return time.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma exists_common_point_outside_forbidden
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (W L R F : Set Y)
    (hbudget : ν (W \ L) + ν (W \ R) + ν (W ∩ F) < ν W) :
    ∃ t ∈ W, t ∈ L ∧ t ∈ R ∧ t ∉ F := by
  by_contra h
  have hcover : W ⊆ ((W \ L) ∪ (W \ R)) ∪ (W ∩ F) := by
    intro t ht
    by_cases hL : t ∈ L
    · by_cases hR : t ∈ R
      · exact Or.inr ⟨ht, by_contra fun hF => h ⟨t, ht, hL, hR, hF⟩⟩
      · exact Or.inl (Or.inr ⟨ht, hR⟩)
    · exact Or.inl (Or.inl ⟨ht, hL⟩)
  have hle : ν W ≤ ν (W \ L) + ν (W \ R) + ν (W ∩ F) :=
    (measure_mono hcover).trans ((measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl))
  exact hbudget.not_ge hle

theorem exists_simultaneous_root_return
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (K G : Set (X n)) (c : ℝ≥0∞)
    (hgood : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
      intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ closedBall 0 r) ≤
        c * intrinsicRootLeaf hij μ x (closedBall 0 r))
    (x y : X n) (hx : x ∈ G) (hy : y ∈ G)
    (heq : intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ y)
    (r : ℝ) (hr : 0 < r) (F : Set ℝ)
    (hbudget : (c + c) * intrinsicRootLeaf hij μ x (closedBall 0 r) +
      intrinsicRootLeaf hij μ x (closedBall 0 r ∩ F) <
        intrinsicRootLeaf hij μ x (closedBall 0 r)) :
    ∃ t ∈ closedBall (0 : ℝ) r,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∈ K ∧
      rightAction y (Matrix.SpecialLinearGroup.transvection hij t) ∈ K ∧ t ∉ F := by
  let ν := intrinsicRootLeaf hij μ x
  let W := closedBall (0 : ℝ) r
  have hleft : ν (W \ rootHitTimes hij K x) ≤ c * ν W := by
    have he : W \ rootHitTimes hij K x = rootHitTimes hij Kᶜ x ∩ W := by
      ext t
      simp only [Set.mem_sdiff, mem_inter_iff, rootHitTimes, mem_ofPred_eq, mem_compl_iff]
      tauto
    rw [he]
    exact hgood x hx r hr
  have hright : ν (W \ rootHitTimes hij K y) ≤ c * ν W := by
    have he : W \ rootHitTimes hij K y = rootHitTimes hij Kᶜ y ∩ W := by
      ext t
      simp only [Set.mem_sdiff, mem_inter_iff, rootHitTimes, mem_ofPred_eq, mem_compl_iff]
      tauto
    rw [he]
    change intrinsicRootLeaf hij μ x _ ≤ c * intrinsicRootLeaf hij μ x _
    rw [heq]
    exact hgood y hy r hr
  apply exists_common_point_outside_forbidden ν W (rootHitTimes hij K x)
    (rootHitTimes hij K y) F
  calc
    ν (W \ rootHitTimes hij K x) + ν (W \ rootHitTimes hij K y) + ν (W ∩ F)
        ≤ c * ν W + c * ν W + ν (W ∩ F) :=
      add_le_add (add_le_add hleft hright) le_rfl
    _ = (c + c) * ν W + ν (W ∩ F) := by rw [add_mul]
    _ < ν W := hbudget

end DukePrimeDegree

end

end OAI
