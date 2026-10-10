import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafMaximalScaling

namespace OAI

/-!
# A maximal bound uniform in the time window

Diagonal invariance rescales any bounded family of witnessing intervals
into the short-time estimate. Its constant is independent of the bound
on those intervals.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem bounded_interval_intrinsic_maximal_bound
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ M : ℕ, ∀ (R : ℝ) (B E : Set (X (d + 1))),
      MeasurableSet B → MeasurableSet E → ∀ c : ℝ≥0∞,
      (∀ᵐ x ∂μ, x ∈ B → ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
        c * intrinsicRootLeaf hij μ x (closedBall 0 r) ≤
          intrinsicRootLeaf hij μ x
            ({u | rightAction x (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩
              closedBall 0 r)) →
      c * μ B ≤ (M : ℝ≥0∞) * μ E + c * ε := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  obtain ⟨M, δ, hδ, hbound⟩ := short_interval_intrinsic_maximal_bound hij μ hfree ε hε
  refine ⟨M, ?_⟩
  intro R B E hB hE c hbad
  let q : ℝ := δ / (|R| + 1)
  have hq : 0 < q := div_pos hδ (by positivity)
  have hqR : q * R ≤ δ := by
    calc
      q * R ≤ q * (|R| + 1) := mul_le_mul_of_nonneg_left (by linarith [le_abs_self R]) hq.le
      _ = δ := div_mul_cancel₀ _ (by positivity)
  let t := Real.log q
  let f := rightActionHomeomorph (rootCanonicalFlow d j t)
  have hexp : Real.exp t = q := Real.exp_log hq
  have hfμ : MeasurePreserving f μ μ := rootCanonicalFlow_preserving d j t μ hA
  have hB' : MeasurableSet (f '' B) := f.isOpenEmbedding.measurableEmbedding.measurableSet_image.mpr hB
  have hE' : MeasurableSet (f '' E) := f.isOpenEmbedding.measurableEmbedding.measurableSet_image.mpr hE
  have hbase : ∀ᵐ x ∂μ, f x ∈ f '' B → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
      c * intrinsicRootLeaf hij μ (f x) (closedBall 0 r) ≤
        intrinsicRootLeaf hij μ (f x)
          ({u | rightAction (f x) (Matrix.SpecialLinearGroup.transvection hij u) ∈ f '' E} ∩
            closedBall 0 r) := by
    filter_upwards [hbad, ae_intrinsicRootLeaf_canonical d hij μ hA t] with x hx hcov
    intro hxB
    obtain ⟨r, hr, hrR, hmass⟩ := hx (f.injective.mem_set_image.mp hxB)
    refine ⟨q * r, mul_pos hq hr,
      (mul_le_mul_of_nonneg_left hrR hq.le).trans hqR, ?_⟩
    have H := intrinsic_bad_interval_scale d hij μ x t r E hE hcov c hmass
    rw [hexp, show rightAction x (rootCanonicalFlow d j t) = f x from rfl] at H
    exact H
  have hnew : ∀ᵐ y ∂μ, y ∈ f '' B → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
      c * intrinsicRootLeaf hij μ y (closedBall 0 r) ≤
        intrinsicRootLeaf hij μ y
          ({u | rightAction y (Matrix.SpecialLinearGroup.transvection hij u) ∈ f '' E} ∩
            closedBall 0 r) := by
    let P : X (d + 1) → Prop := fun y => y ∈ f '' B → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
      c * intrinsicRootLeaf hij μ y (closedBall 0 r) ≤
        intrinsicRootLeaf hij μ y
          ({u | rightAction y (Matrix.SpecialLinearGroup.transvection hij u) ∈ f '' E} ∩
            closedBall 0 r)
    have hb : ∀ᵐ x ∂μ, P (f x) := hbase
    have hmap : ∀ᵐ y ∂μ.map f, P y := f.isOpenEmbedding.measurableEmbedding.ae_map_iff.mpr hb
    simpa only [hfμ.map_eq] using hmap
  have hmeasure (S : Set (X (d + 1))) (hS : MeasurableSet S) : μ (f '' S) = μ S := by
    calc
      μ (f '' S) = (μ.map f) (f '' S) := by rw [hfμ.map_eq]
      _ = μ S := by
        rw [Measure.map_apply f.measurable
          (f.isOpenEmbedding.measurableEmbedding.measurableSet_image.mpr hS),
          f.injective.preimage_image]
  have H := hbound (f '' B) (f '' E) hB' hE' c hnew
  rwa [hmeasure B hB, hmeasure E hE] at H

end DukePrimeDegree

end

end OAI
