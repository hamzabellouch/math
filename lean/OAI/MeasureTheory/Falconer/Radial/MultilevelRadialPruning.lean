import OAI.MeasureTheory.Falconer.Radial.LocalRadialPruning

namespace OAI

/-! # A measurable surviving pair relation at finitely many radial levels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*}

noncomputable def multilevelRadialBad (μ : Measure (Space d)) (J : ℕ)
    (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d)) (c : ℕ → ι → Space d)
    (r D W : ℕ → ℝ) (B : ℝ) (F : ℕ → ℝ≥0∞) : Set (Space d × Space d) :=
  ⋃ j ∈ Finset.range J, levelRadialBad μ (I j) (Q j) (c j) (r j) (D j) B (W j) (F j)

noncomputable def radialGoodPairs (μ : Measure (Space d)) (J : ℕ)
    (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d)) (c : ℕ → ι → Space d)
    (r D W : ℕ → ℝ) (B : ℝ) (F : ℕ → ℝ≥0∞) : Set (Space d × Space d) :=
  (Prod.swap ⁻¹' multilevelRadialBad μ J I Q c r D W B F)ᶜ

theorem multilevelRadialBad_measurable (μ : Measure (Space d)) (J : ℕ)
    (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d)) (c : ℕ → ι → Space d)
    (r D W : ℕ → ℝ) (B : ℝ) (F : ℕ → ℝ≥0∞)
    (hQ : ∀ j < J, ∀ i ∈ I j, MeasurableSet (Q j i)) :
    MeasurableSet (multilevelRadialBad μ J I Q c r D W B F) := by
  apply Finset.measurableSet_biUnion
  intro j hj
  exact levelRadialBad_measurable μ (I j) (Q j) (c j) (r j) (D j) B (W j) (F j)
    (hQ j (Finset.mem_range.mp hj))

theorem radialGoodPairs_measurable (μ : Measure (Space d)) (J : ℕ)
    (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d)) (c : ℕ → ι → Space d)
    (r D W : ℕ → ℝ) (B : ℝ) (F : ℕ → ℝ≥0∞)
    (hQ : ∀ j < J, ∀ i ∈ I j, MeasurableSet (Q j i)) :
    MeasurableSet (radialGoodPairs μ J I Q c r D W B F) :=
  ((multilevelRadialBad_measurable μ J I Q c r D W B F hQ).preimage measurable_swap).compl

theorem radial_good_pairs_cost (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [SFinite ν]
    (J : ℕ) (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d)) (c : ℕ → ι → Space d)
    (r D W : ℕ → ℝ) (B : ℝ) (F K t : ℕ → ℝ≥0∞)
    (hQ : ∀ j < J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hpos : ∀ j < J, ∀ i ∈ I j, μ (Q j i) ≠ 0)
    (hdisj : ∀ j < J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hball : ∀ j < J, ∀ i ∈ I j, ν (Metric.ball (c j i) (r j)) ≤ K j)
    (htrouble : ∀ j < J, ∀ i ∈ I j,
      ((ProbabilityTheory.cond μ (Q j i)).prod ν)
        (troublesomePair (ProbabilityTheory.cond μ (Q j i)) (c j i) (r j) (D j) B (W j) (F j)) ≤ t j) :
    (ν.prod μ) (radialGoodPairs μ J I Q c r D W B F)ᶜ ≤
      (∑ j ∈ Finset.range J, (K j+t j))*μ univ := by
  have hm := multilevelRadialBad_measurable μ J I Q c r D W B F hQ
  change (ν.prod μ) ((Prod.swap ⁻¹' multilevelRadialBad μ J I Q c r D W B F)ᶜ)ᶜ ≤ _
  rw [compl_compl,← Measure.map_apply measurable_swap hm,Measure.prod_swap]
  calc
    _ ≤ ∑ j ∈ Finset.range J,
        (μ.prod ν) (levelRadialBad μ (I j) (Q j) (c j) (r j) (D j) B (W j) (F j)) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range J, (K j+t j)*μ univ := Finset.sum_le_sum (fun j hj =>
      level_radial_bad_mass μ ν (I j) (Q j) (c j) (r j) (D j) B (W j) (F j) (K j) (t j)
        (hQ j (Finset.mem_range.mp hj)) (hpos j (Finset.mem_range.mp hj))
        (hdisj j (Finset.mem_range.mp hj)) (hball j (Finset.mem_range.mp hj))
        (htrouble j (Finset.mem_range.mp hj)))
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem original_tube_test_of_radial_good (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (J : ℕ) (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d)) (c : ℕ → ι → Space d)
    (r D W : ℕ → ℝ) (B : ℝ) (F : ℕ → ℝ≥0∞)
    {x z : Space d} (hgood : (x,z) ∈ radialGoodPairs μ J I Q c r D W B F)
    {j : ℕ} (hj : j < J) (hDr : D j < r j) {i : ι} (hi : i ∈ I j)
    (hQ : ∀ i ∈ I j, MeasurableSet (Q j i))
    (hzQ : z ∈ Q j i) (hzD : ‖z-c j i‖ ≤ D j) (hzB : ‖z‖ ≤ B) :
    μ (Q j i ∩ {y | ‖perpendicularPart (NormedSpace.normalize (z-x)) (y-x)‖ ≤ W j}) ≤
      F j*μ (Q j i) := by
  apply original_tube_test_of_level_retained μ (I j) (Q j) (c j) (r j) (D j) B (W j) (F j)
    hDr hQ (i := i) _ hi hzQ hzD hzB
  intro hb
  exact hgood (mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨Finset.mem_range.mpr hj,hb⟩⟩)

end Falconer

end OAI
