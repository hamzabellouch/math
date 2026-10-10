import OAI.MeasureTheory.Falconer.Estimates.NearPinDeletion
import OAI.MeasureTheory.Falconer.Estimates.RetainedTubeTest

namespace OAI

/-! # One level of measurable radial pruning and its original-law cost -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

noncomputable def levelRadialBad (μ : Measure (Space d)) (I : Finset ι)
    (Q : ι → Set (Space d)) (c : ι → Space d) (r D B W : ℝ) (F : ℝ≥0∞) :
    Set (Space d × Space d) :=
  nearPinPairs I Q c r ∪ ⋃ i ∈ I,
    troublesomePair (ProbabilityTheory.cond μ (Q i)) (c i) r D B W F ∩ (Q i ×ˢ univ)

theorem levelRadialBad_measurable (μ : Measure (Space d)) (I : Finset ι)
    (Q : ι → Set (Space d)) (c : ι → Space d) (r D B W : ℝ) (F : ℝ≥0∞)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) :
    MeasurableSet (levelRadialBad μ I Q c r D B W F) := by
  apply (nearPinPairs_measurable I Q c r hQ).union
  apply Finset.measurableSet_biUnion
  intro i hi
  exact (troublesomePair_measurable _ _ _ _ _ _ _).inter ((hQ i hi).prod MeasurableSet.univ)

theorem level_radial_bad_mass (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [SFinite ν]
    (I : Finset ι) (Q : ι → Set (Space d)) (c : ι → Space d)
    (r D B W : ℝ) (F K t : ℝ≥0∞)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hpos : ∀ i ∈ I, μ (Q i) ≠ 0)
    (hdisj : (I : Set ι).PairwiseDisjoint Q)
    (hball : ∀ i ∈ I, ν (ball (c i) r) ≤ K)
    (htrouble : ∀ i ∈ I, ((ProbabilityTheory.cond μ (Q i)).prod ν)
      (troublesomePair (ProbabilityTheory.cond μ (Q i)) (c i) r D B W F) ≤ t) :
    (μ.prod ν) (levelRadialBad μ I Q c r D B W F) ≤ (K+t)*μ univ := by
  apply (measure_union_le _ _).trans
  have hn := near_pin_pair_mass μ ν I Q c r hQ hdisj K hball
  have ht := conditional_cellwise_pair_deletion μ ν I Q
    (fun i => troublesomePair (ProbabilityTheory.cond μ (Q i)) (c i) r D B W F)
    hQ (fun i _ => troublesomePair_measurable _ _ _ _ _ _ _) hpos hdisj t htrouble
  exact (add_le_add hn ht).trans_eq (add_mul K t (μ univ)).symm

theorem original_tube_test_of_level_retained (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (I : Finset ι) (Q : ι → Set (Space d)) (c : ι → Space d)
    (r D B W : ℝ) (F : ℝ≥0∞) (hDr : D < r)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) {z x : Space d}
    (hgood : (z,x) ∉ levelRadialBad μ I Q c r D B W F) {i : ι} (hi : i ∈ I)
    (hzQ : z ∈ Q i) (hzD : ‖z-c i‖ ≤ D) (hzB : ‖z‖ ≤ B) :
    μ (Q i ∩ {y | ‖perpendicularPart (NormedSpace.normalize (z-x)) (y-x)‖ ≤ W}) ≤ F*μ (Q i) := by
  have hn : (z,x) ∉ nearPinPairs I Q c r := fun h => hgood (Or.inl h)
  have hs := distance_of_not_nearPinPairs I Q c r hn hi hzQ
  have hsep : r ≤ ‖c i-x‖ := by simpa only [dist_eq_norm,norm_sub_rev] using hs
  have hne : z ≠ x := by
    intro he
    subst z
    rw [norm_sub_rev] at hzD
    exact (not_le_of_gt hDr) (hsep.trans hzD)
  have ht : (z,x) ∉ troublesomePair (ProbabilityTheory.cond μ (Q i)) (c i) r D B W F := by
    intro h
    exact hgood (Or.inr (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,h,hzQ,mem_univ _⟩⟩))
  exact original_tube_test_of_not_troublesome μ (Q i) (hQ i hi) (c i) z x r D B W F
    ht hsep hne hzD hzB

end Falconer

end OAI
