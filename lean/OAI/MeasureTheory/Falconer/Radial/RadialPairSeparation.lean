import OAI.MeasureTheory.Falconer.Radial.RadialRemoveDiagonal

namespace OAI

/-! # Separating retained original pairs with their actual ball-mass cost -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

lemma original_close_pair_mass (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (r : ℝ) (K : ℝ≥0∞) (hball : ∀ x, μ (ball x r) ≤ K) :
    (μ.prod μ) {p : Space d × Space d | dist p.1 p.2 < r} ≤ K := by
  have hS : MeasurableSet {p : Space d × Space d | dist p.1 p.2 < r} :=
    measurableSet_lt (by fun_prop) measurable_const
  rw [Measure.prod_apply hS]
  calc
    _ ≤ ∫⁻ _x, K ∂μ := lintegral_mono (fun x => by
      simpa only [preimage_ofPred_eq,Metric.ball,dist_comm] using hball x)
    _ = _ := by simp

noncomputable def separatedRadialPairs (G : Set (Space d × Space d)) (r : ℝ) :
    Set (Space d × Space d) := {p | p ∈ G ∧ r ≤ dist p.1 p.2}

lemma separatedRadialPairs_measurable {G : Set (Space d × Space d)} (hG : MeasurableSet G)
    (r : ℝ) : MeasurableSet (separatedRadialPairs G r) :=
  hG.inter (measurableSet_le measurable_const
    (show Measurable (fun p : Space d × Space d => dist p.1 p.2) from by fun_prop))

lemma separatedRadialPairs_subset (G : Set (Space d × Space d)) (r : ℝ) :
    separatedRadialPairs G r ⊆ G := fun _ hp => hp.1

lemma separatedRadialPairs_cost (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (G : Set (Space d × Space d)) (r : ℝ) (K : ℝ≥0∞)
    (hball : ∀ x, μ (ball x r) ≤ K) :
    (μ.prod μ) (separatedRadialPairs G r)ᶜ ≤ (μ.prod μ) Gᶜ+K := by
  have hs : (separatedRadialPairs G r)ᶜ ⊆ Gᶜ ∪ {p | dist p.1 p.2 < r} := by
    intro p hp
    by_cases hg : p ∈ G
    · right
      by_contra hd
      exact hp ⟨hg,le_of_not_gt hd⟩
    · exact Or.inl hg
  exact (measure_mono hs).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (original_close_pair_mass μ r K hball)))

end Falconer

end OAI
