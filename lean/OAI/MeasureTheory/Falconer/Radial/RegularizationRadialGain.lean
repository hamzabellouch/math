import OAI.MeasureTheory.Falconer.Radial.ClasswiseRadialGain
import OAI.MeasureTheory.Falconer.Estimates.RegularizationCount

namespace OAI

/-! # Recombining the actual radial regularization classes without a class-count loss -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem normalized_regularization_class_eq_cond (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (T : List ℕ) :
    normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T =
      ProbabilityTheory.cond μ (regularizationSet Q μ N B T) := by
  unfold normalizedClass classMeasure ProbabilityTheory.cond regularizationSet
  rw [Measure.restrict_apply_univ]

theorem regularization_radial_gain (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hroot : μ Q.carrierᶜ = 0) {N H : ℕ} (hH : 0 < H) (hNH : H ≤ N) (hdN : d+3 ≤ N)
    {threshold : ℝ≥0∞} (hthreshold : 0 < threshold) (t C : ℝ≥0∞) (r : ℝ)
    (hlocal : ∀ T ∈ regularizationIndex Q μ N (N/H) threshold,
      ∃ G : Set (Space d × Space d), MeasurableSet G ∧
        (ν.prod (normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T)) Gᶜ ≤ t ∧
        ∀ x u : Space d,
          normalizedClass Q μ (regularizationLeaves Q μ N)
            (regularizationLabel Q μ N (N/H)) T
            {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) :
    ∃ G : Set (Space d × Space d), MeasurableSet G ∧
      (ν.prod μ) Gᶜ ≤ ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*threshold+t ∧
      ∀ x u : Space d, μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
  classical
  let I := regularizationIndex Q μ N (N/H) threshold
  let S := regularizationSet Q μ N (N/H)
  have hex : ∀ T : List ℕ, ∃ G : Set (Space d × Space d), MeasurableSet G ∧
      (T ∈ I → (ν.prod (ProbabilityTheory.cond μ (S T))) Gᶜ ≤ t ∧
        ∀ x u : Space d, ProbabilityTheory.cond μ (S T)
          {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) := by
    intro T
    by_cases hT : T ∈ I
    · obtain ⟨G,hm,hc,hg⟩ := hlocal T hT
      rw [normalized_regularization_class_eq_cond] at hc hg
      exact ⟨G,hm,fun _ => ⟨hc,hg⟩⟩
    · exact ⟨∅,MeasurableSet.empty,fun h => (hT h).elim⟩
  choose G hm hg using hex
  have hpos : ∀ T ∈ I, μ (S T) ≠ 0 := by
    intro T hT
    exact (hthreshold.trans_le (regularizationSet_mass Q μ N (N/H) threshold hT)).ne'
  have hdisj : (I : Set (List ℕ)).PairwiseDisjoint S := by
    intro T _ U _ hTU
    exact regularizationSet_disjoint Q hQ μ N (N/H) hTU
  obtain ⟨G',hG',hc,hcap⟩ := classwise_radial_gain μ ν I S G
    (fun T _ => regularizationSet_measurable Q μ N (N/H) T) (fun T _ => hm T)
    hpos hdisj t C r (fun T hT => (hg T hT).1) (fun T hT => (hg T hT).2)
  refine ⟨G',hG',hc.trans (add_le_add ?_ le_rfl),hcap⟩
  exact regularization_discarded_global Q hQ μ hroot hH hNH hdN threshold

end Falconer.Regularization

end OAI
