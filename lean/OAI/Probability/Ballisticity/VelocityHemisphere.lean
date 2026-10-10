import OAI.Probability.Ballisticity.PositiveEscape

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

theorem positive_probability_transience_velocity_hemisphere
    {d : ℕ} (hd : 3 ≤ d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : ℓ ≠ 0)
    (hpos : 0 < annealedLaw ν (TransientPaths ℓ)) :
    ∃ v : Vector d,
      v ≠ 0 ∧ 0 < dot v ℓ ∧ annealedLaw ν (VelocityPaths v) = 1 ∧
      (∀ w : Vector d, annealedLaw ν (VelocityPaths w) = 1 → w = v) ∧
      {u : Vector d | dot u u = 1 ∧ annealedLaw ν (TransientPaths u) = 1} =
        {u : Vector d | dot u u = 1 ∧ 0 < annealedLaw ν (TransientPaths u)} ∧
      {u : Vector d | dot u u = 1 ∧ 0 < annealedLaw ν (TransientPaths u)} =
        {u : Vector d | dot u u = 1 ∧ 0 < dot v u} ∧
      (∀ u : Vector d, dot u u = 1 → dot v u ≤ 0 →
        annealedLaw ν (TransientPaths u) = 0) := by
  obtain ⟨v, hvℓ, hv⟩ := velocity_of_positive_escape hd ν hue ℓ hℓ hpos
  have hv0 : v ≠ 0 := by
    intro h
    subst v
    simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, lt_self_iff_false] at hvℓ
  have hvprob : annealedLaw ν (VelocityPaths v) = 1 :=
    (mem_ae_iff_prob_eq_one (measurableSet_velocityPaths v)).mp hv
  have hunique : ∀ w : Vector d, annealedLaw ν (VelocityPaths w) = 1 → w = v := by
    intro w hw
    apply hasVelocity_unique ν _ hv
    exact (mem_ae_iff_prob_eq_one (measurableSet_velocityPaths w)).mpr hw
  have hpositive (u : Vector d) (hu : dot u u = 1) :
      0 < annealedLaw ν (TransientPaths u) ↔ 0 < dot v u := by
    constructor
    · intro hp
      obtain ⟨w, hwu, hw⟩ := velocity_of_positive_escape hd ν hue u
        (unit_direction_ne_zero u hu) hp
      have hwv : w = v := hasVelocity_unique ν hw hv
      simpa only [hwv] using hwu
    · intro hp
      rw [escape_probability_one_of_velocity ν v u hv hp]
      exact zero_lt_one
  have hone (u : Vector d) (hu : dot u u = 1) :
      annealedLaw ν (TransientPaths u) = 1 ↔ 0 < annealedLaw ν (TransientPaths u) := by
    constructor
    · intro h
      rw [h]
      exact zero_lt_one
    · intro h
      exact escape_probability_one_of_velocity ν v u hv ((hpositive u hu).mp h)
  refine ⟨v, hv0, hvℓ, hvprob, hunique, ?_, ?_, ?_⟩
  · ext u
    exact and_congr_right (hone u)
  · ext u
    exact and_congr_right (hpositive u)
  · intro u hu hnonpos
    apply le_antisymm _ bot_le
    exact le_of_not_gt (fun hp => (not_lt_of_ge hnonpos) ((hpositive u hu).mp hp))

end DirectionalTransience

end OAI
