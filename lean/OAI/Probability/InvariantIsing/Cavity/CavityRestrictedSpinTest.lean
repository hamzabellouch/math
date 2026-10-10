import OAI.Probability.InvariantIsing.Cavity.CavityReplicaRadius

namespace OAI

/-! Hard spatial restrictions of the actual capped spin replica test.
Their only discontinuity lies on the maximum-radius boundary. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityRestrictedSpinReplicaValue {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (z : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) : ℝ :=
  ∫ ε : Fin r → Spin k,
    (∏ i, if 1+‖J z.2 i‖^2 ≤ 1+B^2 then
      Real.exp (min (cavityLogFactor K L C (J z.2 i) (ε i)) T) else 0) * F (z.1, ε)
      ∂Measure.pi (fun _ => π)

lemma cavityRestrictedSpinReplicaValue_eq {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    cavityRestrictedSpinReplicaValue K L C T B J π F =
      {z | cavityReplicaRadius J z ≤ B}.indicator
        (cavityCappedSpinReplicaValue K L C T J π F) := by
  classical
  funext z
  by_cases hz : cavityReplicaRadius J z ≤ B
  · rw [Set.indicator_of_mem (show z ∈ {z | cavityReplicaRadius J z ≤ B} from hz)]
    unfold cavityRestrictedSpinReplicaValue cavityCappedSpinReplicaValue
    have hi := (cavityReplicaRadius_le_iff J z hB).mp hz
    simp only [hi, ite_true]
  · rw [Set.indicator_of_notMem (show z ∉ {z | cavityReplicaRadius J z ≤ B} from hz)]
    have hnot : ¬ ∀ i, 1+‖J z.2 i‖^2 ≤ 1+B^2 :=
      fun hi => hz ((cavityReplicaRadius_le_iff J z hB).mpr hi)
    obtain ⟨i,hi⟩ := not_forall.mp hnot
    have hp (ε : Fin r → Spin k) :
        (∏ j, if 1+‖J z.2 j‖^2 ≤ 1+B^2 then
          Real.exp (min (cavityLogFactor K L C (J z.2 j) (ε j)) T) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    simp only [cavityRestrictedSpinReplicaValue,hp,zero_mul,integral_zero]

lemma cavity_restricted_factor_cap_inactive {d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (hT : cavityFactorSize K L C * (1+B^2) ≤ T)
    (y : EuclideanSpace ℝ (Fin d)) (ε : Spin k) :
    (if 1+‖y‖^2 ≤ 1+B^2 then Real.exp (min (cavityLogFactor K L C y ε) T) else 0) =
      (if 1+‖y‖^2 ≤ 1+B^2 then Real.exp (cavityLogFactor K L C y ε) else 0) := by
  by_cases hy : 1+‖y‖^2 ≤ 1+B^2
  · rw [ite_eq_left hy,ite_eq_left hy,min_eq_left]
    exact (le_abs_self _).trans ((cavity_logFactor_growth K L C y ε).trans
      ((mul_le_mul_of_nonneg_left hy (cavityFactorSize_nonneg K L C)).trans hT))
  · rw [ite_eq_right hy,ite_eq_right hy]

lemma measurable_cavityRestrictedSpinReplicaValue {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Measurable (cavityRestrictedSpinReplicaValue K L C T B J π F) := by
  rw [cavityRestrictedSpinReplicaValue_eq K L C T hB J π F]
  exact (cavityCappedSpinReplicaTest K L C T J π F).continuous.measurable.indicator
    (measurableSet_le (continuous_cavityReplicaRadius J).measurable measurable_const)

lemma cavityRestrictedSpinReplicaValue_bound {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (z : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :
    ‖cavityRestrictedSpinReplicaValue K L C T B J π F z‖ ≤ (Real.exp T)^r * ‖F‖ := by
  rw [cavityRestrictedSpinReplicaValue_eq K L C T hB J π F]
  by_cases hz : cavityReplicaRadius J z ≤ B
  · rw [Set.indicator_of_mem (show z ∈ {z | cavityReplicaRadius J z ≤ B} from hz)]
    exact cavityCappedSpinReplicaValue_bound K L C T J π F z
  · rw [Set.indicator_of_notMem (show z ∉ {z | cavityReplicaRadius J z ≤ B} from hz),norm_zero]
    positivity

end InvariantIsing

end

end OAI
