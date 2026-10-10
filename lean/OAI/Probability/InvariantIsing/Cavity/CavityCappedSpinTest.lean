import OAI.Probability.InvariantIsing.Cavity.CavityContinuousCutoff
import OAI.Probability.InvariantIsing.Cavity.CavityHaarCascadeMatch

namespace OAI

/-! The paper's finite-spin cavity factor as a bounded continuous replica
test, ready for the actual fresh-Haar / recalculated-cascade comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityCappedSpinReplicaValue {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k))
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (z : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) : ℝ :=
  ∫ ε : Fin r → Spin k,
    (∏ i, Real.exp (min (cavityLogFactor K L C (J z.2 i) (ε i)) T)) * F (z.1, ε)
      ∂Measure.pi (fun _ => π)

lemma cavityCappedSpinReplicaValue_bound {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (z : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :
    ‖cavityCappedSpinReplicaValue K L C T J π F z‖ ≤ (Real.exp T)^r * ‖F‖ := by
  have hb (ε : Fin r → Spin k) :
      ‖(∏ i, Real.exp (min (cavityLogFactor K L C (J z.2 i) (ε i)) T)) * F (z.1, ε)‖ ≤
        (Real.exp T)^r * ‖F‖ := by
    rw [norm_mul]
    apply mul_le_mul _ (F.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))]
    exact (Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
      (fun _ _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  have h := norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : Fin r => π)) (ae_of_all _ hb)
  simpa only [cavityCappedSpinReplicaValue, probReal_univ, mul_one] using h

lemma continuous_cavityCappedSpinReplicaValue {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    Continuous (cavityCappedSpinReplicaValue K L C T J π F) := by
  have hp (ε : Fin r → Spin k) : Continuous
      (fun z : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) =>
        (∏ i, Real.exp (min (cavityLogFactor K L C (J z.2 i) (ε i)) T)) * F (z.1, ε)) := by
    apply Continuous.mul
    · apply continuous_finsetProd
      intro i _
      exact Real.continuous_exp.comp
        (((continuous_cavityLogFactor K L C (ε i)).comp
          ((continuous_apply i).comp (J.continuous.comp continuous_snd))).min continuous_const)
    · exact F.continuous.comp (continuous_fst.prodMk continuous_const)
  unfold cavityCappedSpinReplicaValue
  apply continuous_of_dominated (bound := fun _ => (Real.exp T)^r * ‖F‖)
  · intro z
    exact (measurable_of_countable _).aestronglyMeasurable
  · intro z
    apply ae_of_all
    intro ε
    rw [norm_mul]
    apply mul_le_mul _ (F.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))]
    exact (Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
      (fun _ _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  · exact integrable_const _
  · exact ae_of_all _ hp

def cavityCappedSpinReplicaTest {m r q d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (cavityCappedSpinReplicaValue K L C T J π F)
    (continuous_cavityCappedSpinReplicaValue K L C T J π F) ((Real.exp T)^r * ‖F‖)
    (cavityCappedSpinReplicaValue_bound K L C T J π F)

end InvariantIsing

end

end OAI
