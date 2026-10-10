import Mathlib
import OAI.Probability.SKGap.Stability.FieldTonelli
import OAI.Probability.SKGap.Localization.ConditionalIntegralRate

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma conditionalFieldWeight_cylinder {n : ℕ} [NeZero n] (j t σ : ℝ)
    (E : Set (Fin n → ℝ)) (y : Fin n → ℝ) :
    conditionalFieldWeight j t σ (Set.univ ×ˢ E) y=E.indicator (fun _=>1) y := by
  by_cases hy : y∈E <;> simp [conditionalFieldWeight,hy]

lemma field_integral_scalar_bound {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ) (E : Set (Fin n → ℝ)) (hE : MeasurableSet E) :
    (∫⁻ g, ∫⁻ x, fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))
        (fun i=>t+x i) E
      ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
      ∂gaussianCoordinates (MatrixCoordinates (Fin n))) ≤
    ∫⁻ y in E, ENNReal.ofReal (scalarIntegrand j t σ y) := by
  have hh := field_integral_gaussian_reduction hj ht hσ (Set.univ ×ˢ E) (MeasurableSet.univ.prod hE)
  simp only [mem_prod,mem_univ,true_and,ofPred_mem_eq,conditionalFieldWeight_cylinder] at hh
  rw [hh,← lintegral_indicator hE]
  apply lintegral_mono
  intro y
  by_cases hy : y∈E
  · simp only [indicator_of_mem hy,mul_one]
    simpa only [mul_one] using (scalar_weighted_density_bound hj ht hσ y (le_rfl (a := (1:ℝ≥0∞))))
  · simp [hy]

theorem smalltime_bad_integral {j q₀ : ℝ} (hj : 0 < j) (hj1 : j < 1) (hq₀ : 0 < q₀) :
    ∃ t₀ σ₀ a : ℝ, 0 < t₀ ∧ 0 < σ₀ ∧ 0 < a ∧ ∃ N : ℕ,
    ∀ (n : ℕ) [NeZero n],N ≤ n → ∀ t ∈ Icc 0 t₀,∀ σ ∈ Ioc 0 σ₀,
    (∫⁻ g, ∫⁻ x, fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))
        (fun i=>t+x i) {y | q₀ ≤ overlap y}
      ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
      ∂gaussianCoordinates (MatrixCoordinates (Fin n))) ≤ ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨t₀,ht₀,δ,hδ,a,ha,N,hN⟩ := scalar_rate_iii hj hj1 hq₀
  refine ⟨t₀,min δ 1,a,ht₀,lt_min hδ zero_lt_one,ha,N,?_⟩
  intro n _ hn t ht σ hσ
  have hE : MeasurableSet {y : Fin n → ℝ | q₀ ≤ overlap y} :=
    (isClosed_le continuous_const (by unfold overlap magnetization;fun_prop)).measurableSet
  apply (field_integral_scalar_bound hj.le ht.1 hσ.1 _ hE).trans
  exact hN n hn (NeZero.pos n) t ht σ ⟨hσ.1.le,hσ.2⟩ _ hE
    (fun y hy=>by rw [scalarQMoment_empirical_overlap];exact hy)

theorem positive_time_bad_integral {j A t₀ T : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hA : 1 ≤ A) (hsub : sqrt j*A < 1) (ht₀ : 0 < t₀) (hT : t₀ ≤ T) :
    ∃ m ε σ₀ a : ℝ,0 < m ∧ 0 < ε ∧ 0 < σ₀ ∧ 0 < a ∧ ∃ N : ℕ,
    ∀ (n : ℕ) [NeZero n],N ≤ n → ∀ t ∈ Icc t₀ T,∀ σ ∈ Ioc 0 σ₀,
    (∫⁻ g, ∫⁻ x, fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))
        (fun i=>t+x i) {y | (goeMatrix (j/(n:ℝ)) g,y)∈badFieldSet n j A ε m}
      ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
      ∂gaussianCoordinates (MatrixCoordinates (Fin n))) ≤ ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨m,ε,σ₀,a,hm,hε,hσ₀,ha,N,hN⟩ := conditional_bad_integral_rate hj hj1 hA hsub ht₀ hT
  refine ⟨m,ε,σ₀,a,hm,hε,hσ₀,ha,N,?_⟩
  intro n _ hn t ht σ hσ
  have hh := field_integral_gaussian_reduction hj.le (ht₀.le.trans ht.1) hσ.1
    (badFieldFlat n j A ε m) (measurableSet_badFieldFlat _ _ _ _ _)
  change _=∫⁻ y,reducedBadDensity j t σ A ε m y at hh
  erw [hh]
  exact hN n hn t ht σ hσ
end SKGap
end
end

end OAI
