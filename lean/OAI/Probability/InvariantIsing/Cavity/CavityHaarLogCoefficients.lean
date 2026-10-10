import OAI.Probability.InvariantIsing.Cavity.CavityHaarSpinModel
import OAI.Probability.InvariantIsing.Cavity.CavityCappedBlockLog
import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientSampling

namespace OAI

/-! Capped logarithmic coefficient replacement in the actual fresh-Haar
model, with all ordinary spatial moment assumptions discharged. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_haar_capped_coefficient_limit {m q d k : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ n a, 0 < N n a)
    (μ : (n : ℕ) → (a : Fin m) → Measure (Orthogonal (N n a)))
    [∀ n a, IsProbabilityMeasure (μ n a)] [∀ n a, (μ n a).IsMulRightInvariant]
    (Ω X : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, Countable (X n)] [∀ n, MeasurableSingletonClass (X n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (e : Fin d → Fin m × Fin q)
    (v : (n : ℕ) → Ω n → (a : Fin m) → X n → Fin (N n a) → ℝ)
    (hvM : ∀ n x, Measurable (fun ω a => v n ω a x))
    (A₀ : (n : ℕ) → (a : Fin m) → Matrix (Fin (N n a)) (Fin q) ℝ)
    (hA₀ : ∀ n a, (A₀ n a).transpose * A₀ n a = 1)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hv : ∀ n ω x a, ‖(WithLp.toLp 2 (v n ω a x) :
      EuclideanSpace ℝ (Fin (N n a)))‖^2 ≤ C₀ * N n a)
    (A : (n : ℕ) → Ω n → CavityFactorBlocks d k) (hA : ∀ n, Measurable (A n))
    (A₁ : CavityFactorBlocks d k) {D : ℝ} (hD : 0 ≤ D)
    (hAb : ∀ n ω, cavityFactorSize (A n ω).1 (A n ω).2.1 (A n ω).2.2 ≤ D)
    (hA₁ : cavityFactorSize A₁.1 A₁.2.1 A₁.2.2 ≤ D)
    (hprob : ∀ δ > 0, Tendsto (fun n => (P n).real
      {ω | δ < cavityFactorDeviation (A n ω) A₁}) atTop (𝓝 0))
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (T : ℝ) (hT : 0 ≤ T) :
    let Y := fun n (p : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k)) =>
      cavitySelectedSiteProjection e (v n p.1.1) (cavityGroupHaarFrames (A₀ n) p.1.2) p.2.1
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min
        (cavityLogFactor (A n ω.1).1 (A n ω.1).2.1 (A n ω.1).2.2 (Y n (ω,x)) x.2) T)
        ∂(ν n ω.1).prod π) ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, Real.log (∫ x, Real.exp (min
        (cavityLogFactor A₁.1 A₁.2.1 A₁.2.2 (Y n (ω,x)) x.2) T)
        ∂(ν n ω.1).prod π) ∂(P n).prod (Measure.pi (μ n))) atTop (𝓝 0) := by
  intro Y
  let η n := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (N n a))
    (ν n) (hν n) π
  let M := (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C₀^2
  have hm n := cavity_haar_prior_fourth_moment (P n) (ν n) (hν n) (hN n) (μ n)
    e (v n) (hvM n) (A₀ n) (hA₀ n) hC₀ (hv n) π
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (sq_nonneg _) (cavityGaussianAbsMoment_nonneg 4)) (sq_nonneg C₀)
  have hp n : MeasurePreserving Prod.fst ((P n).prod (Measure.pi (μ n))) (P n) :=
    measurePreserving_fst
  have hprob' : ∀ δ > 0, Tendsto (fun n => ((P n).prod (Measure.pi (μ n))).real
      {ω | δ < cavityFactorDeviation (A n ω.1) A₁}) atTop (𝓝 0) := by
    intro δ hδ
    apply (hprob δ hδ).congr'
    filter_upwards [] with n
    exact (cavity_factor_deviation_pullback _ _ Prod.fst (hp n) (A n) (hA n) A₁ δ).symm
  have hout := cavity_capped_block_log_limit (fun n => (P n).prod (Measure.pi (μ n)))
    (fun n => η n) (fun n => (η n).measurable)
    (fun n ω => A n ω.1) (fun n => (hA n).comp measurable_fst) A₁ Y
    (fun n => (measurable_cavitySelectedSiteProjection e (v n) (hvM n) (A₀ n)).comp
      (measurable_fst.prodMk measurable_snd.fst))
    (fun _ p => p.2.2) (fun _ => measurable_snd.snd)
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, Y] using (hm n).1)
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, Y] using (hm n).2.1)
    hD hM hT (fun n ω => hAb n ω.1) hA₁
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, Y, M] using (hm n).2.2) hprob'
  simpa only [η, cavityHaarSpinPriorKernel_apply] using hout

end InvariantIsing

end

end OAI
