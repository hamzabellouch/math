import OAI.Probability.InvariantIsing.Cavity.CavityHaarLogCoefficients
import OAI.Probability.InvariantIsing.Cavity.CavityVanishingPenalty

namespace OAI

/-! Removal of the geometric penalty before replacing the random
compression blocks.  The Haar fourth moment is uniform in those blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_haar_variable_quadratic_penalty {m q d k : ℕ}
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
    {D : ℝ} (hD : 0 ≤ D)
    (hAb : ∀ n ω, cavityFactorSize (A n ω).1 (A n ω).2.1 (A n ω).2.2 ≤ D)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (T : ℝ) (hT : 0 ≤ T)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0)) :
    let Y := fun n (p : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k)) =>
      cavitySelectedSiteProjection e (v n p.1.1) (cavityGroupHaarFrames (A₀ n) p.1.2) p.2.1
    let H := fun n (p : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k)) =>
      cavityLogFactor (A n p.1.1).1 (A n p.1.1).2.1 (A n p.1.1).2.2 (Y n p) p.2.2
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T) ∂(ν n ω.1).prod π)
        ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T - δ n*(1+‖Y n (ω,x)‖^2))
        ∂(ν n ω.1).prod π) ∂(P n).prod (Measure.pi (μ n))) atTop (𝓝 0) := by
  intro Y H
  let η n := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (N n a))
    (ν n) (hν n) π
  let M := (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C₀^2
  have hm n := cavity_haar_prior_fourth_moment (P n) (ν n) (hν n) (hN n) (μ n)
    e (v n) (hvM n) (A₀ n) (hA₀ n) hC₀ (hv n) π
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (sq_nonneg _) (cavityGaussianAbsMoment_nonneg 4)) (sq_nonneg C₀)
  have hY n : Measurable (Y n) :=
    (measurable_cavitySelectedSiteProjection e (v n) (hvM n) (A₀ n)).comp
      (measurable_fst.prodMk measurable_snd.fst)
  have hH n : Measurable (H n) := by
    have hA' : Measurable (fun p : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k) =>
        A n p.1.1) := (hA n).comp measurable_fst.fst
    have hε : Measurable (fun p : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k) =>
        p.2.2) := measurable_snd.snd
    dsimp only [H]
    unfold cavityLogFactor cavityQuadratic
    fun_prop
  let δ' n := min (δ n) 1
  have hδ' : Tendsto δ' atTop (𝓝 0) := by
    simpa only [min_eq_left zero_le_one] using hδlim.min (tendsto_const_nhds (x := (1:ℝ)))
  have hout := cavity_vanishing_quadratic_penalty (fun n => (P n).prod (Measure.pi (μ n)))
    (fun n => η n) (fun n => (η n).measurable) H (fun n p => ‖Y n p‖) hH
    (fun n => (hY n).norm)
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, Y] using (hm n).1)
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, Y] using (hm n).2.1)
    hD hM hT
    (fun n ω x => (cavity_logFactor_growth _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_right (hAb n ω.1) (by positivity)))
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, Y, M] using (hm n).2.2)
    δ' (fun n => le_min (hδ n) zero_le_one) (fun n => min_le_right _ _) hδ'
  apply hout.congr'
  filter_upwards [hδlim.eventually (eventually_lt_nhds zero_lt_one)] with n hn
  simp only [η, cavityHaarSpinPriorKernel_apply, δ', min_eq_left hn.le]

end InvariantIsing

end

end OAI
