import OAI.Probability.InvariantIsing.Cavity.CavityVanishingPenalty
import OAI.Probability.InvariantIsing.Cavity.CavityHaarSpinModel

namespace OAI

/-! Removal of the geometric quadratic penalty for the physical
fresh-Haar model.  Its required moments come from the actual Haar frame. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_haar_quadratic_penalty {m q d k : ℕ}
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
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T : ℝ) (hT : 0 ≤ T) (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hδlim : Tendsto δ atTop (𝓝 0)) :
    let H := fun n => cavityHaarSpinPotential e (v n) (A₀ n) K L C
    let R := fun n (p : (Ω n × ((a : Fin m) → Orthogonal (N n a))) × (X n × Spin k)) =>
      ‖cavitySelectedSiteProjection e (v n p.1.1) (cavityGroupHaarFrames (A₀ n) p.1.2) p.2.1‖
    Tendsto (fun n =>
      (∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T) ∂(ν n ω.1).prod π)
        ∂(P n).prod (Measure.pi (μ n))) -
      ∫ ω, Real.log (∫ x, Real.exp (min (H n (ω,x)) T - δ n * (1 + R n (ω,x)^2))
        ∂(ν n ω.1).prod π) ∂(P n).prod (Measure.pi (μ n))) atTop (𝓝 0) := by
  intro H R
  let η n := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (N n a))
    (ν n) (hν n) π
  let M := (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C₀^2
  have hm n := cavity_haar_prior_fourth_moment (P n) (ν n) (hν n) (hN n) (μ n)
    e (v n) (hvM n) (A₀ n) (hA₀ n) hC₀ (hv n) π
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (sq_nonneg _) (cavityGaussianAbsMoment_nonneg 4)) (sq_nonneg C₀)
  let δ' n := min (δ n) 1
  have hδ' : Tendsto δ' atTop (𝓝 0) := by
    simpa only [min_eq_left zero_le_one] using hδlim.min (tendsto_const_nhds (x := (1:ℝ)))
  have hout := cavity_vanishing_quadratic_penalty (fun n => (P n).prod (Measure.pi (μ n)))
    (fun n => η n) (fun n => (η n).measurable) H R
    (fun n => measurable_cavityHaarSpinPotential e (v n) (hvM n) (A₀ n) K L C)
    (fun n => ((measurable_cavitySelectedSiteProjection e (v n) (hvM n) (A₀ n)).comp
      (measurable_fst.prodMk measurable_snd.fst)).norm)
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, R] using (hm n).1)
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, R] using (hm n).2.1)
    (cavityFactorSize_nonneg K L C) hM hT
    (fun n ω x => cavity_logFactor_growth K L C _ _)
    (fun n => by simpa only [η, cavityHaarSpinPriorKernel_apply, R, M] using (hm n).2.2)
    δ' (fun n => le_min (hδ n) zero_le_one) (fun n => min_le_right _ _) hδ'
  apply hout.congr'
  filter_upwards [hδlim.eventually (eventually_lt_nhds zero_lt_one)] with n hn
  simp only [η, cavityHaarSpinPriorKernel_apply, δ', min_eq_left hn.le]

end InvariantIsing

end

end OAI
