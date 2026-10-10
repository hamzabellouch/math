import OAI.Probability.InvariantIsing.Cavity.CavityHaarRestrictedWeight
import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedFactorIndicator
import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedAverage
import OAI.Probability.InvariantIsing.Cavity.CavityPriorFourthTail

namespace OAI

/-! The physical Haar prior supplies the quantitative denominator-floor
error. No inverse partition moment or full tilted Haar moment is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_haar_restricted_floor_error {m q d k r : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (hN : ∀ a, 0 < N a)
    (μ : (a : Fin m) → Measure (Orthogonal (N a)))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, (μ a).IsMulRightInvariant]
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hvM : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hv : ∀ ω x a, ‖(WithLp.toLp 2 (v ω a x) : EuclideanSpace ℝ (Fin (N a)))‖^2 ≤ C₀ * N a)
    (O : Ω → (Fin r → X) → SpectralBlock m r)
    (hO : ∀ σ, Measurable (fun ω => O ω σ))
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (T : ℝ) {B δ : ℝ} (hB : 0 < B) (hδ : 0 ≤ δ)
    (hT : cavityFactorSize K L C * (1+B^2) ≤ T)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    |(∫ p, cavityRegularizedReplicaMean ((ν p.1).prod π)
        (fun x => cavityHaarRestrictedWeight e v A₀ K L C T B (p,x))
        (cavityProjectedSpinTest (O p.1) F) δ ∂P.prod (Measure.pi μ)) -
      ∫ p, cavityWeightedReplicaMean ((ν p.1).prod π)
        (fun x => cavityHaarRestrictedWeight e v A₀ K L C T B (p,x))
        (cavityProjectedSpinTest (O p.1) F) ∂P.prod (Measure.pi μ)| ≤
      ‖F‖ * r * δ / (Real.exp (-cavityFactorSize K L C * (1+B^2)) / 2) +
        4 * ‖F‖ * ((d : ℝ)^2 * cavityGaussianAbsMoment 4 * C₀^2 / B^4) := by
  let κ := cavityHaarSpinPriorKernel (U := (a : Fin m) → Orthogonal (N a)) ν hν π
  let Y := fun z : (Ω × ((a : Fin m) → Orthogonal (N a))) × (X × Spin k) =>
    cavitySelectedSiteProjection e (v z.1.1) (cavityGroupHaarFrames A₀ z.1.2) z.2.1
  let R := fun z => ‖Y z‖
  let H := cavityHaarSpinPotential e v A₀ K L C
  let s := fun p => {x | ‖Y (p,x)‖ ≤ B}
  let G := cavityHaarSpinReplicaTest (U := (a : Fin m) → Orthogonal (N a)) O F
  have hY : Measurable Y := (measurable_cavitySelectedSiteProjection e v hvM A₀).comp
    (measurable_fst.prodMk measurable_snd.fst)
  have hH : Measurable H := measurable_cavityHaarSpinPotential e v hvM A₀ K L C
  have hG : Measurable G := measurable_cavityHaarSpinReplicaTest O hO F
  have hw p x : (s p).indicator (fun x => Real.exp (H (p,x))) x =
      cavityHaarRestrictedWeight e v A₀ K L C T B (p,x) :=
    (cavityRestrictedFactor_eq_indicator K L C T hB.le hT
      (fun x => Y (p,x)) Prod.snd x).symm
  have hg p x (hx : x ∈ s p) : |H (p,x)| ≤ cavityFactorSize K L C * (1+B^2) := by
    have hp := (sq_le_sq₀ (norm_nonneg (Y (p,x))) hB.le).mpr hx
    exact (cavity_logFactor_growth K L C (Y (p,x)) x.2).trans
      (mul_le_mul_of_nonneg_left (by linarith) (cavityFactorSize_nonneg K L C))
  have hf := cavity_restricted_regularization_error (P.prod (Measure.pi μ))
    (fun p => κ p) κ.measurable H hH s (measurableSet_le hY.norm measurable_const)
    G hG (norm_nonneg F) hδ hg (fun p σ => cavityHaarSpinReplicaTest_bound O F (p,σ))
  have hm := cavity_haar_prior_fourth_moment P ν hν hN μ e v hvM A₀ hA₀ hC₀ hv π
  have hm' : (∀ p, Integrable (fun x => R (p,x)^4) (κ p)) ∧
      Integrable (fun p => ∫ x, R (p,x)^4 ∂κ p) (P.prod (Measure.pi μ)) ∧
      (∫ p, ∫ x, R (p,x)^4 ∂κ p ∂P.prod (Measure.pi μ)) ≤
        (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C₀^2 := by
    simpa only [R,Y,κ,cavityHaarSpinPriorKernel_apply] using hm
  have ht := cavity_random_prior_fourth_tail (P.prod (Measure.pi μ))
    (fun p => κ p) κ.measurable R hY.norm (ae_of_all _ hm'.1) hm'.2.1 hB hm'.2.2
  have ht' : (∫ p, (κ p).real (s p)ᶜ ∂P.prod (Measure.pi μ)) ≤
      (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C₀^2 / B^4 := by
    simpa only [R,s,abs_norm,Set.compl_ofPred,not_le] using ht
  have hwfun p : (s p).indicator (fun x => Real.exp (H (p,x))) =
      fun x => cavityHaarRestrictedWeight e v A₀ K L C T B (p,x) := funext (hw p)
  simp only [hwfun] at hf
  have hout := hf.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left ht' (by positivity : 0 ≤ 4 * ‖F‖)))
  simpa only [κ,cavityHaarSpinPriorKernel_apply,G,cavityHaarSpinReplicaTest,neg_mul] using hout

end InvariantIsing

end

end OAI
