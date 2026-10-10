import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedTilt
import OAI.Probability.InvariantIsing.Cavity.CavityBoundedRegularizationError
import OAI.Probability.InvariantIsing.Cavity.CavityTailIntegral

namespace OAI

/-! Spatially restricted Gibbs tests: separate quantitative control of
the denominator floor and of the discarded full-Gibbs mass. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

theorem cavity_restricted_regularization_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (s : Ω → Set X) (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    {r : ℕ} (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    {A B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hbound : ∀ ω, ∀ x ∈ s ω, |H (ω,x)| ≤ A) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    |(∫ ω, cavityRegularizedReplicaMean (ν ω)
        ((s ω).indicator (fun x => Real.exp (H (ω,x)))) (fun σ => F (ω,σ)) δ ∂P) -
      ∫ ω, cavityWeightedReplicaMean (ν ω)
        ((s ω).indicator (fun x => Real.exp (H (ω,x)))) (fun σ => F (ω,σ)) ∂P| ≤
      B * r * δ / (Real.exp (-A) / 2) + 4 * B * ∫ ω, (ν ω).real (s ω)ᶜ ∂P := by
  classical
  let w := fun p : Ω × X => if p.2 ∈ s p.1 then Real.exp (H p) else 0
  have hw : Measurable w := Measurable.ite hs hH.exp measurable_const
  have hwb ω x : w (ω,x) ∈ Icc 0 (Real.exp A) := by
    by_cases hx : x ∈ s ω
    · simp only [w,hx,ite_true]
      exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ((le_abs_self _).trans (hbound ω x hx))⟩
    · simp only [w,hx,ite_false]
      exact ⟨le_rfl,(Real.exp_pos _).le⟩
  let t := fun ω => (ν ω).real (s ω)ᶜ
  have hsm ω : MeasurableSet (s ω) := hs.preimage measurable_prodMk_left
  have htval ω : (∫ x, (if x ∉ s ω then (1 : ℝ) else 0) ∂ν ω) = t ω := by
    simpa only [Set.indicator, Set.mem_compl_iff, Pi.one_apply] using
      (integral_indicator_one (μ := ν ω) (hsm ω).compl)
  have ht : Measurable t := by
    have hh := measurable_cavityWeightNormalizer ν hν
      (fun p : Ω × X => if p.2 ∉ s p.1 then (1 : ℝ) else 0)
      (Measurable.ite hs.compl measurable_const measurable_const)
    simpa only [cavityWeightNormalizer, htval] using hh
  have hti : Integrable t P := integrable_of_measurable_abs_le ht (c := 1)
    (fun ω => by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  have hlow ω (hω : t ω ≤ 1/2) :
      Real.exp (-A) / 2 ≤ cavityWeightNormalizer (ν ω) (fun x => w (ω,x)) := by
    exact cavity_cutoff_normalizer_half (ν ω) (s ω) (hsm ω)
      (fun x => Real.exp (H (ω,x))) (hH.comp measurable_prodMk_left).exp
      (Real.exp_pos _).le (fun x hx =>
        ⟨Real.exp_le_exp.mpr (abs_le.mp (hbound ω x hx)).1,
          Real.exp_le_exp.mpr (abs_le.mp (hbound ω x hx)).2⟩) hω
  exact cavity_bounded_regularization_mean_error P ν hν w hw F hF t ht hti
    (fun _ => measureReal_nonneg) (Real.exp_pos A).le hB hδ (by positivity) hwb hFb hlow

theorem cavity_restricted_replica_expectation_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (s : Ω → Set X) (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    {r : ℕ} (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    {A B : ℝ} (hB : 0 ≤ B) (hbound : ∀ ω, ∀ x ∈ s ω, |H (ω,x)| ≤ A)
    (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    |(∫ ω, cavityWeightedReplicaMean (ν ω)
        ((s ω).indicator (fun x => Real.exp (H (ω,x)))) (fun σ => F (ω,σ)) ∂P) -
      ∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (H (ω,x)))
        (fun σ => F (ω,σ)) ∂P| ≤
      2 * B * r * ∫ ω, ((ν ω).tilted (fun x => H (ω,x))).real (s ω)ᶜ ∂P := by
  classical
  let w := fun p : Ω × X => if p.2 ∈ s p.1 then Real.exp (H p) else 0
  have hw : Measurable w := Measurable.ite hs hH.exp measurable_const
  have hwb ω x : w (ω,x) ∈ Icc 0 (Real.exp A) := by
    by_cases hx : x ∈ s ω
    · simp only [w,hx,ite_true]
      exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ((le_abs_self _).trans (hbound ω x hx))⟩
    · simp only [w,hx,ite_false]
      exact ⟨le_rfl,(Real.exp_pos _).le⟩
  have hm := measurable_cavityRegularizedReplicaMean ν hν w hw F hF 0
  have hb ω : |cavityWeightedReplicaMean (ν ω) (fun x => w (ω,x))
      (fun σ => F (ω,σ))| ≤ B := by
    have hh := cavityRegularizedReplicaMean_abs_le (ν ω) (fun x => w (ω,x))
      (hw.comp measurable_prodMk_left) (fun σ => F (ω,σ))
      (hF.comp measurable_prodMk_left) (Real.exp_pos A).le hB (show (0:ℝ) ≤ 0 from le_rfl)
      (hwb ω) (hFb ω)
    change |cavityWeightNumerator (ν ω) (fun x => w (ω,x)) (fun σ => F (ω,σ)) /
      cavityWeightNormalizer (ν ω) (fun x => w (ω,x)) ^ r| ≤ B
    simpa only [cavityRegularizedReplicaMean, add_zero] using hh
  have hiW : Integrable (fun ω => cavityWeightedReplicaMean (ν ω)
      (fun x => w (ω,x)) (fun σ => F (ω,σ))) P := by
    apply integrable_of_measurable_abs_le _ hb
    simpa only [cavityRegularizedReplicaMean, add_zero, cavityWeightedReplicaMean] using hm
  have hiF := cavity_exp_replicaMean_integrable P ν hν H hH F hF he hFb
  have hiT := cavity_random_tilted_tail_integrable P ν hν H hH
    (fun ω => (s ω)ᶜ) hs.compl
  change |(∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => w (ω,x))
    (fun σ => F (ω,σ)) ∂P) - _| ≤ _
  rw [← integral_sub hiW hiF]
  apply abs_integral_le_integral_abs.trans
  refine (integral_mono_ae (hiW.sub hiF).abs (hiT.const_mul (2*B*r)) ?_).trans_eq ?_
  · filter_upwards [he] with ω hω
    exact cavity_restricted_replica_error (ν ω) _ hω (s ω)
      (hs.preimage measurable_prodMk_left) _ (hF.comp measurable_prodMk_left) hB (hFb ω)
  · rw [integral_const_mul]

theorem cavity_restricted_regularized_full_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (s : Ω → Set X) (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    {r : ℕ} (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    {A B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hbound : ∀ ω, ∀ x ∈ s ω, |H (ω,x)| ≤ A) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    |(∫ ω, cavityRegularizedReplicaMean (ν ω)
        ((s ω).indicator (fun x => Real.exp (H (ω,x)))) (fun σ => F (ω,σ)) δ ∂P) -
      ∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (H (ω,x)))
        (fun σ => F (ω,σ)) ∂P| ≤
      B * r * δ / (Real.exp (-A) / 2) + 4 * B * (∫ ω, (ν ω).real (s ω)ᶜ ∂P) +
        2 * B * r * ∫ ω, ((ν ω).tilted (fun x => H (ω,x))).real (s ω)ᶜ ∂P := by
  have h₁ := cavity_restricted_regularization_error P ν hν H hH s hs F hF hB hδ hbound hFb
  have h₂ := cavity_restricted_replica_expectation_error P ν hν H hH he s hs F hF hB hbound hFb
  exact (abs_sub_le _ (∫ ω, cavityWeightedReplicaMean (ν ω)
    ((s ω).indicator (fun x => Real.exp (H (ω,x)))) (fun σ => F (ω,σ)) ∂P) _).trans
      (add_le_add h₁ h₂)

theorem cavity_radial_restricted_regularized_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H R : Ω × X → ℝ) (hH : Measurable H) (hR : Measurable R)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    {r : ℕ} (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    {D B a δ : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hg : ∀ ω x, |H (ω,x)| ≤ D * (1 + R (ω,x)^2))
    (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    |(∫ ω, cavityRegularizedReplicaMean (ν ω)
        ({x | |R (ω,x)| ≤ a}.indicator (fun x => Real.exp (H (ω,x))))
        (fun σ => F (ω,σ)) δ ∂P) -
      ∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (H (ω,x)))
        (fun σ => F (ω,σ)) ∂P| ≤
      B * r * δ / (Real.exp (-D * (1+a^2)) / 2) +
        4 * B * (∫ ω, (ν ω).real {x | a < |R (ω,x)|} ∂P) +
        2 * B * r * ∫ ω, ((ν ω).tilted (fun x => H (ω,x))).real
          {x | a < |R (ω,x)|} ∂P := by
  have hg' ω x (hx : x ∈ {x | |R (ω,x)| ≤ a}) : |H (ω,x)| ≤ D*(1+a^2) := by
    have hp := pow_le_pow_left₀ (abs_nonneg (R (ω,x))) hx 2
    rw [sq_abs] at hp
    exact (hg ω x).trans (mul_le_mul_of_nonneg_left (by linarith :
      1 + R (ω,x)^2 ≤ 1+a^2) hD)
  have hh := cavity_restricted_regularized_full_error P ν hν H hH he
    (fun ω => {x | |R (ω,x)| ≤ a}) (measurableSet_le hR.abs measurable_const)
    F hF hB hδ hg' hFb
  simpa only [Set.compl_ofPred, not_le, neg_mul] using hh

end InvariantIsing

end

end OAI
