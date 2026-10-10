import OAI.Analysis.IrrationalRotation.Product.ProductScaleTagAttenuation
import OAI.Analysis.IrrationalRotation.Product.ProductScaleTailAssignment

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Invariant233.ProductScaleLaws
variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem product_tail_conditional_attenuation
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    {Ω : Type*} (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hmx : mx ≤ mΩ) (hmy : my ≤ mΩ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (x y : Ω → ProductCocycle.Space ℕ) (hx : Measurable[mx] x) (hy : Measurable[my] y)
    (hacx : μ.map x ≪ ProductCocycle.haar ℕ) (hacy : μ.map y ≪ ProductCocycle.haar ℕ)
    (horder : ∀ᵐ ω ∂μ, ∀ i,
      ProductCocycle.representative (x ω i) ≤ ProductCocycle.representative (y ω i))
    (top bottom : Bool → ℕ → Set Ω)
    (htop : ∀ which i, MeasurableSet (top which i))
    (hbottom : ∀ which i, MeasurableSet (bottom which i))
    (hindTop : ∀ which, iCondIndepSet mx hmx (top which) μ)
    (hindBottom : ∀ which, iCondIndepSet my hmy (bottom which) μ)
    (j : ℕ)
    (hb : ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ∈ Icc (1 / p.N j) (2 / p.N j))
    (hsmall : ∀ s, j < s → ProductPhases.smallPhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
    (hlarge : ∀ s, j ≤ s → ProductPhases.largePhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.N s) θ)
    (k : ℤ) (hk : (p.K j : ℝ) < |(k : ℝ)|)
    (hlabels : ∀ s, j ≤ s → ∀ which : Bool, ∀ i ∈ ProductPhases.consecutiveBlock p.m s,
      let u := 1 - Int.fract ((k : ℝ) * θ i)
      u ∈ Icc (if which then p.b s else p.a s)
        (1 - (if which then p.b s else p.a s)) → ∀ᵐ ω ∂μ,
        (ProductCocycle.representative (x ω i) < u → ω ∈ top which i → u ≤ ProductCocycle.representative (y ω i)) ∧
        (u ≤ ProductCocycle.representative (y ω i) → ω ∈ bottom which i → ProductCocycle.representative (x ω i) < u) ∧
        (ProductCocycle.representative (x ω i) < u →
          (ProductScaleData.kappa s * Real.sqrt ((if which then p.b s else p.a s) / (p.m s : ℝ))) / 10 ≤
            (μ[(top which i).indicator (fun _ => (1 : ℝ)) | mx]) ω) ∧
        (u ≤ ProductCocycle.representative (y ω i) →
          (ProductScaleData.kappa s * Real.sqrt ((if which then p.b s else p.a s) / (p.m s : ℝ))) / 10 ≤
            (μ[(bottom which i).indicator (fun _ => (1 : ℝ)) | my]) ω))
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E → ∃ i ∈ ProductPhases.consecutiveBlock p.m j,
      ProductCocycle.representative (x ω i) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) ≤ ProductCocycle.representative (y ω i))
    : ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂μ, ω ∈ E →
        ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (y ω) / ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (x ω) ≤
          Real.exp (-p.L j) + H₁.indicator (fun _ => (1 : ℝ)) ω +
            H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  have hc : ∀ i, 0 ≤ p.C (e i).1 := by
    intro i
    rw [hp.C_eq]
    exact (by norm_num : (0 : ℝ) ≤ 1).trans
      ((hp.L_ge_one _).trans (le_max_left _ _))
  by_cases hnear : |(k : ℝ)| ≤ p.N j / 4
  · apply CrossingAvoidance.empty_exceptional_events mx my μ E
      (fun ω => ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (y ω) /
        ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (x ω))
      (Real.exp (-p.L j)) (Real.exp (-p.L j / 400)) (Real.exp_pos _).le
    exact (hp.ae_all_source_tagged_ratios e he θ hθ0 hθsum j hb μ x y
      (hx.mono hmx le_rfl).aemeasurable (hy.mono hmy le_rfl).aemeasurable
      hacx hacy horder E htag).mono (fun _ h hE => h hE k hk hnear)
  · obtain ⟨s, w, I, hjs, hw, _hwidth, hIs, hI, hthreshold, hIntensity, hcost⟩ :=
      hp.exists_phase_tail_thresholds θ j hsmall hlarge k (le_of_not_ge hnear)
    obtain ⟨which, rfl⟩ : ∃ which : Bool, w = if which then p.b s else p.a s := by
      rcases hw with hw | ⟨_, hw⟩
      · exact ⟨true, by simpa using hw⟩
      · exact ⟨false, by simpa using hw⟩
    let w : ℝ := if which then p.b s else p.a s
    let ρ : ℝ := ProductScaleData.kappa s * Real.sqrt (w / (p.m s : ℝ))
    have hρ : 0 ≤ ρ := mul_nonneg
      (by unfold ProductScaleData.kappa; positivity) (Real.sqrt_nonneg _)
    have hl : ∀ᵐ ω ∂μ, ∀ i ∈ I,
        (ProductCocycle.representative (x ω i) < 1 - Int.fract ((k : ℝ) * θ i) →
          ω ∈ top which i → 1 - Int.fract ((k : ℝ) * θ i) ≤ ProductCocycle.representative (y ω i)) ∧
        (1 - Int.fract ((k : ℝ) * θ i) ≤ ProductCocycle.representative (y ω i) →
          ω ∈ bottom which i → ProductCocycle.representative (x ω i) < 1 - Int.fract ((k : ℝ) * θ i)) ∧
        (ProductCocycle.representative (x ω i) < 1 - Int.fract ((k : ℝ) * θ i) →
          ρ / 10 ≤ (μ[(top which i).indicator (fun _ => (1 : ℝ)) | mx]) ω) ∧
        (1 - Int.fract ((k : ℝ) * θ i) ≤ ProductCocycle.representative (y ω i) →
          ρ / 10 ≤ (μ[(bottom which i).indicator (fun _ => (1 : ℝ)) | my]) ω) := by
      apply ae_all_iff.mpr
      intro i
      apply ae_all_iff.mpr
      intro hi
      exact hlabels s hjs which i (hIs hi) (hthreshold i hi)
    have hcostI : ∀ i ∈ I, p.L j ≤ p.C (e i).1 := by
      intro i hi
      rw [ProductPhases.enumeration_block_of_mem p.m e he (hIs hi)]
      exact hcost
    obtain ⟨H₁, H₂, hm₁, hm₂, hb₁, hb₂, hr⟩ :=
      ProductCocycle.finite_conditional_attenuation_of_map_ac mx my hmx hmy μ
        θ (fun i => p.C (e i).1) hθ0 hθsum hc k I x y hx hy hacx hacy
        (top which) (bottom which) (htop which) (hbottom which)
        (hindTop which) (hindBottom which) (p.m s) ρ (p.L j) hρ hIntensity hI hcostI
        horder
        (hl.mono (fun _ h i hi => (h i hi).1))
        (hl.mono (fun _ h i hi => (h i hi).2.1))
        (hl.mono (fun _ h i hi => (h i hi).2.2.1))
        (hl.mono (fun _ h i hi => (h i hi).2.2.2))
    exact ⟨H₁, H₂, hm₁, hm₂, hb₁, hb₂, hr.mono (fun _ h _ => h)⟩

theorem simultaneous_product_tail_conditional_attenuation
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    {Ω : Type*} (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hmx : mx ≤ mΩ) (hmy : my ≤ mΩ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (x y : Ω → ProductCocycle.Space ℕ) (hx : Measurable[mx] x) (hy : Measurable[my] y)
    (hacx : μ.map x ≪ ProductCocycle.haar ℕ) (hacy : μ.map y ≪ ProductCocycle.haar ℕ)
    (horder : ∀ᵐ ω ∂μ, ∀ i,
      ProductCocycle.representative (x ω i) ≤ ProductCocycle.representative (y ω i))
    (top bottom : ℤ → Bool → ℕ → Set Ω)
    (htop : ∀ k which i, MeasurableSet (top k which i))
    (hbottom : ∀ k which i, MeasurableSet (bottom k which i))
    (hindTop : ∀ k which, iCondIndepSet mx hmx (top k which) μ)
    (hindBottom : ∀ k which, iCondIndepSet my hmy (bottom k which) μ)
    (j : ℕ)
    (hb : ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ∈ Icc (1 / p.N j) (2 / p.N j))
    (hsmall : ∀ s, j < s → ProductPhases.smallPhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
    (hlarge : ∀ s, j ≤ s → ProductPhases.largePhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.N s) θ)
    (hlabels : ∀ k : ℤ, ∀ s, j ≤ s → ∀ which : Bool, ∀ i ∈ ProductPhases.consecutiveBlock p.m s,
      let u := 1 - Int.fract ((k : ℝ) * θ i)
      u ∈ Icc (if which then p.b s else p.a s)
        (1 - (if which then p.b s else p.a s)) → ∀ᵐ ω ∂μ,
        (ProductCocycle.representative (x ω i) < u → ω ∈ top k which i → u ≤ ProductCocycle.representative (y ω i)) ∧
        (u ≤ ProductCocycle.representative (y ω i) → ω ∈ bottom k which i → ProductCocycle.representative (x ω i) < u) ∧
        (ProductCocycle.representative (x ω i) < u →
          (ProductScaleData.kappa s * Real.sqrt ((if which then p.b s else p.a s) / (p.m s : ℝ))) / 10 ≤
            (μ[(top k which i).indicator (fun _ => (1 : ℝ)) | mx]) ω) ∧
        (u ≤ ProductCocycle.representative (y ω i) →
          (ProductScaleData.kappa s * Real.sqrt ((if which then p.b s else p.a s) / (p.m s : ℝ))) / 10 ≤
            (μ[(bottom k which i).indicator (fun _ => (1 : ℝ)) | my]) ω))
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E → ∃ i ∈ ProductPhases.consecutiveBlock p.m j,
      ProductCocycle.representative (x ω i) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) ≤ ProductCocycle.representative (y ω i))
    : ∃ H₁ H₂ : ℤ → Set Ω,
      (∀ k, MeasurableSet (H₁ k)) ∧ (∀ k, MeasurableSet (H₂ k)) ∧
      (∀ᵐ ω ∂μ, ∀ k : ℤ, (p.K j : ℝ) < |(k : ℝ)| →
        (μ[(H₁ k).indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-p.L j / 400) ∧
        (μ[(H₂ k).indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-p.L j / 400) ∧
        (ω ∈ E →
          ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (y ω) /
            ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (x ω) ≤
            Real.exp (-p.L j) + (H₁ k).indicator (fun _ => (1 : ℝ)) ω +
              (H₂ k).indicator (fun _ => (1 : ℝ)) ω)) := by
  classical
  let R : ℤ → Ω → ℝ := fun k ω => if (p.K j : ℝ) < |(k : ℝ)| then
    ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (y ω) /
      ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) k (x ω) else 0
  have hEach (k : ℤ) : ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂μ, ω ∈ E → R k ω ≤ Real.exp (-p.L j) +
        H₁.indicator (fun _ => (1 : ℝ)) ω + H₂.indicator (fun _ => (1 : ℝ)) ω) := by
    by_cases hk : (p.K j : ℝ) < |(k : ℝ)|
    · simpa only [R, ite_eq_left hk] using hp.product_tail_conditional_attenuation
        e he θ hθ0 hθsum mx my hmx hmy μ x y hx hy hacx hacy horder
        (top k) (bottom k) (htop k) (hbottom k) (hindTop k) (hindBottom k)
        j hb hsmall hlarge k hk (hlabels k) E htag
    · apply CrossingAvoidance.empty_exceptional_events mx my μ E (R k)
        (Real.exp (-p.L j)) (Real.exp (-p.L j / 400)) (Real.exp_pos _).le
      exact Filter.Eventually.of_forall (fun _ _ => by
        simpa only [R, ite_eq_right hk] using (Real.exp_pos (-p.L j)).le)
  obtain ⟨H₁, H₂, hm₁, hm₂, h⟩ := CrossingAvoidance.simultaneous_exceptional_families
    mx my μ E R (fun _ => Real.exp (-p.L j)) (fun _ => Real.exp (-p.L j / 400)) hEach
  refine ⟨H₁, H₂, hm₁, hm₂, h.mono ?_⟩
  intro ω hω k hk
  simpa only [R, ite_eq_left hk] using hω k

end Invariant233.ProductScaleLaws

end

end OAI
