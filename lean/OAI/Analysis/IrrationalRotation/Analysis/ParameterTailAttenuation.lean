import OAI.Analysis.IrrationalRotation.Couplings.CircleConditionalAttenuation
import OAI.Analysis.IrrationalRotation.Analysis.TailScaleCover

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace Invariant233.CircleParameterLaws
open CircleParameterData

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem measurable_parameter_coordinate (i : ℕ) : Measurable (p.coordinate i) := by
  have hq : (p.q i : ℤ) ≠ 0 := by exact_mod_cast (hp.q_pos i).ne'
  change Measurable (fun x : UnitAddCircle =>
    ((AddCircle.equivIco (1 : ℝ) 0 (p.q i • x)) : ℝ))
  simpa only [natCast_zsmul] using
    (CircleWeightSupport.measurePreserving_characterRepresentative (p.q i) hq).measurable

theorem finite_parameter_conditional_attenuation
    {Ω : Type*} (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hmx : mx ≤ mΩ) (hmy : my ≤ mΩ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (x y : Ω → Circle) (hx : Measurable[mx] x) (hy : Measurable[my] y)
    (hacx : μ.map x ≪ circleMeasure) (hacy : μ.map y ≪ circleMeasure)
    (horder : ∀ᵐ ω ∂μ, ∀ i : p.Coord,
      p.coordinate i.2 (x ω) ≤ p.coordinate i.2 (y ω))
    (top bottom : ℕ → Set Ω)
    (htop : ∀ i, MeasurableSet (top i)) (hbottom : ∀ i, MeasurableSet (bottom i))
    (hindTop : iCondIndepSet mx hmx top μ) (hindBottom : iCondIndepSet my hmy bottom μ)
    (s : ℕ) (hs : 1 ≤ s) (k : ℤ) (I : Finset ℕ) (hIs : I ⊆ p.block s)
    (hI : (p.m s : ℝ) / 20 ≤ (I.card : ℝ))
    (ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ (p.m s : ℝ) * ρ) (hcost : L ≤ p.C s)
    (hforceTop : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      p.coordinate i (x ω) < 1 - Int.fract ((k : ℝ) * p.alpha θ i) →
      ω ∈ top i → 1 - Int.fract ((k : ℝ) * p.alpha θ i) ≤ p.coordinate i (y ω))
    (hforceBottom : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      1 - Int.fract ((k : ℝ) * p.alpha θ i) ≤ p.coordinate i (y ω) →
      ω ∈ bottom i → p.coordinate i (x ω) < 1 - Int.fract ((k : ℝ) * p.alpha θ i))
    (hprobTop : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      p.coordinate i (x ω) < 1 - Int.fract ((k : ℝ) * p.alpha θ i) →
      ρ / 10 ≤ (μ[(top i).indicator (fun _ => (1 : ℝ)) | mx]) ω)
    (hprobBottom : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      1 - Int.fract ((k : ℝ) * p.alpha θ i) ≤ p.coordinate i (y ω) →
      ρ / 10 ≤ (μ[(bottom i).indicator (fun _ => (1 : ℝ)) | my]) ω) :
    ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂μ, p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω) ≤
        Real.exp (-L) + H₁.indicator (fun _ => (1 : ℝ)) ω +
          H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  have hs' : s - 1 + 1 = s := by omega
  let coord (i : ℕ) (hi : i ∈ I) : p.Coord :=
    ⟨s - 1, ⟨i, by simpa only [hs'] using hIs hi⟩⟩
  have hxrep : Measurable[mx] (fun ω i => p.coordinate i (x ω)) := by
    let : MeasurableSpace Ω := mx
    exact Measurable.of_eval (fun i => (hp.measurable_parameter_coordinate i).comp hx)
  have hyrep : Measurable[my] (fun ω i => p.coordinate i (y ω)) := by
    let : MeasurableSpace Ω := my
    exact Measurable.of_eval (fun i => (hp.measurable_parameter_coordinate i).comp hy)
  have hr := hp.ae_parameter_ratio_bounds_of_map_ac μ x y
    (hx.mono hmx le_rfl).aemeasurable (hy.mono hmy le_rfl).aemeasurable hacx hacy horder
  apply CrossingAvoidance.finite_conditional_attenuation mx my hmx hmy μ I
    (fun i => 1 - Int.fract ((k : ℝ) * p.alpha θ i))
    (fun ω i => p.coordinate i (x ω)) (fun ω i => p.coordinate i (y ω))
    hxrep hyrep top bottom htop hbottom hindTop hindBottom (p.m s) ρ L hρ hL hI
    (horder.mono (fun _ h i hi => h (coord i hi)))
    hforceTop hforceBottom hprobTop hprobBottom
    (fun ω => p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω))
    (hr.mono (fun _ h => (h k).1))
  filter_upwards [hr] with ω hω
  intro i hi hcross
  have hc : L ≤ p.coordCost (coord i hi) := by
    change L ≤ p.C (s - 1 + 1)
    rwa [hs']
  exact ((hω k).2 (coord i hi) hcross).trans (Real.exp_le_exp.mpr (neg_le_neg hc))

theorem parameter_tail_conditional_attenuation
    {Ω : Type*} (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hmx : mx ≤ mΩ) (hmy : my ≤ mΩ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (x y : Ω → Circle) (hx : Measurable[mx] x) (hy : Measurable[my] y)
    (hacx : μ.map x ≪ circleMeasure) (hacy : μ.map y ≪ circleMeasure)
    (horder : ∀ᵐ ω ∂μ, ∀ i : p.Coord,
      p.coordinate i.2 (x ω) ≤ p.coordinate i.2 (y ω))
    (top bottom : Bool → ℕ → Set Ω)
    (htop : ∀ which i, MeasurableSet (top which i))
    (hbottom : ∀ which i, MeasurableSet (bottom which i))
    (hindTop : ∀ which, iCondIndepSet mx hmx (top which) μ)
    (hindBottom : ∀ which, iCondIndepSet my hmy (bottom which) μ)
    (j : ℕ) (hj : 1 ≤ j)
    (hlabels : ∀ s, j ≤ s → ∀ which : Bool, ∀ i ∈ p.block s,
      ∀ u ∈ Icc (if which then p.b s else p.a s)
        (1 - (if which then p.b s else p.a s)), ∀ᵐ ω ∂μ,
        (p.coordinate i (x ω) < u → ω ∈ top which i → u ≤ p.coordinate i (y ω)) ∧
        (u ≤ p.coordinate i (y ω) → ω ∈ bottom which i → p.coordinate i (x ω) < u) ∧
        (p.coordinate i (x ω) < u →
          (kappa s * Real.sqrt ((if which then p.b s else p.a s) / (p.m s : ℝ))) / 10 ≤
            (μ[(top which i).indicator (fun _ => (1 : ℝ)) | mx]) ω) ∧
        (u ≤ p.coordinate i (y ω) →
          (kappa s * Real.sqrt ((if which then p.b s else p.a s) / (p.m s : ℝ))) / 10 ≤
            (μ[(bottom which i).indicator (fun _ => (1 : ℝ)) | my]) ω))
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E → ∃ i ∈ p.block j,
      p.coordinate i (x ω) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) < p.coordinate i (y ω))
    (k : ℤ) (hk : (p.K j : ℝ) < |(k : ℝ)|) :
    ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-p.L j / 400)) ∧
      (∀ᵐ ω ∂μ, ω ∈ E →
        p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω) ≤
          Real.exp (-p.L j) + H₁.indicator (fun _ => (1 : ℝ)) ω +
            H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  by_cases hnear : |(k : ℝ)| ≤ p.N j / 4
  · exact CrossingAvoidance.empty_exceptional_events mx my μ E
      (fun ω => p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω))
      (Real.exp (-p.L j)) (Real.exp (-p.L j / 400)) (Real.exp_pos _).le
      (hp.ae_parameter_tagged_ratio_le_exp μ x y
        (hx.mono hmx le_rfl).aemeasurable (hy.mono hmy le_rfl).aemeasurable
        hacx hacy horder j hj k hk hnear E htag)
  · obtain ⟨s, w, I, hjs, hw, hIs, hI, hthreshold, hIntensity, hcost⟩ :=
      hp.exists_tail_crossing_set j hj k (le_of_not_ge hnear)
    obtain ⟨which, rfl⟩ : ∃ which : Bool, w = if which then p.b s else p.a s := by
      rcases hw with hw | ⟨_, hw⟩
      · exact ⟨true, by simpa using hw⟩
      · exact ⟨false, by simpa using hw⟩
    let w : ℝ := if which then p.b s else p.a s
    let ρ : ℝ := kappa s * Real.sqrt (w / (p.m s : ℝ))
    have hρ : 0 ≤ ρ := mul_nonneg (by unfold kappa; positivity) (Real.sqrt_nonneg _)
    have hl : ∀ᵐ ω ∂μ, ∀ i ∈ I,
        (p.coordinate i (x ω) < 1 - Int.fract ((k : ℝ) * p.alpha θ i) →
          ω ∈ top which i → 1 - Int.fract ((k : ℝ) * p.alpha θ i) ≤ p.coordinate i (y ω)) ∧
        (1 - Int.fract ((k : ℝ) * p.alpha θ i) ≤ p.coordinate i (y ω) →
          ω ∈ bottom which i → p.coordinate i (x ω) < 1 - Int.fract ((k : ℝ) * p.alpha θ i)) ∧
        (p.coordinate i (x ω) < 1 - Int.fract ((k : ℝ) * p.alpha θ i) →
          ρ / 10 ≤ (μ[(top which i).indicator (fun _ => (1 : ℝ)) | mx]) ω) ∧
        (1 - Int.fract ((k : ℝ) * p.alpha θ i) ≤ p.coordinate i (y ω) →
          ρ / 10 ≤ (μ[(bottom which i).indicator (fun _ => (1 : ℝ)) | my]) ω) := by
      apply ae_all_iff.mpr
      intro i
      apply ae_all_iff.mpr
      intro hi
      exact hlabels s hjs which i (hIs hi)
        (1 - Int.fract ((k : ℝ) * p.alpha θ i)) (hthreshold i hi)
    obtain ⟨H₁, H₂, hm₁, hm₂, hb₁, hb₂, hr⟩ :=
      hp.finite_parameter_conditional_attenuation mx my hmx hmy μ x y hx hy hacx hacy
        horder (top which) (bottom which) (htop which) (hbottom which)
        (hindTop which) (hindBottom which) s (hj.trans hjs) k I hIs hI
        ρ (p.L j) hρ hIntensity hcost
        (hl.mono (fun _ h i hi => (h i hi).1))
        (hl.mono (fun _ h i hi => (h i hi).2.1))
        (hl.mono (fun _ h i hi => (h i hi).2.2.1))
        (hl.mono (fun _ h i hi => (h i hi).2.2.2))
    exact ⟨H₁, H₂, hm₁, hm₂, hb₁, hb₂, hr.mono (fun _ h _ => h)⟩

end Invariant233.CircleParameterLaws

end

end OAI
