import OAI.Analysis.IrrationalRotation.Product.ProductCocycle
import OAI.Analysis.IrrationalRotation.Couplings.FiniteConditionalAttenuation
import OAI.Analysis.IrrationalRotation.Analysis.TaggedThresholdCrossing

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Function Set
open scoped BigOperators

namespace Invariant233.ProductCocycle

theorem cocycleVersion_ratio_le_exp_of_crossing {ι : Type*}
    (θ c : ι → ℝ) (k : ℤ) (x y : Space ι) (i : ι)
    (hc : ∀ j, 0 ≤ c j)
    (horder : ∀ j, representative (x j) ≤ representative (y j))
    (hx : HasFiniteSupport (fun j => ⌊representative (x j) + (k : ℝ) * θ j⌋))
    (hy : HasFiniteSupport (fun j => ⌊representative (y j) + (k : ℝ) * θ j⌋))
    (hcross : representative (x i) < 1 - Int.fract ((k : ℝ) * θ i) ∧
      1 - Int.fract ((k : ℝ) * θ i) ≤ representative (y i)) :
    cocycleVersion θ c k y / cocycleVersion θ c k x ≤ Real.exp (-c i) := by
  classical
  have h := FiniteSupportCocycle.exp_tsum_floor_ratio_le_finite_crossings
    (fun j => representative (x j)) (fun j => representative (y j))
    (fun j => (k : ℝ) * θ j) c {i}
    (fun j => representative_mem_Ico (x j)) (fun j => representative_mem_Ico (y j))
    hc horder hx hy (by simpa using hcross)
  simpa only [cocycleVersion, Finset.sum_singleton] using h

theorem ae_all_int_finite_floor_support_of_map_ac
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (x : Ω → Space ι) (hx : AEMeasurable x μ) (hac : μ.map x ≪ haar ι) :
    ∀ᵐ ω ∂μ, ∀ k : ℤ,
      HasFiniteSupport (fun i => ⌊representative (x ω i) + (k : ℝ) * θ i⌋) := by
  apply ae_of_ae_map hx (p := fun z : Space ι => ∀ k : ℤ,
    HasFiniteSupport (fun i => ⌊representative (z i) + (k : ℝ) * θ i⌋))
  apply hac.ae_le
  exact CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ

theorem ae_all_int_ratio_bounds_of_map_ac
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (θ c : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : Summable θ) (hc : ∀ i, 0 ≤ c i)
    (x y : Ω → Space ι) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ haar ι) (hacy : μ.map y ≪ haar ι)
    (horder : ∀ᵐ ω ∂μ, ∀ i, representative (x ω i) ≤ representative (y ω i)) :
    ∀ᵐ ω ∂μ, ∀ k : ℤ,
      cocycleVersion θ c k (y ω) / cocycleVersion θ c k (x ω) ≤ 1 ∧
      ∀ i, (representative (x ω i) < 1 - Int.fract ((k : ℝ) * θ i) ∧
        1 - Int.fract ((k : ℝ) * θ i) ≤ representative (y ω i)) →
      cocycleVersion θ c k (y ω) / cocycleVersion θ c k (x ω) ≤ Real.exp (-c i) := by
  filter_upwards [ae_all_int_finite_floor_support_of_map_ac μ θ hθ0 hθ x hx hacx,
    ae_all_int_finite_floor_support_of_map_ac μ θ hθ0 hθ y hy hacy, horder]
    with ω hxs hys hord
  intro k
  exact ⟨cocycleVersion_ratio_le_one θ c k (x ω) (y ω) hc hord (hxs k) (hys k),
    fun i hi => cocycleVersion_ratio_le_exp_of_crossing θ c k (x ω) (y ω) i
      hc hord (hxs k) (hys k) hi⟩

theorem finite_conditional_attenuation_of_map_ac
    {ι Ω : Type*} [Countable ι]
    (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (hmx : mx ≤ mΩ) (hmy : my ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (θ c : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (k : ℤ) (I : Finset ι)
    (x y : Ω → Space ι) (hx : Measurable[mx] x) (hy : Measurable[my] y)
    (hacx : μ.map x ≪ haar ι) (hacy : μ.map y ≪ haar ι)
    (top bottom : ι → Set Ω)
    (htop : ∀ i, MeasurableSet (top i)) (hbottom : ∀ i, MeasurableSet (bottom i))
    (hindTop : iCondIndepSet mx hmx top μ) (hindBottom : iCondIndepSet my hmy bottom μ)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ)
    (hI : m / 20 ≤ (I.card : ℝ)) (hcost : ∀ i ∈ I, L ≤ c i)
    (horder : ∀ᵐ ω ∂μ, ∀ i, representative (x ω i) ≤ representative (y ω i))
    (hforceTop : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      representative (x ω i) < 1 - Int.fract ((k : ℝ) * θ i) →
      ω ∈ top i → 1 - Int.fract ((k : ℝ) * θ i) ≤ representative (y ω i))
    (hforceBottom : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      1 - Int.fract ((k : ℝ) * θ i) ≤ representative (y ω i) →
      ω ∈ bottom i → representative (x ω i) < 1 - Int.fract ((k : ℝ) * θ i))
    (hprobTop : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      representative (x ω i) < 1 - Int.fract ((k : ℝ) * θ i) →
      ρ / 10 ≤ (μ[(top i).indicator (fun _ => (1 : ℝ)) | mx]) ω)
    (hprobBottom : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      1 - Int.fract ((k : ℝ) * θ i) ≤ representative (y ω i) →
      ρ / 10 ≤ (μ[(bottom i).indicator (fun _ => (1 : ℝ)) | my]) ω) :
    ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂μ, cocycleVersion θ c k (y ω) / cocycleVersion θ c k (x ω) ≤
        Real.exp (-L) + H₁.indicator (fun _ => (1 : ℝ)) ω +
          H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  have hxrep : Measurable[mx] (fun ω i => representative (x ω i)) := by
    let : MeasurableSpace Ω := mx
    exact Measurable.of_eval (fun i => measurable_representative.comp ((measurable_pi_apply i).comp hx))
  have hyrep : Measurable[my] (fun ω i => representative (y ω i)) := by
    let : MeasurableSpace Ω := my
    exact Measurable.of_eval (fun i => measurable_representative.comp ((measurable_pi_apply i).comp hy))
  have hr := ae_all_int_ratio_bounds_of_map_ac μ θ c hθ0 hθ hc x y
    (hx.mono hmx le_rfl).aemeasurable (hy.mono hmy le_rfl).aemeasurable hacx hacy horder
  apply CrossingAvoidance.finite_conditional_attenuation mx my hmx hmy μ I
    (fun i => 1 - Int.fract ((k : ℝ) * θ i))
    (fun ω i => representative (x ω i)) (fun ω i => representative (y ω i))
    hxrep hyrep top bottom htop hbottom hindTop hindBottom m ρ L hρ hL hI
    (horder.mono (fun _ h i _ => h i)) hforceTop hforceBottom hprobTop hprobBottom
    (fun ω => cocycleVersion θ c k (y ω) / cocycleVersion θ c k (x ω))
    (hr.mono (fun _ h => (h k).1))
  filter_upwards [hr] with ω hω
  intro i hi hcross
  exact ((hω k).2 i hcross).trans (Real.exp_le_exp.mpr (neg_le_neg (hcost i hi)))

theorem ae_tagged_ratio_le_exp_of_map_ac
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (θ c : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : Summable θ) (hc : ∀ i, 0 ≤ c i)
    (x y : Ω → Space ι) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ haar ι) (hacy : μ.map y ≪ haar ι)
    (horder : ∀ᵐ ω ∂μ, ∀ i, representative (x ω i) ≤ representative (y ω i))
    (m K L : ℝ) (hm : 2 ≤ m) (hK : 0 < K) (k : ℤ)
    (hklo : K < |(k : ℝ)|) (hkhi : |(k : ℝ)| ≤ m * K / 4)
    (I : Finset ι) (hlo : ∀ i ∈ I, 1 / (m * K) < θ i)
    (hhi : ∀ i ∈ I, θ i < 2 / (m * K)) (hcost : ∀ i ∈ I, L ≤ c i)
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E → ∃ i ∈ I,
      representative (x ω i) < 1 / m ∧ 1 - 1 / m < representative (y ω i)) :
    ∀ᵐ ω ∂μ, ω ∈ E →
      cocycleVersion θ c k (y ω) / cocycleVersion θ c k (x ω) ≤ Real.exp (-L) := by
  filter_upwards [ae_all_int_ratio_bounds_of_map_ac μ θ c hθ0 hθ hc x y
    hx hy hacx hacy horder, htag] with ω hr ht
  intro hE
  obtain ⟨i, hi, hxi, hyi⟩ := ht hE
  have hcross := FloorCocycle.tagged_crossing_of_window k hm hK
    (hlo i hi) (hhi i hi) hklo hkhi hxi hyi
  exact ((hr k).2 i hcross).trans (Real.exp_le_exp.mpr (neg_le_neg (hcost i hi)))

end Invariant233.ProductCocycle

end

end OAI
