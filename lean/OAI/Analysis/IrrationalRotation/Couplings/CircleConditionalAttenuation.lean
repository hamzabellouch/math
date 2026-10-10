import OAI.Analysis.IrrationalRotation.Rotation.ParameterCircleCocycle
import OAI.Analysis.IrrationalRotation.Couplings.FiniteConditionalAttenuation
import OAI.Analysis.IrrationalRotation.Analysis.TaggedThresholdCrossing

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Function Set
open scoped BigOperators

namespace Invariant233.CircleWeights

theorem cocycle_ratio_le_exp_of_crossing {ι : Type*}
    (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ) (k : ℤ) (x y : UnitAddCircle) (i : ι)
    (hc : ∀ j, 0 ≤ c j) (horder : ∀ j, coordinate q j x ≤ coordinate q j y)
    (hx : HasFiniteSupport (fun j => ⌊coordinate q j x + (k : ℝ) * phase θ q j⌋))
    (hy : HasFiniteSupport (fun j => ⌊coordinate q j y + (k : ℝ) * phase θ q j⌋))
    (hcross : coordinate q i x < 1 - Int.fract ((k : ℝ) * phase θ q i) ∧
      1 - Int.fract ((k : ℝ) * phase θ q i) ≤ coordinate q i y) :
    cocycle θ q c k y / cocycle θ q c k x ≤ Real.exp (-c i) := by
  classical
  have h := FiniteSupportCocycle.exp_tsum_floor_ratio_le_finite_crossings
    (fun j => coordinate q j x) (fun j => coordinate q j y)
    (fun j => (k : ℝ) * phase θ q j) c {i}
    (fun j => coordinate_mem_Ico q j x) (fun j => coordinate_mem_Ico q j y)
    hc horder hx hy (by simpa using hcross)
  simpa only [cocycle, floorCost, Finset.sum_singleton] using h

theorem ae_all_int_finite_floor_support_of_map_ac
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (θ : ℝ) (q : ι → ℤ) (hq : ∀ i, q i ≠ 0)
    (hphase : Summable (phase θ q))
    (x : Ω → UnitAddCircle) (hx : AEMeasurable x μ)
    (hac : μ.map x ≪ (volume : Measure UnitAddCircle)) :
    ∀ᵐ ω ∂μ, ∀ k : ℤ,
      HasFiniteSupport (fun i => ⌊coordinate q i (x ω) + (k : ℝ) * phase θ q i⌋) := by
  apply ae_of_ae_map hx (p := fun z : UnitAddCircle => ∀ k : ℤ,
    HasFiniteSupport (fun i => ⌊coordinate q i z + (k : ℝ) * phase θ q i⌋))
  exact hac.ae_le (CircleWeightSupport.ae_all_int_finite_floor_support q hq
    (phase θ q) (phase_nonneg θ q) hphase)

theorem ae_all_int_ratio_bounds_of_map_ac
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (θ : ℝ) (q : ι → ℤ) (hq : ∀ i, q i ≠ 0)
    (hphase : Summable (phase θ q)) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (x y : Ω → UnitAddCircle) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ (volume : Measure UnitAddCircle))
    (hacy : μ.map y ≪ (volume : Measure UnitAddCircle))
    (horder : ∀ᵐ ω ∂μ, ∀ i, coordinate q i (x ω) ≤ coordinate q i (y ω)) :
    ∀ᵐ ω ∂μ, ∀ k : ℤ,
      cocycle θ q c k (y ω) / cocycle θ q c k (x ω) ≤ 1 ∧
      ∀ i, (coordinate q i (x ω) < 1 - Int.fract ((k : ℝ) * phase θ q i) ∧
        1 - Int.fract ((k : ℝ) * phase θ q i) ≤ coordinate q i (y ω)) →
      cocycle θ q c k (y ω) / cocycle θ q c k (x ω) ≤ Real.exp (-c i) := by
  filter_upwards [ae_all_int_finite_floor_support_of_map_ac μ θ q hq hphase x hx hacx,
    ae_all_int_finite_floor_support_of_map_ac μ θ q hq hphase y hy hacy, horder]
    with ω hxs hys hord
  intro k
  refine ⟨?_, fun i hi => cocycle_ratio_le_exp_of_crossing θ q c k (x ω) (y ω) i
    hc hord (hxs k) (hys k) hi⟩
  exact FiniteSupportCocycle.exp_tsum_floor_ratio_le_one
    (fun i => coordinate q i (x ω)) (fun i => coordinate q i (y ω))
    (phase θ q) c k hc hord (hxs k) (hys k)

theorem finite_conditional_attenuation_of_map_ac
    {ι Ω : Type*} [Countable ι]
    (mx my : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (hmx : mx ≤ mΩ) (hmy : my ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (θ : ℝ) (q : ι → ℤ) (hq : ∀ i, q i ≠ 0)
    (hphase : Summable (phase θ q)) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (k : ℤ) (I : Finset ι)
    (x y : Ω → UnitAddCircle) (hx : Measurable[mx] x) (hy : Measurable[my] y)
    (hacx : μ.map x ≪ (volume : Measure UnitAddCircle))
    (hacy : μ.map y ≪ (volume : Measure UnitAddCircle))
    (top bottom : ι → Set Ω)
    (htop : ∀ i, MeasurableSet (top i)) (hbottom : ∀ i, MeasurableSet (bottom i))
    (hindTop : iCondIndepSet mx hmx top μ) (hindBottom : iCondIndepSet my hmy bottom μ)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ)
    (hI : m / 20 ≤ (I.card : ℝ)) (hcost : ∀ i ∈ I, L ≤ c i)
    (horder : ∀ᵐ ω ∂μ, ∀ i, coordinate q i (x ω) ≤ coordinate q i (y ω))
    (hforceTop : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      coordinate q i (x ω) < 1 - Int.fract ((k : ℝ) * phase θ q i) →
      ω ∈ top i → 1 - Int.fract ((k : ℝ) * phase θ q i) ≤ coordinate q i (y ω))
    (hforceBottom : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      1 - Int.fract ((k : ℝ) * phase θ q i) ≤ coordinate q i (y ω) →
      ω ∈ bottom i → coordinate q i (x ω) < 1 - Int.fract ((k : ℝ) * phase θ q i))
    (hprobTop : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      coordinate q i (x ω) < 1 - Int.fract ((k : ℝ) * phase θ q i) →
      ρ / 10 ≤ (μ[(top i).indicator (fun _ => (1 : ℝ)) | mx]) ω)
    (hprobBottom : ∀ᵐ ω ∂μ, ∀ i ∈ I,
      1 - Int.fract ((k : ℝ) * phase θ q i) ≤ coordinate q i (y ω) →
      ρ / 10 ≤ (μ[(bottom i).indicator (fun _ => (1 : ℝ)) | my]) ω) :
    ∃ H₁ H₂ : Set Ω, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂μ, (μ[H₁.indicator (fun _ => (1 : ℝ)) | mx]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂μ, (μ[H₂.indicator (fun _ => (1 : ℝ)) | my]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂μ, cocycle θ q c k (y ω) / cocycle θ q c k (x ω) ≤
        Real.exp (-L) + H₁.indicator (fun _ => (1 : ℝ)) ω +
          H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  have hxrep : Measurable[mx] (fun ω i => coordinate q i (x ω)) := by
    let : MeasurableSpace Ω := mx
    exact Measurable.of_eval (fun i =>
      (CircleWeightSupport.measurePreserving_characterRepresentative (q i) (hq i)).measurable.comp hx)
  have hyrep : Measurable[my] (fun ω i => coordinate q i (y ω)) := by
    let : MeasurableSpace Ω := my
    exact Measurable.of_eval (fun i =>
      (CircleWeightSupport.measurePreserving_characterRepresentative (q i) (hq i)).measurable.comp hy)
  have hr := ae_all_int_ratio_bounds_of_map_ac μ θ q hq hphase c hc x y
    (hx.mono hmx le_rfl).aemeasurable (hy.mono hmy le_rfl).aemeasurable hacx hacy horder
  apply CrossingAvoidance.finite_conditional_attenuation mx my hmx hmy μ I
    (fun i => 1 - Int.fract ((k : ℝ) * phase θ q i))
    (fun ω i => coordinate q i (x ω)) (fun ω i => coordinate q i (y ω))
    hxrep hyrep top bottom htop hbottom hindTop hindBottom m ρ L hρ hL hI
    (horder.mono (fun _ h i _ => h i)) hforceTop hforceBottom hprobTop hprobBottom
    (fun ω => cocycle θ q c k (y ω) / cocycle θ q c k (x ω))
    (hr.mono (fun _ h => (h k).1))
  filter_upwards [hr] with ω hω
  intro i hi hcross
  exact ((hω k).2 i hcross).trans (Real.exp_le_exp.mpr (neg_le_neg (hcost i hi)))

theorem ae_tagged_ratio_le_exp_of_map_ac
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (θ : ℝ) (q : ι → ℤ) (hq : ∀ i, q i ≠ 0)
    (hphase : Summable (phase θ q)) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (x y : Ω → UnitAddCircle) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ (volume : Measure UnitAddCircle))
    (hacy : μ.map y ≪ (volume : Measure UnitAddCircle))
    (horder : ∀ᵐ ω ∂μ, ∀ i, coordinate q i (x ω) ≤ coordinate q i (y ω))
    (m K L : ℝ) (hm : 2 ≤ m) (hK : 0 < K) (k : ℤ)
    (hklo : K < |(k : ℝ)|) (hkhi : |(k : ℝ)| ≤ m * K / 4)
    (I : Finset ι) (hlo : ∀ i ∈ I, 1 / (m * K) < phase θ q i)
    (hhi : ∀ i ∈ I, phase θ q i < 2 / (m * K)) (hcost : ∀ i ∈ I, L ≤ c i)
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E → ∃ i ∈ I,
      coordinate q i (x ω) < 1 / m ∧ 1 - 1 / m < coordinate q i (y ω)) :
    ∀ᵐ ω ∂μ, ω ∈ E →
      cocycle θ q c k (y ω) / cocycle θ q c k (x ω) ≤ Real.exp (-L) := by
  filter_upwards [ae_all_int_ratio_bounds_of_map_ac μ θ q hq hphase c hc x y
    hx hy hacx hacy horder, htag] with ω hr ht
  intro hE
  obtain ⟨i, hi, hxi, hyi⟩ := ht hE
  have hcross := FloorCocycle.tagged_crossing_of_window k hm hK
    (hlo i hi) (hhi i hi) hklo hkhi hxi hyi
  exact ((hr k).2 i hcross).trans (Real.exp_le_exp.mpr (neg_le_neg (hcost i hi)))

end Invariant233.CircleWeights

namespace Invariant233.CircleParameterLaws

theorem ae_parameter_ratio_bounds_of_map_ac
    {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → Circle) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ circleMeasure) (hacy : μ.map y ≪ circleMeasure)
    (horder : ∀ᵐ ω ∂μ, ∀ i : p.Coord, p.coordinate i.2 (x ω) ≤ p.coordinate i.2 (y ω)) :
    ∀ᵐ ω ∂μ, ∀ k : ℤ,
      p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω) ≤ 1 ∧
      ∀ i : p.Coord,
        (p.coordinate i.2 (x ω) < 1 - Int.fract ((k : ℝ) * p.alpha θ i.2) ∧
          1 - Int.fract ((k : ℝ) * p.alpha θ i.2) ≤ p.coordinate i.2 (y ω)) →
        p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω) ≤ Real.exp (-p.coordCost i) := by
  have hord : ∀ᵐ ω ∂μ, ∀ i : p.Coord,
      CircleWeights.coordinate p.coordFrequency i (x ω) ≤
        CircleWeights.coordinate p.coordFrequency i (y ω) := by
    simpa only [p.coord_coordinate_eq] using horder
  simpa only [CircleParameterData.floorCocycle, p.coord_coordinate_eq, p.coord_phase_eq] using
    CircleWeights.ae_all_int_ratio_bounds_of_map_ac μ θ p.coordFrequency
      hp.coordFrequency_ne_zero hp.summable_coord_phases p.coordCost
      (fun i => (hp.coordCost_pos i).le) x y hx hy hacx hacy hord

theorem ae_parameter_tagged_ratio_le_exp
    {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → Circle) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hacx : μ.map x ≪ circleMeasure) (hacy : μ.map y ≪ circleMeasure)
    (horder : ∀ᵐ ω ∂μ, ∀ i : p.Coord, p.coordinate i.2 (x ω) ≤ p.coordinate i.2 (y ω))
    (j : ℕ) (hj : 1 ≤ j) (k : ℤ)
    (hklo : (p.K j : ℝ) < |(k : ℝ)|) (hkhi : |(k : ℝ)| ≤ p.N j / 4)
    (E : Set Ω) (htag : ∀ᵐ ω ∂μ, ω ∈ E → ∃ i ∈ p.block j,
      p.coordinate i (x ω) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) < p.coordinate i (y ω)) :
    ∀ᵐ ω ∂μ, ω ∈ E →
      p.floorCocycle θ k (y ω) / p.floorCocycle θ k (x ω) ≤ Real.exp (-p.L j) := by
  filter_upwards [hp.ae_parameter_ratio_bounds_of_map_ac μ x y hx hy hacx hacy horder,
    htag] with ω hr ht
  intro hE
  obtain ⟨i, hi, hxi, hyi⟩ := ht hE
  have hj' : j - 1 + 1 = j := by omega
  let a : p.Coord := ⟨j - 1, ⟨i, by simpa only [hj'] using hi⟩⟩
  have hm : (2 : ℝ) ≤ (p.m j : ℝ) := by exact_mod_cast (le_trans (by norm_num) (hp.m_ge_200 j hj))
  have hK : (0 : ℝ) < (p.K j : ℝ) := by exact_mod_cast hp.K_pos j hj
  have hphase := hp.phase_bounds j hj i hi
  have hcross := FloorCocycle.tagged_crossing_of_window k hm hK
    hphase.1 hphase.2 hklo hkhi hxi hyi
  have hratio := (hr k).2 a hcross
  have hcost : p.L j ≤ p.coordCost a := by
    change p.L j ≤ p.C (j - 1 + 1)
    rw [hj', hp.C_eq j hj]
    exact le_max_left _ _
  exact hratio.trans (Real.exp_le_exp.mpr (neg_le_neg hcost))

end Invariant233.CircleParameterLaws

end

end OAI
