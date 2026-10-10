import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace OAI

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal NNReal

namespace Balanced.ProfileWeakDetection

variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem prod_eq_mass_smul_normalized [Nonempty X] [Nonempty Y]
    (μ : FiniteMeasure X) (ν : FiniteMeasure Y) :
    μ.prod ν = (μ.mass * ν.mass) •
      (μ.normalize.prod ν.normalize).toFiniteMeasure := by
  apply Subtype.ext
  change (μ : Measure X).prod (ν : Measure Y) = _
  nth_rw 1 [μ.self_eq_mass_smul_normalize, ν.self_eq_mass_smul_normalize]
  simp only [FiniteMeasure.toMeasure_smul, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  simp only [mul_comm]
  rfl

theorem tendsto_finiteMeasure_prod
    [Nonempty X] [Nonempty Y] [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {l : Filter I} {μn : I → FiniteMeasure X} {νn : I → FiniteMeasure Y}
    {μ : FiniteMeasure X} {ν : FiniteMeasure Y}
    (hμ : Tendsto μn l (𝓝 μ)) (hν : Tendsto νn l (𝓝 ν)) :
    Tendsto (fun n => (μn n).prod (νn n)) l (𝓝 (μ.prod ν)) := by
  have hm := hμ.mass.mul hν.mass
  by_cases hμ0 : μ = 0
  · rw [hμ0, FiniteMeasure.zero_prod]
    apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
    simpa only [FiniteMeasure.mass_prod, hμ0, FiniteMeasure.zero_mass, zero_mul] using hm
  by_cases hν0 : ν = 0
  · rw [hν0, FiniteMeasure.prod_zero]
    apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
    simpa only [FiniteMeasure.mass_prod, hν0, FiniteMeasure.zero_mass, mul_zero] using hm
  have hp := ProbabilityMeasure.continuous_prod.tendsto (μ.normalize, ν.normalize)
  have hn := hp.comp ((FiniteMeasure.tendsto_normalize_of_tendsto hμ hμ0).prodMk_nhds
    (FiniteMeasure.tendsto_normalize_of_tendsto hν hν0))
  have hf := ProbabilityMeasure.toFiniteMeasure_continuous.tendsto (μ.normalize.prod ν.normalize)
  have hs := hm.smul (hf.comp hn)
  simpa only [Function.comp_apply, ← prod_eq_mass_smul_normalized] using hs

theorem finiteMeasure_le_liminf_open
    [Nonempty X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {l : Filter I} {μn : I → FiniteMeasure X}
    {μ : FiniteMeasure X} (hμ : Tendsto μn l (𝓝 μ))
    {G : Set X} (hG : IsOpen G) :
    (μ : Measure X) G ≤ l.liminf (fun n => (μn n : Measure X) G) := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  by_cases hμ0 : μ = 0
  · simp [hμ0]
  have hn := FiniteMeasure.tendsto_normalize_of_tendsto hμ hμ0
  have ho := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hn hG
  have hm : Tendsto (fun n => ((μn n).mass : ℝ≥0∞)) l (𝓝 (μ.mass : ℝ≥0∞)) :=
    ENNReal.continuous_coe.continuousAt.tendsto.comp hμ.mass
  have heq (ρ : FiniteMeasure X) :
      (ρ : Measure X) G = (ρ.mass : ℝ≥0∞) * (ρ.normalize : Measure X) G := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ρ.self_eq_mass_mul_normalize, ENNReal.coe_mul,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  rw [heq μ]
  calc
    (μ.mass : ℝ≥0∞) * (μ.normalize : Measure X) G ≤
        (μ.mass : ℝ≥0∞) * l.liminf (fun n => ((μn n).normalize : Measure X) G) :=
      mul_le_mul_right ho _
    _ = (l.liminf (fun n => ((μn n).mass : ℝ≥0∞))) *
        l.liminf (fun n => ((μn n).normalize : Measure X) G) := by rw [hm.liminf_eq]
    _ ≤ l.liminf (fun n => ((μn n).mass : ℝ≥0∞) *
        ((μn n).normalize : Measure X) G) := ENNReal.le_liminf_mul
    _ = l.liminf (fun n => (μn n : Measure X) G) := by simp only [heq]

theorem finiteMeasureReal_le_liminf_open
    [Nonempty X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {l : Filter I} [l.NeBot]
    {μn : I → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μn l (𝓝 μ)) {G : Set X} (hG : IsOpen G) :
    (μ : Measure X).real G ≤ l.liminf (fun n => (μn n : Measure X).real G) := by
  have hm : Tendsto (fun n => ((μn n).mass : ℝ≥0∞)) l (𝓝 (μ.mass : ℝ≥0∞)) :=
    ENNReal.continuous_coe.continuousAt.tendsto.comp hμ.mass
  have hlim : l.liminf (fun n => (μn n : Measure X) G) ≤ (μ.mass : ℝ≥0∞) := by
    rw [← hm.liminf_eq]
    apply liminf_le_liminf _ ⟨0, Eventually.of_forall (fun _ => bot_le)⟩
      hm.isCoboundedUnder_ge
    exact Eventually.of_forall fun n => by
      rw [FiniteMeasure.ennreal_mass]
      exact measure_mono (subset_univ _)
  have hfinite : l.liminf (fun n => (μn n : Measure X) G) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hlim
  obtain ⟨B, hB⟩ := hμ.mass.isBoundedUnder_le
  have hbound : ∀ᶠ n in l, (μn n : Measure X) G ≤ (B : ℝ≥0∞) := by
    filter_upwards [hB] with n hn
    calc
      (μn n : Measure X) G ≤ (μn n : Measure X) univ := measure_mono (subset_univ _)
      _ = ((μn n).mass : ℝ≥0∞) := (FiniteMeasure.ennreal_mass (μ := μn n)).symm
      _ ≤ B := ENNReal.coe_le_coe.mpr hn
  have hreal := ENNReal.toReal_mono hfinite (finiteMeasure_le_liminf_open hμ hG)
  simpa only [Measure.real, ← ENNReal.liminf_toReal_eq ENNReal.coe_ne_top hbound] using hreal

def detectionSet (z h : X → ℝ) (η ε : ℝ) : Set X :=
  {x | η < z x ∧ z x < 1 ∧ ε < |h x|}

omit [MeasurableSpace X] in
theorem isOpen_detectionSet [TopologicalSpace X] {z h : X → ℝ}
    (hz : Continuous z) (hh : Continuous h) (η ε : ℝ) :
    IsOpen (detectionSet z h η ε) :=
  (isOpen_lt continuous_const hz).inter
    ((isOpen_lt hz continuous_const).inter (isOpen_lt continuous_const hh.abs))

theorem le_liminf_product_detection
    [Nonempty X] [Nonempty Y] [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {l : Filter I} [l.NeBot]
    {μn : I → FiniteMeasure X} {νn : I → FiniteMeasure Y}
    {μ : FiniteMeasure X} {ν : FiniteMeasure Y}
    (hμ : Tendsto μn l (𝓝 μ)) (hν : Tendsto νn l (𝓝 ν))
    {z h : X × Y → ℝ} (hz : Continuous z) (hh : Continuous h) (η ε : ℝ) :
    ((μ.prod ν : FiniteMeasure (X × Y)) : Measure (X × Y)).real
        (detectionSet z h η ε) ≤
      l.liminf (fun n => ((μn n).prod (νn n) : Measure (X × Y)).real
        (detectionSet z h η ε)) :=
  finiteMeasureReal_le_liminf_open (tendsto_finiteMeasure_prod hμ hν)
    (isOpen_detectionSet hz hh η ε)

omit [MeasurableSpace X] in

theorem detectionSet_subset_of_uniform_approximation
    {z h g : X → ℝ} {η ε δ : ℝ} (happrox : ∀ x, |g x - h x| ≤ δ) :
    detectionSet z h η (ε + δ) ⊆ detectionSet z g η ε := by
  intro x hx
  refine ⟨hx.1, hx.2.1, ?_⟩
  have ha := abs_sub_abs_le_abs_sub (h x) (g x)
  have hb := happrox x
  rw [abs_sub_comm] at hb
  have hc := hx.2.2
  linarith

theorem le_liminf_open_sections
    [Nonempty X] [Nonempty Y] [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {l : Filter I} [l.NeBot] {xn : I → X} {x : X}
    {μn : I → FiniteMeasure Y} {μ : FiniteMeasure Y}
    (hx : Tendsto xn l (𝓝 x)) (hμ : Tendsto μn l (𝓝 μ))
    {G : Set (X × Y)} (hG : IsOpen G) :
    (μ : Measure Y).real (Prod.mk x ⁻¹' G) ≤
      l.liminf (fun n => (μn n : Measure Y).real (Prod.mk (xn n) ⁻¹' G)) := by
  let δ : X → FiniteMeasure X := fun a => (diracProba a).toFiniteMeasure
  have hδ : Continuous δ :=
    ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_diracProba
  have ht := tendsto_finiteMeasure_prod ((hδ.tendsto x).comp hx) hμ
  have hl := finiteMeasureReal_le_liminf_open ht hG
  have he (a : X) (ρ : FiniteMeasure Y) :
      (δ a |>.prod ρ : Measure (X × Y)).real G =
        (ρ : Measure Y).real (Prod.mk a ⁻¹' G) := by
    change ((Measure.dirac a).prod (ρ : Measure Y) G).toReal = _
    rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hG.measurableSet]
    rfl
  simpa only [Function.comp_apply, he] using hl

theorem le_liminf_moving_product_detection
    {P : Type*} [MeasurableSpace P] [Nonempty P]
    [Nonempty X] [Nonempty Y]
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology P] [SecondCountableTopology X] [SecondCountableTopology Y]
    [PseudoMetrizableSpace P] [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y]
    [OpensMeasurableSpace P] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {l : Filter I} [l.NeBot] {pn : I → P} {p : P}
    {μn : I → FiniteMeasure X} {νn : I → FiniteMeasure Y}
    {μ : FiniteMeasure X} {ν : FiniteMeasure Y}
    (hp : Tendsto pn l (𝓝 p))
    (hμ : Tendsto μn l (𝓝 μ)) (hν : Tendsto νn l (𝓝 ν))
    {z : X × Y → ℝ} {h : P × (X × Y) → ℝ}
    (hz : Continuous z) (hh : Continuous h) (η ε : ℝ) :
    (μ.prod ν : Measure (X × Y)).real
        (detectionSet z (fun y => h (p, y)) η ε) ≤
      l.liminf (fun n => ((μn n).prod (νn n) : Measure (X × Y)).real
        (detectionSet z (fun y => h (pn n, y)) η ε)) := by
  have ho := isOpen_detectionSet (hz.comp continuous_snd) hh η ε
  exact le_liminf_open_sections hp (tendsto_finiteMeasure_prod hμ hν) ho

end Balanced.ProfileWeakDetection

end OAI
