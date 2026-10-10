import OAI.Analysis.IrrationalRotation.Analysis.CrossingAvoidance
import OAI.Analysis.IrrationalRotation.Couplings.ConditionalKernelSupport
import Mathlib.Probability.Independence.Conditional

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Invariant233.CrossingAvoidance

section KernelBounds

variable {ι Ω Y : Type*} [Countable ι] [MeasurableSpace Ω] [MeasurableSpace Y]

theorem kernel_iIndepSet_ae (κ : Kernel Y Ω) (ν : Measure Y)
    (events : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (events i))
    (hind : Kernel.iIndepSet events κ ν) :
    ∀ᵐ y ∂ν, iIndepSet events (κ y) := by
  have hall : ∀ᵐ y ∂ν, ∀ s : Finset ι,
      κ y (⋂ i ∈ s, events i) = ∏ i ∈ s, κ y (events i) :=
    ae_all_iff.mpr (fun s => hind.meas_biInter s)
  filter_upwards [hall] with y hy
  exact (iIndepSet_iff_meas_biInter hmeas).mpr hy

theorem kernel_avoid_le_exp (κ : Kernel Y Ω) (ν : Measure Y)
    (events : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (events i))
    (hind : Kernel.iIndepSet events κ ν) (selected : Y → Finset ι) (p : Y → ℝ)
    (hp : ∀ᵐ y ∂ν, ∀ i ∈ selected y, p y ≤ (κ y).real (events i)) :
    ∀ᵐ y ∂ν, (κ y).real (⋂ i ∈ selected y, (events i)ᶜ) ≤
      Real.exp (-((selected y).card : ℝ) * p y) := by
  filter_upwards [kernel_iIndepSet_ae κ ν events hmeas hind, hp] with y hy hp
  let : IsProbabilityMeasure (κ y) := hy.isProbabilityMeasure
  exact measureReal_avoid_le_exp (κ y) events hy hmeas (selected y) (p y) hp

theorem kernel_bad_le_exp_intensity (κ : Kernel Y Ω) (ν : Measure Y)
    (events : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (events i))
    (hind : Kernel.iIndepSet events κ ν) (selected : Y → Finset ι)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ)
    (hcard : ∀ᵐ y ∂ν, m / 40 ≤ ((selected y).card : ℝ))
    (hp : ∀ᵐ y ∂ν, ∀ i ∈ selected y, ρ / 10 ≤ (κ y).real (events i))
    (bad : Y → Set Ω)
    (hbad : ∀ᵐ y ∂ν, ∀ᵐ ω ∂κ y,
      ω ∈ bad y → ∀ i ∈ selected y, ω ∉ events i) :
    ∀ᵐ y ∂ν, (κ y).real (bad y) ≤ Real.exp (-L / 400) := by
  filter_upwards [kernel_iIndepSet_ae κ ν events hmeas hind, hcard, hp, hbad]
    with y hy hcard hp hbad
  let : IsProbabilityMeasure (κ y) := hy.isProbabilityMeasure
  have hsubset : bad y ≤ᵐ[κ y] ⋂ i ∈ selected y, (events i)ᶜ := by
    filter_upwards [hbad] with ω hω
    intro hb
    exact Set.mem_iInter.mpr (fun i => Set.mem_iInter.mpr (fun hi => hω hb i hi))
  have hmono : (κ y).real (bad y) ≤ (κ y).real (⋂ i ∈ selected y, (events i)ᶜ) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)
  refine hmono.trans ?_
  exact measureReal_le_exp_intensity (κ y) events hy hmeas (selected y) m ρ L
    hρ hcard hL hp _ (Set.Subset.refl _)

theorem kernel_bad_le_exp_intensity_on (κ : Kernel Y Ω) (ν : Measure Y)
    (events : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (events i))
    (hind : Kernel.iIndepSet events κ ν) (selected : Y → Finset ι)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ) (active : Y → Prop)
    (hcard : ∀ᵐ y ∂ν, active y → m / 40 ≤ ((selected y).card : ℝ))
    (hp : ∀ᵐ y ∂ν, active y → ∀ i ∈ selected y, ρ / 10 ≤ (κ y).real (events i))
    (bad : Y → Set Ω)
    (hzero : ∀ᵐ y ∂ν, ¬ active y → κ y (bad y) = 0)
    (hbad : ∀ᵐ y ∂ν, ∀ᵐ ω ∂κ y,
      ω ∈ bad y → ∀ i ∈ selected y, ω ∉ events i) :
    ∀ᵐ y ∂ν, (κ y).real (bad y) ≤ Real.exp (-L / 400) := by
  filter_upwards [kernel_iIndepSet_ae κ ν events hmeas hind, hcard, hp, hzero, hbad]
    with y hy hcard hp hzero hbad
  let : IsProbabilityMeasure (κ y) := hy.isProbabilityMeasure
  by_cases ha : active y
  · have hsubset : bad y ≤ᵐ[κ y] ⋂ i ∈ selected y, (events i)ᶜ := by
      filter_upwards [hbad] with ω hω
      intro hb
      exact Set.mem_iInter.mpr (fun i => Set.mem_iInter.mpr (fun hi => hω hb i hi))
    have hmono : (κ y).real (bad y) ≤ (κ y).real (⋂ i ∈ selected y, (events i)ᶜ) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)
    exact hmono.trans (measureReal_le_exp_intensity (κ y) events hy hmeas (selected y) m ρ L
      hρ (hcard ha) hL (hp ha) _ (Set.Subset.refl _))
  · change (κ y (bad y)).toReal ≤ _
    rw [hzero ha, ENNReal.toReal_zero]
    exact (Real.exp_pos _).le

end KernelBounds

section ConditionalExpectation

variable {ι Ω : Type*} [Countable ι]

theorem iCondIndepSet_ae_condExpKernel (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (events : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (events i))
    (hind : iCondIndepSet m' hm' events μ) :
    ∀ᵐ x ∂μ, iIndepSet events (condExpKernel μ m' x) := by
  exact ae_of_ae_trim hm'
    (@kernel_iIndepSet_ae ι Ω Ω ‹Countable ι› mΩ m'
      (condExpKernel μ m') (μ.trim hm') events hmeas hind)

theorem conditional_bad_le_exp_intensity (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (events : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (events i))
    (hind : iCondIndepSet m' hm' events μ) (selected : Ω → Finset ι)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ) (active : Ω → Prop)
    (hcard : ∀ᵐ x ∂μ, active x → m / 40 ≤ ((selected x).card : ℝ))
    (hp : ∀ᵐ x ∂μ, active x → ∀ i ∈ selected x,
      ρ / 10 ≤ (condExpKernel μ m' x).real (events i))
    (bad : Set Ω) (hbadmeas : MeasurableSet bad)
    (hzero : ∀ᵐ x ∂μ, ¬ active x → condExpKernel μ m' x bad = 0)
    (hbad : ∀ᵐ x ∂μ, ∀ᵐ ω ∂condExpKernel μ m' x,
      ω ∈ bad → ∀ i ∈ selected x, ω ∉ events i) :
    ∀ᵐ x ∂μ, (μ[bad.indicator (fun _ => (1 : ℝ)) | m']) x ≤
      Real.exp (-L / 400) := by
  filter_upwards [iCondIndepSet_ae_condExpKernel m' hm' μ events hmeas hind,
    hcard, hp, hzero, hbad, condExpKernel_ae_eq_condExp hm' hbadmeas]
    with x hx hcard hp hzero hbad heq
  rw [← heq]
  let : IsProbabilityMeasure (condExpKernel μ m' x) := hx.isProbabilityMeasure
  by_cases ha : active x
  · have hsubset : bad ≤ᵐ[condExpKernel μ m' x] ⋂ i ∈ selected x, (events i)ᶜ := by
      filter_upwards [hbad] with ω hω
      intro hb
      exact Set.mem_iInter.mpr (fun i => Set.mem_iInter.mpr (fun hi => hω hb i hi))
    have hmono : (condExpKernel μ m' x).real bad ≤
        (condExpKernel μ m' x).real (⋂ i ∈ selected x, (events i)ᶜ) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)
    exact hmono.trans (measureReal_le_exp_intensity (condExpKernel μ m' x) events hx hmeas
      (selected x) m ρ L hρ (hcard ha) hL (hp ha) _ (Set.Subset.refl _))
  · change (condExpKernel μ m' x bad).toReal ≤ _
    rw [hzero ha, ENNReal.toReal_zero]
    exact (Real.exp_pos _).le

theorem conditional_bad_le_exp_of_endpoint {Y : Type*}
    (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    [MeasurableSpace Y] [MeasurableEq Y]
    (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (events : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (events i))
    (hind : iCondIndepSet m' hm' events μ)
    (endpoint : Ω → Y) (hendpoint : Measurable[m'] endpoint)
    (selected : Y → Finset ι) (active : Y → Prop)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ)
    (hcard : ∀ y, active y → m / 40 ≤ ((selected y).card : ℝ))
    (hp : ∀ᵐ x ∂μ, active (endpoint x) → ∀ i ∈ selected (endpoint x),
      ρ / 10 ≤ (μ[(events i).indicator (fun _ => (1 : ℝ)) | m']) x)
    (bad : Set Ω) (hbadmeas : MeasurableSet bad)
    (hbad : ∀ᵐ ω ∂μ, ω ∈ bad → active (endpoint ω) ∧
      ∀ i ∈ selected (endpoint ω), ω ∉ events i) :
    ∀ᵐ x ∂μ, (μ[bad.indicator (fun _ => (1 : ℝ)) | m']) x ≤
      Real.exp (-L / 400) := by
  have heq : ∀ᵐ x ∂μ, ∀ i, (condExpKernel μ m' x).real (events i) =
      (μ[(events i).indicator (fun _ => (1 : ℝ)) | m']) x :=
    ae_all_iff.mpr (fun i => condExpKernel_ae_eq_condExp hm' (hmeas i))
  have hpKernel : ∀ᵐ x ∂μ, active (endpoint x) → ∀ i ∈ selected (endpoint x),
      ρ / 10 ≤ (condExpKernel μ m' x).real (events i) := by
    filter_upwards [hp, heq] with x hx heq
    intro ha i hi
    rw [heq i]
    exact hx ha i hi
  have hfixed := condExpKernel_ae_eq_of_measurable m' hm' μ endpoint hendpoint
  have hlift := ae_ae_condExpKernel_of_ae m' hm' μ hbad
  have hsupport : ∀ᵐ x ∂μ, ∀ᵐ ω ∂condExpKernel μ m' x,
      ω ∈ bad → active (endpoint x) ∧ ∀ i ∈ selected (endpoint x), ω ∉ events i := by
    filter_upwards [hfixed, hlift] with x hfixed hlift
    filter_upwards [hfixed, hlift] with ω hfixed hlift
    intro hb
    simpa only [hfixed] using hlift hb
  have hzero : ∀ᵐ x ∂μ, ¬ active (endpoint x) → condExpKernel μ m' x bad = 0 := by
    filter_upwards [hsupport] with x hx
    intro ha
    have hn : ∀ᵐ ω ∂condExpKernel μ m' x, ω ∉ bad := by
      filter_upwards [hx] with ω hω
      exact fun hb => ha (hω hb).1
    simpa only [not_not, Set.ofPred_mem_eq] using (ae_iff.mp hn)
  have havoid : ∀ᵐ x ∂μ, ∀ᵐ ω ∂condExpKernel μ m' x,
      ω ∈ bad → ∀ i ∈ selected (endpoint x), ω ∉ events i := by
    filter_upwards [hsupport] with x hx
    filter_upwards [hx] with ω hω
    exact fun hb => (hω hb).2
  exact conditional_bad_le_exp_intensity m' hm' μ events hmeas hind
    (fun x => selected (endpoint x)) m ρ L hρ hL (fun x => active (endpoint x))
    (Filter.Eventually.of_forall (fun x => hcard (endpoint x))) hpKernel
    bad hbadmeas hzero havoid

end ConditionalExpectation

end Invariant233.CrossingAvoidance

end OAI
