import OAI.NumberTheory.DukePrimeDegree.Dynamics.ExactInvariantSets
import OAI.NumberTheory.PrimePackets.KernelEntropy
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-!
# Pointwise invariant versions under a Haar measure class

The version is formed by averaging only on orbits where the observable
is almost everywhere constant. Those orbits form an exactly invariant
measurable set. This avoids an intersection of uncountably many conull
sets and does not assume amenability of the acting group.
-/

noncomputable section
open MeasureTheory Set Filter
open MeasureTheory.Measure
open scoped ENNReal

namespace DukePrimeDegree

variable {H Y : Type*} [Group H] [MeasurableSpace H]
  [MeasurableSpace Y] [MulAction H Y]

def orbitConstantMean (ρ : Measure H) (f : Y → ℝ) (x : Y) : ℝ :=
  ∫ h, f (h • x) ∂ρ

def orbitConstantSet (ρ : Measure H) (f : Y → ℝ) : Set Y :=
  {x | ∀ᵐ h ∂ρ, f (h • x) = orbitConstantMean ρ f x}

lemma measurable_orbitConstantMean
    (ρ : Measure H) [SFinite ρ]
    (hsmul : Measurable (fun p : Y × H => p.2 • p.1))
    (f : Y → ℝ) (hf : Measurable f) :
    Measurable (orbitConstantMean ρ f) :=
  ((hf.comp hsmul).stronglyMeasurable.integral_prod_right').measurable

lemma measurableSet_orbitConstantSet
    (ρ : Measure H) [SFinite ρ]
    (hsmul : Measurable (fun p : Y × H => p.2 • p.1))
    (f : Y → ℝ) (hf : Measurable f) :
    MeasurableSet (orbitConstantSet ρ f) := by
  have hm := measurable_orbitConstantMean ρ hsmul f hf
  have hbad : MeasurableSet {p : Y × H |
      f (p.2 • p.1) ≠ orbitConstantMean ρ f p.1} :=
    (measurableSet_eq_fun (hf.comp hsmul) (hm.comp measurable_fst)).compl
  have hmass := measurable_measure_prodMk_left (ν := ρ) hbad
  have heq : orbitConstantSet ρ f =
      {x : Y | ρ {h : H | f (h • x) ≠ orbitConstantMean ρ f x} = 0} := by
    ext x
    exact ae_iff
  rw [heq]
  exact measurableSet_eq_fun hmass measurable_const

omit [MeasurableSpace Y] in
lemma orbitConstantMean_smul_of_mem
    (ρ : Measure H) [IsProbabilityMeasure ρ]
    (hρ : ∀ g : H, QuasiMeasurePreserving (fun h : H => h * g) ρ ρ)
    (f : Y → ℝ) {x : Y} (hx : x ∈ orbitConstantSet ρ f) (g : H) :
    orbitConstantMean ρ f (g • x) = orbitConstantMean ρ f x := by
  apply integral_eq_const
  simpa only [mul_smul] using (hρ g).ae hx

omit [MeasurableSpace Y] in
lemma smul_mem_orbitConstantSet
    (ρ : Measure H) [IsProbabilityMeasure ρ]
    (hρ : ∀ g : H, QuasiMeasurePreserving (fun h : H => h * g) ρ ρ)
    (f : Y → ℝ) (x : Y) (g : H) :
    g • x ∈ orbitConstantSet ρ f ↔ x ∈ orbitConstantSet ρ f := by
  have himp (y : Y) (a : H) (hy : y ∈ orbitConstantSet ρ f) :
      a • y ∈ orbitConstantSet ρ f := by
    have hmean := orbitConstantMean_smul_of_mem ρ hρ f hy a
    change ∀ᵐ h ∂ρ, f (h • (a • y)) = orbitConstantMean ρ f (a • y)
    rw [hmean]
    simpa only [mul_smul] using (hρ a).ae hy
  exact ⟨fun hx => by simpa only [inv_smul_smul] using himp (g • x) g⁻¹ hx,
    himp x g⟩

/-- A probability in a right-translation invariant measure class gives
an exactly invariant measurable version of an almost invariant real
observable. The observable need not be globally bounded. -/
theorem exists_pointwise_invariant_version_of_probability_class
    (ρ : Measure H) [IsProbabilityMeasure ρ]
    (hρ : ∀ g : H, QuasiMeasurePreserving (fun h : H => h * g) ρ ρ)
    (μ : Measure Y) [SFinite μ]
    (hsmul : Measurable (fun p : H × Y => p.1 • p.2))
    (f : Y → ℝ) (hf : Measurable f)
    (hfix : ∀ h : H, (fun x : Y => f (h • x)) =ᵐ[μ] f) :
    ∃ f₀ : Y → ℝ, Measurable[PrimeDegreePackets.actionInvariantSigma H Y] f₀ ∧
      f₀ =ᵐ[μ] f ∧ ∀ (h : H) (x : Y), f₀ (h • x) = f₀ x := by
  let E := orbitConstantSet ρ f
  let c := orbitConstantMean ρ f
  let f₀ := E.indicator c
  have hc : Measurable c := measurable_orbitConstantMean ρ
    (hsmul.comp measurable_swap) f hf
  have hE : MeasurableSet E := measurableSet_orbitConstantSet ρ
    (hsmul.comp measurable_swap) f hf
  have hfixed (h : H) (x : Y) : f₀ (h • x) = f₀ x := by
    by_cases hx : x ∈ E
    · have hhx : h • x ∈ E := (smul_mem_orbitConstantSet ρ hρ f x h).mpr hx
      simpa only [f₀, Set.indicator_of_mem hx, Set.indicator_of_mem hhx] using
        orbitConstantMean_smul_of_mem ρ hρ f hx h
    · have hhx : h • x ∉ E := fun hh => hx ((smul_mem_orbitConstantSet ρ hρ f x h).mp hh)
      simp only [f₀, Set.indicator_of_notMem hx, Set.indicator_of_notMem hhx]
  refine ⟨f₀, PrimeDegreePackets.measurable_actionInvariantSigma
    (hc.indicator hE) hfixed, ?_, hfixed⟩
  have hmeas : MeasurableSet {p : H × Y | f (p.1 • p.2) = f p.2} :=
    measurableSet_eq_fun (hf.comp hsmul) (hf.comp measurable_snd)
  have hboth : ∀ᵐ x ∂μ, ∀ᵐ h ∂ρ, f (h • x) = f x :=
    (Measure.ae_ae_comm hmeas).mp (Eventually.of_forall hfix)
  filter_upwards [hboth] with x hx
  have hcx : c x = f x := integral_eq_const hx
  have hxE : x ∈ E := by
    change ∀ᵐ h ∂ρ, f (h • x) = c x
    rwa [hcx]
  simpa only [f₀, Set.indicator_of_mem hxE] using hcx

/-- Normalize the finite measure previously constructed from Haar.
This is an actual probability measure, not a probability input. -/
theorem exists_probability_right_quasiInvariant_measure
    [MeasurableMul₂ H] [MeasurableInv H] (haar : Measure H) [SFinite haar]
    [haar.IsMulLeftInvariant] (hhaar : haar ≠ 0) :
    ∃ ρ : Measure H, IsProbabilityMeasure ρ ∧
      ∀ g : H, QuasiMeasurePreserving (fun h : H => h * g) ρ ρ := by
  obtain ⟨ν, hfin, hν, hright⟩ := exists_finite_right_quasiInvariant_measure haar hhaar
  let : IsFiniteMeasure ν := hfin
  let c : ℝ≥0∞ := (ν Set.univ)⁻¹
  refine ⟨c • ν, ⟨?_⟩, fun g => (hright g).smul_measure c⟩
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Measure.measure_univ_ne_zero.mpr hν) (measure_ne_top _ _)

theorem exists_pointwise_invariant_version_of_haar
    [MeasurableMul₂ H] [MeasurableInv H] (haar : Measure H) [SFinite haar]
    [haar.IsMulLeftInvariant] (hhaar : haar ≠ 0)
    (μ : Measure Y) [SFinite μ]
    (hsmul : Measurable (fun p : H × Y => p.1 • p.2))
    (f : Y → ℝ) (hf : Measurable f)
    (hfix : ∀ h : H, (fun x : Y => f (h • x)) =ᵐ[μ] f) :
    ∃ f₀ : Y → ℝ, Measurable[PrimeDegreePackets.actionInvariantSigma H Y] f₀ ∧
      f₀ =ᵐ[μ] f ∧ ∀ (h : H) (x : Y), f₀ (h • x) = f₀ x := by
  obtain ⟨ρ, hprob, hright⟩ := exists_probability_right_quasiInvariant_measure haar hhaar
  let : IsProbabilityMeasure ρ := hprob
  exact exists_pointwise_invariant_version_of_probability_class ρ hright μ hsmul f hf hfix

end DukePrimeDegree

end

end OAI
