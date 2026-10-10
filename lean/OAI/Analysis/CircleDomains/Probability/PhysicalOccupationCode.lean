import OAI.Analysis.CircleDomains.Probability.PhysicalImageOccupation
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.GiryMonad

namespace OAI

/-! Borel physical occupation on ordinary path space, with zero extension
off the finite-length paths. This lets measurable arc selection act directly
on path laws without introducing a new code law. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

def physicalOccupationCode (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) : Measure Y :=
  if h : physicalDomainLength e y₀ γ < ∞ then dyadicPhysicalOccupation e y₀ ⟨γ, h⟩ else 0

lemma physicalOccupationCode_eq (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    physicalOccupationCode e y₀ γ.val = dyadicPhysicalOccupation e y₀ γ := by
  simp only [physicalOccupationCode, dite_eq_left γ.property]

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

lemma measurable_physicalOccupationCode (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    Measurable (physicalOccupationCode e y₀) := by
  have hm := (measurable_dyadicPhysicalOccupation e hU y₀).dite
    (show Measurable (fun _ => (0 : Measure Y)) from measurable_const)
    (measurableSet_finitePhysicalDomainLength e hU y₀)
  convert hm using 1
  funext γ
  unfold physicalOccupationCode
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact (h₂ h₁).elim
  · exact (h₁ h₂).elim
  · rfl

def meanPhysicalOccupation (e : G ≃ₜ U) (y₀ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) : Measure Y :=
  (μ : Measure C(PathTime, X)).bind (physicalOccupationCode e y₀)

lemma meanPhysicalOccupation_apply (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) {S : Set Y} (hS : MeasurableSet S) :
    meanPhysicalOccupation e y₀ μ S =
      ∫⁻ γ, physicalOccupationCode e y₀ γ S ∂(μ : Measure C(PathTime, X)) :=
  Measure.bind_apply hS (measurable_physicalOccupationCode e hU y₀).aemeasurable

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
lemma physicalOccupationCode_simple_subarc_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ α : C(PathTime, X)) (hγ : physicalDomainLength e y₀ γ < ∞)
    (hi : Injective α) (hs : range α ⊆ range γ) :
    physicalOccupationCode e y₀ α ≤ physicalOccupationCode e y₀ γ := by
  have hα : physicalDomainLength e y₀ α < ∞ :=
    (simple_subarc_physical_length_le e hU y₀ ⟨γ, hγ⟩ α hi hs).trans_lt hγ
  rw [physicalOccupationCode_eq e y₀ ⟨α, hα⟩, physicalOccupationCode_eq e y₀ ⟨γ, hγ⟩]
  exact simple_subarc_physical_occupation_le e hU y₀ ⟨γ, hγ⟩ ⟨α, hα⟩ hi hs

lemma meanPhysicalOccupation_map_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) (f : C(PathTime, X) → C(PathTime, X))
    (hfm : AEMeasurable f (μ : Measure C(PathTime, X)))
    (hγ : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), physicalDomainLength e y₀ γ < ∞)
    (hi : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), Injective (f γ))
    (hs : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), range (f γ) ⊆ range γ) :
    meanPhysicalOccupation e y₀ (μ.map f) ≤ meanPhysicalOccupation e y₀ μ := by
  apply Measure.le_iff.mpr
  intro S hS
  have hm : Measurable (fun γ => physicalOccupationCode e y₀ γ S) :=
    (Measure.measurable_coe hS).comp (measurable_physicalOccupationCode e hU y₀)
  rw [meanPhysicalOccupation_apply e hU y₀ _ hS, meanPhysicalOccupation_apply e hU y₀ _ hS,
    ProbabilityMeasure.toMeasure_map, lintegral_map' hm.aemeasurable hfm]
  apply lintegral_mono_ae
  filter_upwards [hγ, hi, hs] with γ hγ hi hs
  exact physicalOccupationCode_simple_subarc_le e hU y₀ γ (f γ) hγ hi hs S

lemma meanPhysicalOccupation_mono (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (μ ν : ProbabilityMeasure C(PathTime, X)) (c : ℝ≥0∞)
    (h : (μ : Measure C(PathTime, X)) ≤ c • (ν : Measure C(PathTime, X))) :
    meanPhysicalOccupation e y₀ μ ≤ c • meanPhysicalOccupation e y₀ ν := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [meanPhysicalOccupation_apply e hU y₀ μ hS, Measure.smul_apply,
    meanPhysicalOccupation_apply e hU y₀ ν hS, smul_eq_mul]
  simpa only [lintegral_smul_measure, smul_eq_mul] using
    (lintegral_mono' h (le_refl (fun γ => physicalOccupationCode e y₀ γ S)))

end CircleDomainRigidity

end

end OAI
