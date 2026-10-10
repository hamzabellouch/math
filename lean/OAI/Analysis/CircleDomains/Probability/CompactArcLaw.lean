import OAI.Analysis.CircleDomains.Topology.TerminalArcSet
import Mathlib.Probability.ConditionalProbability

namespace OAI

/-! Conditioning the terminal-arc law on a compact family of mass greater
than one half loses at most a factor two in every measure bound. -/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

section Restriction
variable {Ω : Type*} [MeasurableSpace Ω]

def restrictProbability (μ : ProbabilityMeasure Ω) (K : Set Ω)
    (hK : (μ : Measure Ω) K ≠ 0) : ProbabilityMeasure Ω :=
  ⟨cond (μ : Measure Ω) K, cond_isProbabilityMeasure hK⟩

theorem restrictProbability_le_two (μ : ProbabilityMeasure Ω) (K : Set Ω)
    (hK : (1 / 2 : ℝ≥0∞) ≤ (μ : Measure Ω) K) :
    (restrictProbability μ K (ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1/2).trans_le hK)) : Measure Ω) ≤
      (2 : ℝ≥0∞) • (μ : Measure Ω) := by
  apply Measure.le_iff.mpr
  intro S hS
  change cond (μ : Measure Ω) K S ≤ _
  rw [cond_apply' hS, Measure.smul_apply, smul_eq_mul]
  apply mul_le_mul' ?_ (measure_mono inter_subset_right)
  have hi := ENNReal.inv_le_inv.mpr hK
  norm_num at hi ⊢
  exact hi

theorem restrictProbability_ae_mem (μ : ProbabilityMeasure Ω) (K : Set Ω)
    (hK : (μ : Measure Ω) K ≠ 0) (hm : MeasurableSet K) :
    ∀ᵐ x ∂(restrictProbability μ K hK : Measure Ω), x ∈ K := ae_cond_mem hm

end Restriction

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem exists_compact_terminal_arc_law
    (μ : ProbabilityMeasure C(PathTime, Sphere)) (V : Set Sphere) (hV : IsOpen V)
    (b : Sphere) (hμ : ∀ᵐ α : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
      α ∈ terminalArcSet V b) :
    ∃ (K : Set C(PathTime, Sphere)) (η : ProbabilityMeasure C(PathTime, Sphere)),
      IsCompact K ∧ K ⊆ terminalArcSet V b ∧
      (∀ᵐ α ∂(η : Measure C(PathTime, Sphere)), α ∈ K) ∧
      (η : Measure C(PathTime, Sphere)) ≤ (2 : ℝ≥0∞) • (μ : Measure C(PathTime, Sphere)) := by
  obtain ⟨K, hKS, hK, hmass⟩ := exists_compact_terminal_arc_core μ V hV b hμ
  have hpos : (μ : Measure C(PathTime, Sphere)) K ≠ 0 :=
    ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1/2).trans hmass)
  exact ⟨K, restrictProbability μ K hpos, hK, hKS,
    restrictProbability_ae_mem μ K hpos hK.measurableSet,
    restrictProbability_le_two μ K hmass.le⟩

theorem exists_compact_selected_arc_law
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (μ : ProbabilityMeasure C(PathTime, Sphere)) (V : Set Sphere) (hV : IsOpen V)
    (b : Sphere) (hμ : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
      γ ⊥ ∉ V ∧ γ ⊤ ∈ V ∧ γ ⊤ = b) :
    ∃ (K : Set C(PathTime, Sphere)) (η : ProbabilityMeasure C(PathTime, Sphere)),
      IsCompact K ∧ K ⊆ terminalArcSet V b ∧
      (∀ᵐ α ∂(η : Measure C(PathTime, Sphere)), α ∈ K) ∧
      (∀ x, pathHitProbability η x ≤ 2 * pathHitProbability μ x) ∧
      (∀ x ∉ closure V, pathHitProbability η x = 0) := by
  obtain ⟨f, hfm, hf⟩ := exists_measurable_terminal_arc_selector hselect harcs μ V hV
  obtain ⟨K, η, hK, hKS, hη, hbound⟩ := exists_compact_terminal_arc_law (μ.map f) V hV b
    (terminalArcLaw_mem μ V hV b f hfm hf hμ)
  have hends : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
      γ ⊥ ∉ V ∧ γ ⊤ ∈ V := hμ.mono fun _ h => ⟨h.1, h.2.1⟩
  refine ⟨K, η, hK, hKS, hη, ?_, ?_⟩
  · intro x
    exact (hbound _).trans (mul_le_mul' le_rfl
      (terminalArcLaw_hit_le μ V hV f hfm hf hends x))
  · intro x hx
    apply le_antisymm ?_ bot_le
    have h := hbound {α | ∃ t : PathTime, α t = x}
    change pathHitProbability η x ≤ 2 * pathHitProbability (μ.map f) x at h
    rw [terminalArcLaw_hit_eq_zero μ V hV f hfm hf hends hx, mul_zero] at h
    exact h

end CircleDomainRigidity

end

end OAI
