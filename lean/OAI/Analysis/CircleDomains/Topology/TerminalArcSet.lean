import OAI.Analysis.CircleDomains.Probability.TerminalArcLaw
import OAI.Analysis.CircleDomains.Topology.DyadicOpenCover
import OAI.Analysis.CircleDomains.Selection.PhysicalSubpaths
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! The endpoint and interior conditions of the compact arc reduction form
a Borel set. Consequently a full law of these arcs has a compact core. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

lemma measurableSet_pathsInsideOpenTime (V : Set Sphere) (hV : IsOpen V)
    (T : Set PathTime) (hT : IsOpen T) :
    MeasurableSet {α : C(PathTime, Sphere) | MapsTo α T V} := by
  have he : {α : C(PathTime, Sphere) | MapsTo α T V} =
      ⋂ p : DyadicInside T, pathsInsideOn V
        (dyadicLeft p.val.1 p.val.2) (dyadicRight p.val.1 p.val.2) := by
    ext α
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h p
      exact h.mono_left p.property
    · intro h t ht
      obtain ⟨p, hp⟩ := mem_iUnion.mp ((iUnion_insideDyadicCell hT).symm ▸ ht)
      exact h p hp
  rw [he]
  exact MeasurableSet.iInter fun p => (isOpen_pathsInsideOn hV _ _).measurableSet

def terminalArcSet (V : Set Sphere) (b : Sphere) : Set C(PathTime, Sphere) :=
  {α | Injective α ∧ α ⊥ ∈ frontier V ∧ α ⊤ = b ∧
    MapsTo α (Ioo ⊥ ⊤) V}

lemma measurableSet_terminalArcSet (V : Set Sphere) (hV : IsOpen V) (b : Sphere) :
    MeasurableSet (terminalArcSet V b) := by
  exact measurableSet_injective_paths.inter
    (((continuous_eval_const ⊥).measurable isClosed_frontier.measurableSet).inter
      ((measurableSet_eq_fun (continuous_eval_const ⊤).measurable measurable_const).inter
        (measurableSet_pathsInsideOpenTime V hV (Ioo ⊥ ⊤) isOpen_Ioo)))

theorem terminalArcLaw_mem (μ : ProbabilityMeasure C(PathTime, Sphere))
    (V : Set Sphere) (hV : IsOpen V) (b : Sphere)
    (f : C(PathTime, Sphere) → C(PathTime, Sphere))
    (hfm : AEMeasurable f (μ : Measure C(PathTime, Sphere)))
    (hf : ∀ γ, γ ⊥ ∉ V → γ ⊤ ∈ V →
      (terminalPath γ (lastEntryTime γ V), f γ) ∈ simpleSubarcRelation)
    (hends : ∀ᵐ γ ∂(μ : Measure C(PathTime, Sphere)),
      γ ⊥ ∉ V ∧ γ ⊤ ∈ V ∧ γ ⊤ = b) :
    ∀ᵐ α : C(PathTime, Sphere) ∂(μ.map f : Measure C(PathTime, Sphere)),
      α ∈ terminalArcSet V b := by
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff hfm (measurableSet_terminalArcSet V hV b)).mpr
  filter_upwards [hends] with γ hγ
  obtain ⟨hi, h0, h1, hs, hfront, hinterior⟩ :=
    terminal_arc_selector_properties hV hf γ hγ.1 hγ.2.1
  exact ⟨hi, hfront, h1.trans hγ.2.2, fun t ht => (hinterior t ht).1⟩

theorem exists_compact_terminal_arc_core
    (η : ProbabilityMeasure C(PathTime, Sphere)) (V : Set Sphere)
    (hV : IsOpen V) (b : Sphere)
    (hη : ∀ᵐ α : C(PathTime, Sphere) ∂(η : Measure C(PathTime, Sphere)),
      α ∈ terminalArcSet V b) :
    ∃ K : Set C(PathTime, Sphere), K ⊆ terminalArcSet V b ∧ IsCompact K ∧
      (1 / 2 : ℝ≥0∞) < (η : Measure C(PathTime, Sphere)) K := by
  have hm : (η : Measure C(PathTime, Sphere)) (terminalArcSet V b) = 1 := by
    rw [← measure_univ (μ := (η : Measure C(PathTime, Sphere)))]
    exact measure_congr (Filter.eventuallyEqSet_univ.mpr hη)
  exact (measurableSet_terminalArcSet V hV b).exists_lt_isCompact
    (by rw [hm]; norm_num)

end CircleDomainRigidity

end

end OAI
