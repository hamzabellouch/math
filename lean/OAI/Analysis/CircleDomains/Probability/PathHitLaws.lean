import OAI.Analysis.CircleDomains.Topology.SphereLevels
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace OAI

/-! Closed path-hit relations and the joint upper semicontinuity of their probabilities.
The time interval is compact, so projection of the closed incidence relation is closed.
Weak convergence and the existing Portmanteau theorem then apply to the product with
the moving point mass. This supplies the actual hit function used in law fusion. -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

abbrev PathTime := Icc (0 : ℝ) 1

section ClosedRelation

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [TopologicalSpace Ω] [TopologicalSpace X]
  [BorelSpace Ω] [BorelSpace X]
  [SecondCountableTopology Ω] [SecondCountableTopology X]
  [PseudoMetrizableSpace Ω] [PseudoMetrizableSpace X]

omit [PseudoMetrizableSpace Ω] [PseudoMetrizableSpace X] in
theorem product_dirac_closed_section {H : Set (Ω × X)} (hH : IsClosed H)
    (μ : ProbabilityMeasure Ω) (x : X) :
    ((μ.prod (diracProba x) : ProbabilityMeasure (Ω × X)) : Measure (Ω × X)) H =
      (μ : Measure Ω) {ω | (ω, x) ∈ H} := by
  rw [ProbabilityMeasure.toMeasure_prod, Measure.prod_apply_symm hH.measurableSet]
  change (∫⁻ y, (μ : Measure Ω) ((fun ω => (ω, y)) ⁻¹' H) ∂Measure.dirac x) = _
  rw [lintegral_dirac' _ (measurable_measure_prodMk_right hH.measurableSet)]
  rfl

/-- Closed incidence has jointly upper semicontinuous hit probability in the weak law
and the tested point. No regularity of individual path lengths is involved. -/
theorem closed_section_probability_upperSemicontinuous {H : Set (Ω × X)}
    (hH : IsClosed H) :
    UpperSemicontinuous (fun p : ProbabilityMeasure Ω × X =>
      (p.1 : Measure Ω) {ω | (ω, p.2) ∈ H}) := by
  have hc : Continuous (fun p : ProbabilityMeasure Ω × X => p.1.prod (diracProba p.2)) :=
    ProbabilityMeasure.continuous_prod.comp
      (continuous_fst.prodMk (continuous_diracProba.comp continuous_snd))
  apply upperSemicontinuous_iff_limsup_le.mpr
  intro p
  simpa only [product_dirac_closed_section hH] using
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hc.continuousAt hH

end ClosedRelation

section Paths

variable {X : Type*} [MetricSpace X]

def pathHitSet : Set (C(PathTime, X) × X) :=
  {p | ∃ t : PathTime, p.1 t = p.2}

theorem isClosed_pathHitSet : IsClosed (pathHitSet (X := X)) := by
  let K : Set ((C(PathTime, X) × X) × PathTime) :=
    {p | p.1.1 p.2 = p.1.2}
  have hK : IsClosed K := isClosed_eq
    (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
    (continuous_snd.comp continuous_fst)
  have he : Prod.fst '' K = pathHitSet (X := X) := by
    ext p
    constructor
    · rintro ⟨⟨q, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(p, t), ht, rfl⟩
  rw [← he]
  exact isClosedMap_fst_of_compactSpace K hK

theorem isClosed_paths_hitting (x : X) :
    IsClosed {γ : C(PathTime, X) | ∃ t : PathTime, γ t = x} :=
  isClosed_pathHitSet.preimage (continuous_id.prodMk continuous_const)

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def pathHitProbability (μ : ProbabilityMeasure C(PathTime, X)) (x : X) : ℝ≥0∞ :=
  (μ : Measure C(PathTime, X)) {γ | ∃ t : PathTime, γ t = x}

theorem pathHitProbability_upperSemicontinuous :
    UpperSemicontinuous (fun p : ProbabilityMeasure C(PathTime, X) × X =>
      pathHitProbability p.1 p.2) :=
  closed_section_probability_upperSemicontinuous isClosed_pathHitSet

theorem measurable_pathHitProbability_point (μ : ProbabilityMeasure C(PathTime, X)) :
    Measurable (pathHitProbability μ) :=
  (pathHitProbability_upperSemicontinuous.comp
    (continuous_const.prodMk continuous_id)).measurable

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [BorelSpace C(PathTime, X)] in
theorem pathHitProbability_le_one (μ : ProbabilityMeasure C(PathTime, X)) (x : X) :
    pathHitProbability μ x ≤ 1 := prob_le_one

/-- A continuously varying untagged path law retains joint upper semicontinuity.
This also applies after a Borel-preserving Polish refinement of the code-law space. -/
theorem pathHitProbability_comp_upperSemicontinuous
    {Z : Type*} [TopologicalSpace Z] {law : Z → ProbabilityMeasure C(PathTime, X)}
    (hlaw : Continuous law) :
    UpperSemicontinuous (fun p : Z × X => pathHitProbability (law p.1) p.2) :=
  pathHitProbability_upperSemicontinuous.comp
    ((hlaw.comp continuous_fst).prodMk continuous_snd)

end Paths

end CircleDomainRigidity

end

end OAI
