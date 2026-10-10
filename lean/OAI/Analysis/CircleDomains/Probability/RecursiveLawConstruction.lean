import OAI.Analysis.CircleDomains.Probability.RecursiveCodeLaw
import OAI.Analysis.CircleDomains.Probability.PositiveBarrierLaw

namespace OAI

/-! Insert the actual prior-law presentation into the path-code data, and
retain all quantitative outputs of the positive-law theorem in a recursion stage. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

def endpointCodeData (base : PathCodeData Sphere Sphere) (p : Sphere)
    {flags : Set Sphere} {μ : ℕ → Measure C(PathTime, Sphere)}
    (R : PriorLawPresentation base.dust flags μ) (contours gates : ℕ → Set Sphere) :
    PathCodeData Sphere Sphere :=
  { base with
    target := p
    priorLaws := μ
    priorDeletions := R.priorDeletions
    flagDeletions := R.flagDeletions
    gateContours := contours
    gateSets := gates }

def RecursiveCodeGeometry.of_presentation
    (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (he : ∀ y : base.physicalDomain, (base.domainEquiv y).val = π y.val)
    (p : Sphere) (hp : p ∈ base.dust)
    {flags : Set Sphere} {μ : ℕ → Measure C(PathTime, Sphere)}
    (R : PriorLawPresentation base.dust flags μ) (contours gates : ℕ → Set Sphere) :
    RecursiveCodeGeometry base π flags where
  data := endpointCodeData base p R contours gates
  physical_eq := rfl
  quotient_eq := rfl
  dust_eq := rfl
  anchor_eq := rfl
  levels_eq := rfl
  weights_eq := rfl
  domain_agrees := he
  target_dust := hp
  presentation := R
  prior_deletions_eq := rfl
  flag_deletions_eq := rfl

def positiveRecursiveBudgets (ω : TupleType → ℝ≥0∞) (r : ℝ≥0) (hr : 0 < r) :
    RecursiveLawBudgets where
  occupationMass := densityMassBound sphericalArea (r : ℝ≥0∞)⁻¹
  tupleMass := densityMassBound (tupleReference ω) (r : ℝ≥0∞)⁻¹
  energy := (r : ℝ≥0∞)⁻¹
  visitConstant := (r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1
  occupationMass_finite := densityMassBound_lt_top sphericalArea
    (ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr hr))
  energy_finite := ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr hr)
  visitConstant_finite := ENNReal.add_lt_top.mpr ⟨ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hr.ne')), by simp⟩

def RecursiveCodeLaw.of_positive_candidate
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {flags : Set Sphere}
    (G : RecursiveCodeGeometry base π flags) (ω : TupleType → ℝ≥0∞)
    (r : ℝ≥0) (hr : 0 < r) (ε : ℝ)
    (P : ProbabilityMeasure (BasePathCode G.data))
    (hP : CodeLawCandidate G.data (fun x : G.presentation.marks => x.val)
      sphericalArea (tupleReference ω)
      (densityMassBound sphericalArea (r : ℝ≥0∞)⁻¹)
      (densityMassBound (tupleReference ω) (r : ℝ≥0∞)⁻¹)
      (r : ℝ≥0∞)⁻¹ (((r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1) ^ 2) P)
    (hfinite : ∀ F : Finset G.data.dust,
      ∑ x ∈ F, pathHitReal (codePathLaw G.data P) x.val ^ 2 ≤
        (((r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1).toReal + ε) ^ 2)
    (hcount : {x : Sphere | x ∈ G.data.dust ∧
      0 < pathHitProbability (codePathLaw G.data P) x}.Countable) :
    RecursiveCodeLaw base π flags ω :=
  ⟨G, ⟨positiveRecursiveBudgets ω r hr, P, hP,
    ((r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1).toReal + ε, hfinite,
    by simpa only [pathHitProbability_codePathLaw] using hcount⟩⟩

end CircleDomainRigidity

end

end OAI
