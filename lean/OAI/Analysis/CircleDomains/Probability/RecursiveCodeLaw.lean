import OAI.Analysis.CircleDomains.Modulus.DustPriorBudgets
import OAI.Analysis.CircleDomains.Selection.FullHitSupport
import OAI.Analysis.CircleDomains.Sobolev.FiniteSphericalArea

namespace OAI

/-! The proved outputs retained at one stage of the endpoint-law recursion.
The candidate includes actual densities and quantitative mark budgets. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

structure RecursiveCodeGeometry (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (flags : Set Sphere) where
  data : PathCodeData Sphere Sphere
  physical_eq : data.physicalDomain = base.physicalDomain
  quotient_eq : data.quotientDomain = base.quotientDomain
  dust_eq : data.dust = base.dust
  anchor_eq : data.anchor = base.anchor
  levels_eq : data.levels = base.levels
  weights_eq : data.levelWeights = base.levelWeights
  domain_agrees : ∀ y : data.physicalDomain, (data.domainEquiv y).val = π y.val
  target_dust : data.target ∈ base.dust
  presentation : PriorLawPresentation base.dust flags data.priorLaws
  prior_deletions_eq : data.priorDeletions = presentation.priorDeletions
  flag_deletions_eq : data.flagDeletions = presentation.flagDeletions

structure RecursiveLawBudgets where
  occupationMass : ℝ≥0∞
  tupleMass : ℝ≥0∞
  energy : ℝ≥0∞
  visitConstant : ℝ≥0∞
  occupationMass_finite : occupationMass < ∞
  energy_finite : energy < ∞
  visitConstant_finite : visitConstant < ∞

def RecursiveLawWitness (d : PathCodeData Sphere Sphere) (marks : Set Sphere)
    (ω : TupleType → ℝ≥0∞) :=
  Σ budgets : RecursiveLawBudgets, {law : ProbabilityMeasure (BasePathCode d) //
    CodeLawCandidate d (fun x : marks => x.val) sphericalArea (tupleReference ω)
      budgets.occupationMass budgets.tupleMass budgets.energy (budgets.visitConstant ^ 2) law ∧
    ∃ hitConstant : ℝ,
      (∀ F : Finset d.dust,
        ∑ x ∈ F, pathHitReal (codePathLaw d law) x.val ^ 2 ≤ hitConstant ^ 2) ∧
      {x | x ∈ d.dust ∧ 0 < codeHitProbability d law x}.Countable}

namespace RecursiveLawWitness
variable {d : PathCodeData Sphere Sphere} {marks : Set Sphere}
  {ω : TupleType → ℝ≥0∞} (W : RecursiveLawWitness d marks ω)
abbrev budgets := W.1
abbrev law := W.2.val
abbrev candidate := W.2.property.1
def hitConstant : ℝ := Classical.choose W.2.property.2
theorem finite_hit_tests : ∀ F : Finset d.dust,
    ∑ x ∈ F, pathHitReal (codePathLaw d W.law) x.val ^ 2 ≤ W.hitConstant ^ 2 :=
  (Classical.choose_spec W.2.property.2).1
theorem countable_dust_hits : {x | x ∈ d.dust ∧ 0 < codeHitProbability d W.law x}.Countable :=
  (Classical.choose_spec W.2.property.2).2
end RecursiveLawWitness

def RecursiveCodeLaw (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (flags : Set Sphere) (ω : TupleType → ℝ≥0∞) :=
  Σ geometry : RecursiveCodeGeometry base π flags,
    RecursiveLawWitness geometry.data geometry.presentation.marks ω

namespace RecursiveCodeLaw

variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
  (L : RecursiveCodeLaw base π flags ω)

abbrev geometry := L.1
abbrev witness := L.2
abbrev data := L.geometry.data
abbrev physical_eq := L.geometry.physical_eq
abbrev quotient_eq := L.geometry.quotient_eq
abbrev dust_eq := L.geometry.dust_eq
abbrev anchor_eq := L.geometry.anchor_eq
abbrev levels_eq := L.geometry.levels_eq
abbrev weights_eq := L.geometry.weights_eq
abbrev domain_agrees := L.geometry.domain_agrees
abbrev target_dust := L.geometry.target_dust
abbrev presentation := L.geometry.presentation
abbrev prior_deletions_eq := L.geometry.prior_deletions_eq
abbrev flag_deletions_eq := L.geometry.flag_deletions_eq
abbrev law := L.witness.law
abbrev candidate := L.witness.candidate
abbrev hitConstant := L.witness.hitConstant
abbrev finite_hit_tests := L.witness.finite_hit_tests
abbrev countable_dust_hits := L.witness.countable_dust_hits
abbrev occupationMass := L.witness.budgets.occupationMass
abbrev tupleMass := L.witness.budgets.tupleMass
abbrev energy := L.witness.budgets.energy
abbrev visitConstant := L.witness.budgets.visitConstant
abbrev occupationMass_finite := L.witness.budgets.occupationMass_finite
abbrev energy_finite := L.witness.budgets.energy_finite
abbrev visitConstant_finite := L.witness.budgets.visitConstant_finite

def density : Sphere → ℝ≥0∞ := Classical.choose L.candidate.1.2

theorem density_measurable : Measurable L.density := (Classical.choose_spec L.candidate.1.2).1

theorem occupation_eq : meanCodeOccupation L.data L.law = sphericalArea.withDensity L.density :=
  (Classical.choose_spec L.candidate.1.2).2.1

theorem density_energy_finite : (∫⁻ x, L.density x ^ 2 ∂sphericalArea) < ∞ :=
  (Classical.choose_spec L.candidate.1.2).2.2.trans_lt L.energy_finite

theorem finite_occupation : IsFiniteMeasure (meanCodeOccupation L.data L.law) :=
  ⟨L.candidate.1.1.trans_lt L.occupationMass_finite⟩

variable [BorelSpace C(PathTime, Sphere)]

theorem hit_square_finite : (∑' x : base.dust, codeHitProbability L.data L.law x.val ^ 2) < ∞ := by
  have h := (codeHit_square_tsum_le L.data L.law L.hitConstant L.finite_hit_tests).trans_lt
    ENNReal.ofReal_lt_top
  change (∑' x : L.data.dust, codeHitProbability L.data L.law x.val ^ 2) < ∞ at h
  rw [L.dust_eq] at h
  exact h

omit [BorelSpace C(PathTime, Sphere)] in
theorem tuple_absolutelyContinuous : meanCodeTuple L.data L.law ≪ tupleReference ω := by
  obtain ⟨q, _, hq, _⟩ := L.candidate.2.2.2
  rw [hq]
  exact withDensity_absolutelyContinuous _ _

theorem prior_visit_norm_finite (i : ℕ) :
    countingSquareNorm (fun x : support (dustPriorHitMass base.dust (L.data.priorLaws i)) =>
      meanVisitCount (codePathLaw L.data L.law) x.val) < ∞ :=
  L.presentation.prior_visit_norm_finite L.data L.law sphericalArea (tupleReference ω)
    L.occupationMass L.tupleMass L.energy L.visitConstant L.visitConstant_finite L.candidate i

theorem flag_visit_norm_finite (i : ℕ) (hflags : support (base.levelWeights i) ⊆ flags) :
    countingSquareNorm (fun x : support (base.levelWeights i) =>
      meanVisitCount (codePathLaw L.data L.law) x.val) < ∞ :=
  (candidate_visit_norm_on_marks L.data L.law L.presentation.marks _
    (hflags.trans L.presentation.extra_marks) L.candidate.2.1).trans_lt L.visitConstant_finite

theorem full_hit_support_countable
    (hU : IsOpen base.quotientDomain) (hG : IsOpen base.physicalDomain)
    (hBU : base.dustᶜ ⊆ base.quotientDomain)
    (hdisj : Disjoint base.quotientDomain base.dust)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x)) :
    (support (priorHitMass (codePathLaw L.data L.law : Measure C(PathTime, Sphere)))).Countable := by
  have hz (x : Sphere) (hx : x ∉ L.data.dust) (hi : x ≠ π OnePoint.infty) :
      codeHitProbability L.data L.law x = 0 := by
    apply codeHitProbability_zero_off_dust L.data (by simpa only [L.quotient_eq] using hU)
      (by simpa only [L.physical_eq] using hG)
      (by simpa only [L.dust_eq, L.quotient_eq] using hBU)
      π hπ hclosed hsurj (by simpa only [L.physical_eq] using hr) L.domain_agrees
      (fun ht => disjoint_left.mp hdisj (L.quotient_eq ▸ ht) L.target_dust)
      L.law L.density L.density_measurable L.occupation_eq L.density_energy_finite x hx hi
  have hc := countable_full_hit_support (codeHitProbability L.data L.law) L.data.dust
    (π OnePoint.infty) L.countable_dust_hits hz
  apply hc.mono
  intro x hx
  change priorHitMass (codePathLaw L.data L.law : Measure _) x ≠ 0 at hx
  change codeHitProbability L.data L.law x ≠ 0
  rwa [priorHitMass_codePathLaw] at hx

end RecursiveCodeLaw
end CircleDomainRigidity

end

end OAI
