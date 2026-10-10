import Mathlib
import OAI.Analysis.HardSphere.Geometry.SharedIdentities

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups CellOrbital
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma route_acceptance_pos (σ : Equiv.Perm I) (s : Finset I)
    (hσ : ∀i,i∉s→σ i=i) (r : ℝ) (anchor : J→Torus L)
    (allowed : J→Set C(Time,Point)) (label : J→I)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (ν : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (ν i)]
    (a : ℝ≥0∞) (ha : 0<a)
    (hi : UniformInsertionOn (routeChecks σ s hσ r anchor allowed label get hg) ν a s)
    (x : ∀i,X i) (z : ∀i,X (σ.symm i))
    (hx : x∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ) :
    0<(Measure.pi fun i:s ↦ ν i)
      {p | ambientFirst s σ (x,p)∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ ∧
        ambientSecond s σ hσ (x,p)∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ} := by
  let C := routeChecks σ s hσ r anchor allowed label get hg
  have hso : Disjoint s (Finset.univ\s) := Finset.disjoint_left.mpr (fun _ hi hj ↦ (Finset.mem_sdiff.mp hj).2 hi)
  have ho : (fun i ↦ (x i,z i))∈retainedEvent C (Finset.univ\s) :=
    routeChecks_outside σ s hσ r anchor allowed label get hg _ hso _
      (fun e he ↦ hx e (Finset.subset_univ _))
  have hp := partialNormalizer_pos C ha hi hso (fun i ↦ (x i,z i)) ho
  have he := congrArg (fun A ↦ Prod.mk x ⁻¹' A)
    (ambient_proposalEvent σ s hσ r anchor allowed label get hg z)
  change 0<(Measure.pi fun i:s ↦ ν i) (Prod.mk x ⁻¹'
    {p | ambientFirst s σ p∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ ∧
      ambientSecond s σ hσ p∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ})
  rw [he]
  have hm := (measurable_proposalEvent C s (Finset.univ\s) z).preimage (measurable_prodMk_left (x:=x))
  change 0 < ∫⁻ proposal, (Prod.mk x ⁻¹' proposalEvent C s (Finset.univ\s) z).indicator
    (fun _ ↦ (1 : ℝ≥0∞)) proposal ∂(Measure.pi fun i:s ↦ ν i) at hp
  simpa only [lintegral_indicator_fun_one hm] using hp

theorem route_shared_mass (σ : Equiv.Perm I) (s : Finset I)
    (hσ : ∀i,i∉s→σ i=i) (r : ℝ) (anchor : J→Torus L)
    (allowed : J→Set C(Time,Point)) (label : J→I)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (ν : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (ν i)]
    (a : ℝ≥0∞) (ha : 0<a)
    (hi : UniformInsertionOn (routeChecks σ s hσ r anchor allowed label get hg) ν a s)
    (z : ∀i,X (σ.symm i)) :
    let A := retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ
    let P := conditionedMeasure (Measure.pi μ) A
    ambientSharedKernel s σ hσ (Kernel.const Unit P)
      (fun i ↦ Kernel.const Unit (ν i)) (Prod.snd ⁻¹' A) () univ = P univ := by
  dsimp only
  apply ambientSharedKernel_mass
  · exact (measurableSet_retainedEvent _ _).preimage measurable_snd
  · have hm := ae_restrict_mem (μ:=Measure.pi μ) (measurableSet_retainedEvent
      (primaryChecks r anchor allowed label get hg) Finset.univ)
    have hx := Measure.ae_smul_measure hm
      ((Measure.pi μ) (retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ))⁻¹
    filter_upwards [hx] with x hx
    exact route_acceptance_pos σ s hσ r anchor allowed label get hg ν a ha hi x z hx

end HardSphere.Bridge
end
end

end OAI
