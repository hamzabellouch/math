import Mathlib
import OAI.Analysis.HardSphere.Conditioning.PairedChecks
import OAI.Analysis.HardSphere.Allocation.Allocation

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I P : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace P]
  (avoid : P→P→Prop) (hm : MeasurableSet {p : P×P | avoid p.1 p.2}) (real : I→Prop)
  (edge : I→I→Prop)
attribute [local instance] Classical.propDecidable

abbrev Edge := {p : I×I // edge p.1 p.2}

def sparseReference (e : Edge edge) : LocalCheck (fun _ : I ↦ P) :=
  primaryPairCheck avoid hm real e.val.1 e.val.2

def sparseProposal (S : Finset I) (σ : Equiv.Perm I) (e : Bool×Edge edge) : LocalCheck (fun _ : I ↦ P×P) :=
  pairedRouteChecks avoid hm real S σ (e.1,e.2.val.1,e.2.val.2)

omit [Fintype I] in
lemma sparse_primary (S : Finset I) (σ : Equiv.Perm I) (U : Finset I) (x z : I→P) :
    checkWeight (sparseProposal avoid hm real edge S σ) U (fun i ↦ (x i,z i))≤
      checkWeight (sparseReference avoid hm real edge) U x := by
  by_cases h : x∈retainedEvent (sparseReference avoid hm real edge) U
  · have he : checkWeight (sparseReference avoid hm real edge) U x=1 := by simp [checkWeight,h]
    rw [he]
    exact checkWeight_le_one _ _ _
  · have hn : (fun i ↦ (x i,z i))∉retainedEvent (sparseProposal avoid hm real edge S σ) U := by
      intro hp
      exact h (fun e he ↦ hp (false,e) he)
    simp only [checkWeight,Set.indicator_of_notMem h,Set.indicator_of_notMem hn,le_refl]

omit [Fintype I] in
lemma sparse_outside (S o : Finset I) (hso : Disjoint S o) (σ : Equiv.Perm I)
    (hσ : ∀i,i∉S→σ i=i) (x z : I→P)
    (hx : x∈retainedEvent (sparseReference avoid hm real edge) o) :
    (fun i ↦ (x i,z i))∈retainedEvent (sparseProposal avoid hm real edge S σ) o := by
  rintro ⟨b,e⟩ hc
  cases b
  · exact hx e hc
  · have hi : σ e.val.1∈o := hc (by simp [sparseProposal,pairedRouteChecks,ownedPairCheck])
    have hj : σ e.val.2∈o := hc (by simp [sparseProposal,pairedRouteChecks,ownedPairCheck])
    have hin : e.val.1∉S := fun hs ↦ Finset.disjoint_left.mp hso ((perm_mem_of_fix_outside S σ hσ _).mpr hs) hi
    have hjn : e.val.2∉S := fun hs ↦ Finset.disjoint_left.mp hso ((perm_mem_of_fix_outside S σ hσ _).mpr hs) hj
    have hio : e.val.1∈o := by simpa only [hσ _ hin] using hi
    have hjo : e.val.2∈o := by simpa only [hσ _ hjn] using hj
    have hre := hx e (by simpa only [sparseReference,primaryPairCheck,Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hio hjo)
    simpa only [sparseReference,sparseProposal,pairedRouteChecks,ownedPairCheck,primaryPairCheck,
      hin,hjn,ite_false,hσ _ hin,hσ _ hjn] using hre

omit [Fintype I] in
lemma pair_subset_one {s t : Finset I} (i j : I) (hi : i∈s∪t) (hj : j∈s∪t)
    (hij : ¬(i∈s ∧ j∈t)) (hji : ¬(j∈s ∧ i∈t)) :
    ({i,j} : Finset I)⊆s ∨ ({i,j} : Finset I)⊆t := by
  rcases Finset.mem_union.mp hi with hi|hi
  · left
    have hj' : j∈s := (Finset.mem_union.mp hj).resolve_right (fun h ↦ hij ⟨hi,h⟩)
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl
    · exact hi
    · exact hj'
  · right
    have hj' : j∈t := (Finset.mem_union.mp hj).resolve_left (fun h ↦ hji ⟨h,hi⟩)
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl
    · exact hi
    · exact hj'

omit [Fintype I] in
lemma sparse_reference_separated (s t : Finset I)
    (hsep : ∀i j,edge i j→¬(i∈s ∧ j∈t) ∧ ¬(j∈s ∧ i∈t)) :
    SeparatedChecks (sparseReference avoid hm real edge) s t := by
  intro e he
  exact pair_subset_one e.val.1 e.val.2 (he (by simp [sparseReference,primaryPairCheck]))
    (he (by simp [sparseReference,primaryPairCheck])) (hsep _ _ e.property).1 (hsep _ _ e.property).2

omit [Fintype I] in
lemma sparse_proposal_separated (S s t : Finset I) (σ : Equiv.Perm I)
    (hsep : ∀i j,edge i j→¬(i∈s ∧ j∈t) ∧ ¬(j∈s ∧ i∈t))
    (hsep' : ∀i j,edge i j→¬(σ i∈s ∧ σ j∈t) ∧ ¬(σ j∈s ∧ σ i∈t)) :
    SeparatedChecks (sparseProposal avoid hm real edge S σ) s t := by
  rintro ⟨b,e⟩ he
  cases b
  · exact pair_subset_one e.val.1 e.val.2 (he (by simp [sparseProposal,pairedRouteChecks,ownedPairCheck]))
      (he (by simp [sparseProposal,pairedRouteChecks,ownedPairCheck])) (hsep _ _ e.property).1 (hsep _ _ e.property).2
  · exact pair_subset_one (σ e.val.1) (σ e.val.2) (he (by simp [sparseProposal,pairedRouteChecks,ownedPairCheck]))
      (he (by simp [sparseProposal,pairedRouteChecks,ownedPairCheck])) (hsep' _ _ e.property).1 (hsep' _ _ e.property).2

end HardSphere.Comparison
namespace HardSphere.Groups
open Wiener
attribute [local irreducible] torusDistance

lemma confined_far_avoid {L : Length} (v w : Torus L) (f g : ConfigurationPath 1 L)
    (hf : Confined v f) (hg : Confined w g) (hfar : 21<torusDistance L v w)
    {r : ℝ} (hr : r≤1) : ∀s : Time,r<torusDistance L (f s 0) (g s 0) := by
  intro s
  have h₁ := torusDistance_triangle' L v (f s 0) w
  have h₂ := torusDistance_triangle' L (f s 0) (g s 0) w
  rw [torusDistance_comm L v (f s 0)] at h₁
  have hh := hf s
  have hh' := hg s
  linarith

lemma incident_centers_close {I : Type*} {L : Length} (anchor center : I→Torus L)
    (owner : I→I) (hcenter : ∀i,torusDistance L (anchor i) (center (owner i))≤1)
    (i j : I) (hij : torusDistance L (anchor i) (anchor j)≤21) :
    torusDistance L (center (owner i)) (center (owner j))≤23 := by
  have h₁ := torusDistance_triangle' L (center (owner i)) (anchor i) (center (owner j))
  have h₂ := torusDistance_triangle' L (anchor i) (anchor j) (center (owner j))
  rw [torusDistance_comm L (center (owner i)) (anchor i)] at h₁
  linarith [hcenter i,hcenter j]

end HardSphere.Groups

end
end

end

end OAI
