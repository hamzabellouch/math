import OAI.MeasureTheory.Falconer.Recursion.BranchValidity
import OAI.MeasureTheory.Falconer.Angular.SourceAngularReduction
import OAI.MeasureTheory.Falconer.Recursion.SourcePrefixReduction
import OAI.MeasureTheory.Falconer.Recursion.SourceSuffixReduction

namespace OAI

namespace PlanarFalconer
open MeasureTheory

namespace AngularStateData

def branchState (d : AngularStateData) : BranchState := .H d.a₀ d.t₀ d.a d.v d.i

theorem branchState_descriptors (d : AngularStateData) :
    d.branchState.descriptors d.profile d.N d.q = d.retainedList d.a := rfl

theorem successor_branchState (d : AngularStateData) (p : ℕ) (row : CellPath × CellPath) :
    (d.successor p row).branchState = .H d.a₀ d.t₀ p d.v d.i := rfl

theorem near_branch_transition (d : AngularStateData) (hw : d.a+100*d.q < d.v)
    (hn : d.a < d.v-2*sourceFarBuffer d.N ((d.retainedList d.a).sup descriptorLength) d.sig)
    (row : CellPath × CellPath) :
    BranchStep d.profile d.N d.q d.sig d.branchState .near
      ((d.successor (d.v-2*sourceFarBuffer d.N ((d.retainedList d.a).sup descriptorLength) d.sig) row).branchState) :=
  BranchStep.near hw hn

theorem direct_branch_transition (d : AngularStateData) (hw : d.a+100*d.q < d.v)
    {e : PolicyDescriptor} (he : DirectPolicyWitness d.profile d.N d.q d.a₀ d.t₀ d.a d.v d.sig e)
    (row : CellPath × CellPath) :
    BranchStep d.profile d.N d.q d.sig d.branchState .direct
      ((d.successor (descriptorAnchor e) row).branchState) := BranchStep.direct hw he

end AngularStateData

namespace PositiveDistanceData

def branchState (d : PositiveDistanceData) : BranchState := .D d.a d.t d.i
noncomputable def branchProfile (d : PositiveDistanceData) (n : ℕ) : ℝ := d.mass n-(n:ℝ)/d.N

def angularSuccessor (d : PositiveDistanceData) (p v : ℕ) (row : CellPath × CellPath) : AngularStateData :=
  ⟨d.Q,d.ρ,d.mass,d.N,d.q,d.a,d.t,p,v,d.J,d.i,d.lam,d.sig,row.1,row.2⟩

theorem angularSuccessor_energy (d : PositiveDistanceData) (p v : ℕ) (row : CellPath × CellPath)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (Ψ : ℝ → ℝ) :
    (d.angularSuccessor p v row).energy k h Ψ =
      d.policyCellEnergy (d.prefixRemainingList p) k h p v Ψ row := rfl

theorem angularSuccessor_list_index (d : PositiveDistanceData) (p v : ℕ) (row : CellPath × CellPath) :
    (d.angularSuccessor p v row).retainedList p = d.prefixRemainingList p ∧
    (d.angularSuccessor p v row).i = d.i ∧
    (d.angularSuccessor p v row).profile = d.branchProfile := ⟨rfl,rfl,rfl⟩

theorem suffix_branch_transition (d : PositiveDistanceData) (hw : d.a+100*d.q < d.t)
    (hs : d.a+d.t < 2*policyDepth d.branchProfile d.N d.q d.a d.t) :
    BranchStep d.branchProfile d.N d.q d.sig d.branchState .suffix
      (({d with t := policyDepth d.branchProfile d.N d.q d.a d.t,i := d.i+1} : PositiveDistanceData).branchState) :=
  BranchStep.suffix hw hs

theorem low_branch_transition (d : PositiveDistanceData) (hw : d.a+100*d.q < d.t)
    {v : ℕ} (hv : v ∈ d.prefixLowDepths) :
    BranchStep d.branchProfile d.N d.q d.sig d.branchState .low
      (({d with t := v,i := d.i+1} : PositiveDistanceData).branchState) := by
  obtain ⟨hm,hg⟩ := Finset.mem_filter.mp hv
  exact BranchStep.low hw hm (by linarith)

theorem high_branch_transition (d : PositiveDistanceData) (hw : d.a+100*d.q < d.t)
    (hs : 2*policyDepth d.branchProfile d.N d.q d.a d.t ≤ d.a+d.t)
    {v : ℕ} (hv : v ∈ Finset.Ioc d.a d.t) (hg : (d.t:ℝ)-d.sig*d.N < (v:ℝ))
    (row : CellPath × CellPath) :
    BranchStep d.branchProfile d.N d.q d.sig d.branchState .high
      ((d.angularSuccessor (policyDepth d.branchProfile d.N d.q d.a d.t) v row).branchState) :=
  BranchStep.high hw hs hv (by change (d.t:ℝ)-v < d.sig*d.N; linarith)

theorem high_energy_member_transition (d : PositiveDistanceData) (K : ℕ) (Ψ : ℝ → ℝ)
    (hw : d.a+100*d.q < d.t)
    (hs : 2*policyDepth d.branchProfile d.N d.q d.a d.t ≤ d.a+d.t)
    {E : ℝ} (hE : E ∈ d.prefixSuccessorEnergies K (policyDepth d.branchProfile d.N d.q d.a d.t) Ψ) :
    E = 0 ∨ ∃ v ∈ Finset.Ioc d.a d.t, ∃ row ∈ sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y
      (policyDepth d.branchProfile d.N d.q d.a d.t-d.a),
      ∃ k : Fin 2 → PolicyDescriptor → ℕ, ∃ h : Fin 2 → Plane → ℂ,
      (∀ l, ∑ e ∈ d.prefixRemainingList (policyDepth d.branchProfile d.N d.q d.a d.t), k l e ≤ K) ∧
      (∀ l, Measurable (h l)) ∧ (∀ l x, ‖h l x‖ ≤ 1) ∧
      BranchStep d.branchProfile d.N d.q d.sig d.branchState .high
        ((d.angularSuccessor (policyDepth d.branchProfile d.N d.q d.a d.t) v row).branchState) ∧
      E = ((d.angularSuccessor (policyDepth d.branchProfile d.N d.q d.a d.t) v row).energy k h Ψ).toReal := by
  rcases hE with rfl | ⟨v,hv,hg,row,hr,k,hk,h,hh,hhb,hE⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨v,hv,row,hr,k,h,hk,hh,hhb,d.high_branch_transition hw hs hv hg row,hE⟩

end PositiveDistanceData

namespace AngularStateData

theorem far_branch_transition (d : AngularStateData) (hw : d.a+100*d.q < d.v)
    (hn : d.a < d.v-2*sourceFarBuffer d.N ((d.retainedList d.a).sup descriptorLength) d.sig)
    {b : ℕ} (hb : b ∈ Finset.Icc (d.a+9)
      (d.v-2*sourceFarBuffer d.N ((d.retainedList d.a).sup descriptorLength) d.sig+5)) :
    BranchStep d.profile d.N d.q d.sig d.branchState .far (d.distanceSuccessor b).branchState :=
  BranchStep.far hw hn (by
    change b ∈ Finset.Icc (d.a+9)
      (d.v-2*sourceFarBuffer d.N ((d.retainedList d.a).sup descriptorLength) d.sig+6)
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hb).1, by have := (Finset.mem_Icc.mp hb).2; omega⟩)

theorem far_successor_list_index (d : AngularStateData) (b : ℕ) :
    (d.distanceSuccessor b).branchState.descriptors d.profile d.N d.q =
      policyDescriptorList d.profile d.N d.q b d.v ∧
    (d.distanceSuccessor b).i = d.i+1 ∧
    (d.distanceSuccessor b).branchProfile = d.profile := ⟨rfl,rfl,rfl⟩

end AngularStateData

end PlanarFalconer

end OAI
