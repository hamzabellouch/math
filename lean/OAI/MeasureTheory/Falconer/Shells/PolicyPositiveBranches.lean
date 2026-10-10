import OAI.MeasureTheory.Falconer.Shells.PolicyPositiveRecurrence
import OAI.MeasureTheory.Falconer.Estimates.PolicySuffixRecurrence
import OAI.MeasureTheory.Falconer.Angular.PolicyAngularBranches

namespace OAI

/-! # Concrete positive successors in the weighted branch tree -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (BranchState BranchStep BranchLabel branchExponent branchCost policyDepth)

namespace PolicyJetData
variable {m : ℕ}

def positiveBranchState (P : PolicyJetData m) : BranchState := .D P.a P.t P.i

theorem positiveBranchState_valid (P : PolicyJetData m) (hat : P.a ≤ P.t) :
    P.positiveBranchState.Valid P.N P.σ := ⟨hat,P.base_right.trans P.base_N⟩

theorem positiveSuccessor_state (P : PolicyJetData m) (v : ℕ) (hv : v ≤ P.t₀) (i : ℕ) :
    (P.positiveSuccessor v hv i).positiveBranchState = .D P.a v i := rfl

theorem positive_low_branch (P : PolicyJetData m) (hwide : P.a+100*P.q < P.t)
    {v : ℕ} (hv : v ∈ Finset.Ioc P.a P.t) (hgap : P.σ*P.N ≤ (P.t:ℝ)-v) :
    BranchStep P.policy P.N P.q P.σ P.positiveBranchState .low
      (P.positiveSuccessor v ((Finset.mem_Ioc.mp hv).2.trans P.base_right) (P.i+1)).positiveBranchState :=
  BranchStep.low hwide hv hgap

theorem positive_suffix_branch (P : PolicyJetData m) (hwide : P.a+100*P.q < P.t)
    (hside : P.a+P.t < 2*policyDepth P.policy P.N P.q P.a P.t) :
    BranchStep P.policy P.N P.q P.σ P.positiveBranchState .suffix
      (.D P.a (policyDepth P.policy P.N P.q P.a P.t) (P.i+1)) :=
  BranchStep.suffix hwide hside

theorem positive_high_branch (P : PolicyJetData m) (hwide : P.a+100*P.q < P.t)
    (hside : 2*policyDepth P.policy P.N P.q P.a P.t ≤ P.a+P.t)
    (hleft : P.a₀ = P.a) (hright : P.t₀ = P.t)
    {v : ℕ} (hv : v ∈ Finset.Ioc P.a P.t) (hgap : (P.t:ℝ)-v < P.σ*P.N)
    (hap : P.a ≤ policyDepth P.policy P.N P.q P.a P.t)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hrow : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ
      (policyDepth P.policy P.N P.q P.a P.t-P.a) ×ˢ
        (P.Q.descendant P.Y).occupiedPaths P.ρ (policyDepth P.policy P.N P.q P.a P.t-P.a)) :
    BranchStep P.policy P.N P.q P.σ P.positiveBranchState .high
      (((P.atFrequency v ((Finset.mem_Ioc.mp hv).2.trans P.base_right)).child
        (policyDepth P.policy P.N P.q P.a P.t) hap row hrow).branchState) := by
  change BranchStep P.policy P.N P.q P.σ (.D P.a P.t P.i) .high
    (.H P.a₀ P.t₀ (policyDepth P.policy P.N P.q P.a P.t) v P.i)
  rw [hleft,hright]
  exact BranchStep.high hwide hside hv hgap

theorem directWeight_eq_high_branchExponent (P : PolicyJetData m) (p v : ℕ) (lam σ ε : ℝ)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N) :
    P.directWeight p lam σ ε = ((2:ℝ)^P.N)^(branchExponent P.policy
      (dimensionalBranchReserve (m+3) lam σ) σ ε P.positiveBranchState .high
        (.H P.a P.t p v P.i)) := by
  simp only [directWeight,branchExponent,branchCost,positiveBranchState,BranchState.start,
    reduceCtorEq,ite_false,hprofile]

theorem low_branchExponent (P : PolicyJetData m) (v : ℕ) (lam σ ε : ℝ) :
    branchExponent P.policy lam σ ε P.positiveBranchState .low (.D P.a v (P.i+1)) = ε := by
  simp only [branchExponent,branchCost,positiveBranchState,BranchState.start,sub_self,
    mul_zero,zero_add,ite_true]

/-- Change only the current pair of cells; the retained descriptor set shrinks. -/
def onCells (P : PolicyJetData m) (a : ℕ) (ha : P.a ≤ a)
    (X Y : List (Fin (m+3) → Bool)) (hX : X.length = a) (hY : Y.length = a) : PolicyJetData m :=
  { P with
    a := a, X := X, Y := Y, X_length := hX, Y_length := hY,
    base_left := P.base_left.trans ha,
    separated := fun b hb => P.separated b
      (PlanarFalconer.remainingPolicyDescriptors_mono P.policy P.N P.q P.a₀ P.t₀ ha hb) }

end PolicyJetData
end Falconer

end OAI
