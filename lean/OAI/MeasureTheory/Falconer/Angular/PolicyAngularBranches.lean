import OAI.MeasureTheory.Falconer.Graphs.PolicyGraphRecurrence
import OAI.MeasureTheory.Falconer.Estimates.PolicyFarCoefficients

namespace OAI

/-! # The proved angular steps use the scheduled scalar branches -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (BranchState BranchStep BranchLabel branchExponent branchCost descriptorAnchor)

namespace PolicyJetData
variable {m : ℕ}

def branchState (P : PolicyJetData m) : BranchState := .H P.a₀ P.t₀ P.a P.t P.i

theorem branchState_valid (P : PolicyJetData m) (hat : P.a ≤ P.t)
    (hbase : (P.t₀:ℝ) ≤ P.t+P.σ*P.N) : P.branchState.Valid P.N P.σ :=
  ⟨P.base_left,hat,P.base_right,P.base_N,hbase⟩

theorem branchState_nearDepth (P : PolicyJetData m) :
    P.branchState.nearDepth P.policy P.N P.q P.σ = P.splitDepth := rfl

theorem child_branchState (P : PolicyJetData m) (p : ℕ) (hap : P.a ≤ p)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hrow : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
      (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a)) :
    (P.child p hap row hrow).branchState = .H P.a₀ P.t₀ p P.t P.i := rfl

theorem direct_branch (P : PolicyJetData m) (hwide : P.a+100*P.q < P.t)
    {d : PlanarFalconer.PolicyDescriptor}
    (hd : PlanarFalconer.DirectPolicyWitness P.policy P.N P.q P.a₀ P.t₀ P.a P.t P.σ d) :
    BranchStep P.policy P.N P.q P.σ P.branchState .direct
      (.H P.a₀ P.t₀ (descriptorAnchor d) P.t P.i) := BranchStep.direct hwide hd

theorem near_branch (P : PolicyJetData m) (hwide : P.a+100*P.q < P.t)
    (hnear : P.a < P.splitDepth) :
    BranchStep P.policy P.N P.q P.σ P.branchState .near
      (.H P.a₀ P.t₀ P.splitDepth P.t P.i) := BranchStep.near hwide hnear

theorem far_branch (P : PolicyJetData m) (hwide : P.a+100*P.q < P.t)
    (hnear : P.a < P.splitDepth) {b : ℕ}
    (hb : b ∈ Finset.Icc (P.a+9) (P.splitDepth+6)) :
    BranchStep P.policy P.N P.q P.σ P.branchState .far (.D b P.t (P.i+1)) :=
  BranchStep.far hwide hnear hb

theorem directWeight_eq_branchExponent (P : PolicyJetData m) (p : ℕ) (lam σ ε : ℝ)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N) :
    P.directWeight p lam σ ε = ((2:ℝ)^P.N)^(branchExponent P.policy
      (dimensionalBranchReserve (m+3) lam σ) σ ε P.branchState .direct
        (.H P.a₀ P.t₀ p P.t P.i)) := by
  simp only [directWeight,branchExponent,branchCost,branchState,BranchState.start,
    reduceCtorEq,ite_false,hprofile]

theorem nearWeight_eq_branchExponent (P : PolicyJetData m) (lam σ ε : ℝ)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N) :
    P.farWeight P.splitDepth lam σ ε = ((2:ℝ)^P.N)^(branchExponent P.policy
      (dimensionalBranchReserve (m+3) lam σ) σ ε P.branchState .near
        (.H P.a₀ P.t₀ P.splitDepth P.t P.i)) := by
  simp only [farWeight,branchExponent,branchCost,branchState,BranchState.start,
    reduceCtorEq,ite_false,hprofile,add_zero]

theorem farWeight_eq_branchExponent (P : PolicyJetData m) (b : ℕ) (lam σ ε : ℝ)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N) :
    P.farWeight b lam σ ε = ((2:ℝ)^P.N)^(branchExponent P.policy
      (dimensionalBranchReserve (m+3) lam σ) σ ε P.branchState .far (.D b P.t (P.i+1))) := by
  simp only [farWeight,branchExponent,branchCost,branchState,BranchState.start,
    reduceCtorEq,ite_false,hprofile,add_zero]

end PolicyJetData
end Falconer

end OAI
