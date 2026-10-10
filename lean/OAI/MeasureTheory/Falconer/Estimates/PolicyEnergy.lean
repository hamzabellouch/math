import OAI.MeasureTheory.Falconer.Recursion.PolicyFarSuccessors
import OAI.MeasureTheory.Falconer.Estimates.PolicyCommonBudgets

namespace OAI

/-! # The actual energies represented by scalar branch states

The context fixes the original measure, masks and profile. The constructors
carry the actual positive count or angular envelope, and the positive case
records the cell separation supplied by the far partition.
-/

namespace Falconer
open Set MeasureTheory

structure PolicyContext (m : ℕ) where
  Q : DyadicCube (m+3)
  ρ : Measure (Space (m+3))
  profile : ℝ → ℝ
  N : ℕ
  s : ℝ
  lam : ℝ
  σ : ℝ
  J : ℕ
  q : ℕ
  policy : ℕ → ℝ
  masks : PlanarFalconer.PolicyDescriptor → Finset (Sphere (m+3))
  Z : ℝ

def PolicyJetData.context {m : ℕ} (P : PolicyJetData m) : PolicyContext m :=
  ⟨P.Q,P.ρ,P.profile,P.N,P.s,P.lam,P.σ,P.J,P.q,P.policy,P.masks,P.Z⟩

inductive PolicyEnergy {m : ℕ} (K L : ℕ) (Ψ : ℝ → ℝ) (w₀ : Sphere (m+3)) :
    PolicyContext m → PlanarFalconer.BranchState → ℝ → Prop
  | positive (P : PolicyJetData m) (hleft : P.a₀ = P.a) (hright : P.t₀ = P.t)
      (lower : 125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖)
      (upper : ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
        2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side) :
      PolicyEnergy K L Ψ w₀ P.context P.positiveBranchState (P.positiveCount w₀)
  | angular (P : PolicyJetData m) :
      PolicyEnergy K L Ψ w₀ P.context P.branchState (P.envelope K L Ψ)

namespace PolicyJetData
variable {m : ℕ}

theorem context_child (P : PolicyJetData m) (p : ℕ) (hap : P.a ≤ p)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hr : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
      (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a)) :
    (P.child p hap row hr).context = P.context := rfl

theorem context_positiveSuccessor (P : PolicyJetData m) (v : ℕ) (hv : v ≤ P.t₀) (i : ℕ) :
    (P.positiveSuccessor v hv i).context = P.context := rfl

theorem context_farPositiveSuccessor (P : PolicyJetData m) (a : ℕ) (ha : P.a ≤ a)
    (U : List (Fin (m+3) → Bool)) (hU : U.length = P.a)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hr : row ∈ farCellPartners (P.Q.descendant U) P.ρ (a-P.a)) :
    (P.farPositiveSuccessor a ha U hU row hr).context = P.context := rfl

theorem energy_farPositiveSuccessor (P : PolicyJetData m) (K L : ℕ)
    (Ψ : ℝ → ℝ) (w₀ : Sphere (m+3)) (a : ℕ) (ha : P.a ≤ a)
    (U : List (Fin (m+3) → Bool)) (hU : U.length = P.a)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hr : row ∈ farCellPartners (P.Q.descendant U) P.ρ (a-P.a)) :
    PolicyEnergy K L Ψ w₀ P.context (.D a P.t (P.i+1))
      ((P.farPositiveSuccessor a ha U hU row hr).positiveCount w₀) := by
  have hg := P.farPositiveSuccessor_geometry a ha U hU row hr
  exact .positive (P.farPositiveSuccessor a ha U hU row hr) rfl rfl hg.1 hg.2


theorem energy_child (P : PolicyJetData m) (K L : ℕ) (Ψ : ℝ → ℝ) (w₀ : Sphere (m+3))
    (p : ℕ) (hap : P.a ≤ p)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hr : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
      (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a)) :
    PolicyEnergy K L Ψ w₀ P.context (.H P.a₀ P.t₀ p P.t P.i)
      ((P.child p hap row hr).envelope K L Ψ) := .angular (P.child p hap row hr)

theorem energy_positiveSuccessor (P : PolicyJetData m) (K L : ℕ)
    (Ψ : ℝ → ℝ) (w₀ : Sphere (m+3)) (v : ℕ) (hv : v ≤ P.t₀) (i : ℕ)
    (lower : 125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
      ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖)
    (upper : ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
      2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side) :
    PolicyEnergy K L Ψ w₀ P.context (.D P.a v i)
      ((P.positiveSuccessor v hv i).positiveCount w₀) :=
  .positive (P.positiveSuccessor v hv i) rfl rfl lower upper

end PolicyJetData
end Falconer

end OAI
