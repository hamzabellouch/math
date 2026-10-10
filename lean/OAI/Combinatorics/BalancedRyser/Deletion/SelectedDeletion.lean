import OAI.Combinatorics.BalancedRyser.Candidates.Candidates
import OAI.Combinatorics.BalancedRyser.Deletion.Deletion

namespace OAI

noncomputable section
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

namespace Balanced
open scoped _root_.Balanced
namespace SelectedDeletion

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

abbrev Output := Slot F → F

abbrev Kernel := MergedPairs F → Output F → ℝ

variable {F}

def configuration (M : MergedPairs F) (s : Output F) : Configuration F :=
  ⟨M, fun i => retainedChoice M (i.1, s i)⟩

def InitialGood (M : MergedPairs F) (c C : ℝ) : Prop :=
  CandidateGraphGood M c C ∧ DistinctConstituents M

def IsExperiment (κ : Kernel F) (c C : ℝ) : Prop :=
  (∀ M s, 0 ≤ κ M s) ∧
  (∀ M, ∑ s, κ M s ≤ 1) ∧
  (∀ M, ¬ InitialGood M c C → ∀ s, κ M s = 0) ∧
  (∀ M s, 0 < κ M s →
    (configuration M s).Valid ∧ (configuration M s).Compatible)

def fixedSuccessMass (κ : Kernel F) (M : MergedPairs F) : ℝ :=
  ∑ s, κ M s

def fixedCylinderMass (κ : Kernel F) (M : MergedPairs F)
    (J : Finset (Slot F)) (prescribed : Output F) : ℝ :=
  ∑ s, if ∀ i ∈ J, s i = prescribed i then κ M s else 0

def jointMass (κ : Kernel F) (E : MergedPairs F → Output F → Prop) : ℝ :=
  ∑ M, ((offsetLaw F) M).toReal * ∑ s, if E M s then κ M s else 0

def successMass (κ : Kernel F) : ℝ := jointMass κ (fun _ _ => True)

def deletionJointMass (κ : Kernel F) (D : DeletionSet F 3) : ℝ :=
  jointMass κ (fun M s => (configuration M s).deletedLines = D.val)

def RealizesConditionalLaw (κ : Kernel F) (Q : PMF (DeletionSet F 3)) : Prop :=
  ∀ D, (Q D).toReal = deletionJointMass κ D / successMass κ

def occupancyFailureMass (κ : Kernel F) (ρ : ℝ) : ℝ :=
  jointMass κ (fun M s =>
    ¬ (configuration M s).Occupancy ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊)

end SelectedDeletion

universe u

def SelectedDeletionResult : Prop :=
  ∃ c C K ρ a₀ C₀ : ℝ, ∃ ε : ℕ → ℝ, ∃ N : ℕ,
    0 < c ∧ 0 < C ∧ 1 ≤ K ∧ 0 < ρ ∧ ρ < 1 ∧
    0 < a₀ ∧ 0 < C₀ ∧ 4 ≤ N ∧
    (∀ q, 0 ≤ ε q) ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      N ≤ Fintype.card F →
      ∃ κ : SelectedDeletion.Kernel F,
        SelectedDeletion.IsExperiment κ c C ∧
        (∀ M, SelectedDeletion.InitialGood M c C →
          1 - ε (Fintype.card F) ≤ SelectedDeletion.fixedSuccessMass κ M) ∧
        (∀ M (J : Finset (Slot F)) (prescribed : SelectedDeletion.Output F),
          SelectedDeletion.fixedCylinderMass κ M J prescribed ≤
            (K / (Fintype.card F : ℝ)) ^ J.card) ∧
        a₀ ≤ SelectedDeletion.successMass κ ∧
        SelectedDeletion.occupancyFailureMass κ ρ ≤ ε (Fintype.card F) ∧
        ∃ Q : PMF (DeletionSet F 3),
          SelectedDeletion.RealizesConditionalLaw κ Q ∧ DeletionDominated 3 C₀ Q

end Balanced

end

end OAI
