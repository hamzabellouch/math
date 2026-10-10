import OAI.Combinatorics.Ryser.LineCover.Definitions
import OAI.Combinatorics.Ryser.LineCover.DeletionDefinitions
import OAI.Combinatorics.Ryser.Probability.Product

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

structure DeletionProcess (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (D : ℕ) (δ : ℝ) where
  shapes : Finset (Finset (Point F))
  shapeCount : shapes.card ≤ D * Fintype.card F ^ D
  shapeSize : ∀ S ∈ shapes, S.card ≤ D * Fintype.card F
  sparse : SparseShapes shapes D
  trialsCount : ℕ
  trials : Fin trialsCount → FiniteLaw (Outcome shapes D)
  trialsCount_le : trialsCount ≤ D * Fintype.card F
  pointCap : ∀ i x,
    (trials i).prob (fun a => x ∈ deleted ∅ a) ≤ (D : ℝ) / Fintype.card F
  survival : ℝ
  survivalLower : δ ≤ survival
  uniformSurvival : ∀ x,
    (FiniteLaw.pi trials).prob (fun ω => x ∈ survivors ∅ ω) = survival
  lineCap : ∀ l : AffineLine F,
    (∑ i, (trials i).prob (fun a => ∃ S ∈ a.val, S.val = linePoints l)) ≤
      (D : ℝ) / Fintype.card F

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {shapes : Finset (Finset (Point F))} {D n : ℕ}

def GoodLineCover (δ ρ : ℝ) (ω : Fin n → Outcome shapes D) : Prop :=
  (∀ l : AffineLine F,
    δ * Fintype.card F / 2 ≤
      ((survivors {linePoints l} ω ∩ linePoints l).card : ℝ)) ∧
  (∀ L : Finset (AffineLine F), L.card ≤ Fintype.card F →
    (survivors ∅ ω \ L.biUnion linePoints).card ≤ 2 * Fintype.card F →
    ∃ p : ProjectivePoint F,
      (1 - ρ) * Fintype.card F ≤ ((coverPencil L p).card : ℝ))

namespace DeletionProcess

variable {δ : ℝ} (process : DeletionProcess F D δ)

abbrev Config := Fin process.trialsCount → Outcome process.shapes D

def law : FiniteLaw process.Config := FiniteLaw.pi process.trials

def survivorSet (ω : process.Config) : Finset (Point F) := survivors ∅ ω

theorem point_survival_ge (x : Point F) :
    δ ≤ process.law.prob (fun ω => x ∈ process.survivorSet ω) := by
  change δ ≤ (FiniteLaw.pi process.trials).prob (fun ω => x ∈ survivors ∅ ω)
  rw [process.uniformSurvival]
  exact process.survivalLower

end DeletionProcess
end RyserCoveringCounterexample.LineCover

end

end OAI
