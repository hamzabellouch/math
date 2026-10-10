import OAI.Combinatorics.EditApproximation.Binary.BinaryEnvelopeReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Online objective construction charges every historical table read,
including repeated uses in gain and decrement terms. -/

namespace EditApproximation
namespace BinaryFraction





@[simp] theorem gainReadWithWork_eq {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (s : ℕ) (i : β × σ) :
    (gainReadWithWork mass read s i).1 = (gainWithWork mass (fun t j => (read t j).1) s i).1 := rfl

@[simp] theorem decrementReadWithWork_eq {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (s : ℕ) (i : β × σ) :
    (decrementReadWithWork mass read s i).1 = (decrementWithWork mass (fun t j => (read t j).1) s i).1 := rfl



@[simp] theorem optimisticTermReadWithWork_eq {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (coefficient : BinaryFraction)
    (s : ℕ) (i : β × σ) :
    (optimisticTermReadWithWork mass read coefficient s i).1 =
      (optimisticTermWithWork mass (fun t j => (read t j).1) coefficient s i).1 := rfl

theorem optimisticTermReadWithWork_cost {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (coefficient : BinaryFraction)
    (s : ℕ) (i : β × σ) (R : ℕ) (hs : (read s i).2 ≤ R) (hs' : (read (s + 1) i).2 ≤ R) :
    (optimisticTermReadWithWork mass read coefficient s i).2 ≤
      (optimisticTermWithWork mass (fun t j => (read t j).1) coefficient s i).2 + 3 * R := by
  simp only [optimisticTermReadWithWork, optimisticTermWithWork, gainReadWithWork,
    decrementReadWithWork, gainWithWork, decrementWithWork]
  omega



theorem onlineLinearReadWithWork_eq_cost {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) (R : ℕ) (hr : ∀ s ≤ t + 1, (read s i).2 ≤ R) :
    (onlineLinearReadWithWork mass read eta kappa t i).1 =
      (onlineLinearWithWork mass (fun s j => (read s j).1) eta kappa t i).1 ∧
    (onlineLinearReadWithWork mass read eta kappa t i).2 ≤
      (onlineLinearWithWork mass (fun s j => (read s j).1) eta kappa t i).2 + (3 * t + 1) * R := by
  have ht := vectorMapWithWork_extra t
    (fun s => optimisticTermReadWithWork mass read (coefficientWithWork kappa).1 s.val i)
    (fun s => optimisticTermWithWork mass (fun t j => (read t j).1) (coefficientWithWork kappa).1 s.val i)
    (3 * R) (fun _ => rfl) (fun s => optimisticTermReadWithWork_cost mass read _ s.val i R
      (hr _ (by omega)) (hr _ (by omega)))
  have hcur := hr t (by omega)
  unfold onlineLinearReadWithWork onlineLinearWithWork
  dsimp only
  rw [ht.1]
  refine ⟨rfl, ?_⟩
  simp only [gainReadWithWork, gainWithWork]
  nlinarith only [ht.2, hcur]

def preparedBandOptimizerReadWithWork {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × σ → BinaryFraction × ℕ) (eta kappa : BinaryFraction)
    (band : List (Fin M → σ)) (G K t : ℕ) : Vector BinaryFraction d × ℕ :=
  let vertices := bandVerticesWithWork coordinates mass band
  let linear := vectorMapWithWork d fun i =>
    onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t (coordinates.get i)
  let answer := finiteOptimizerWithWork vertices.1 linear.1 G K
  (answer.1, vertices.2 + linear.2 + answer.2 + 2)

theorem preparedBandOptimizerReadWithWork_eq_cost {M d : ℕ} {σ : Type*} [DecidableEq σ]
    (coordinates : Vector (Fin M × σ) d) (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × σ → BinaryFraction × ℕ) (eta kappa : BinaryFraction)
    (band : List (Fin M → σ)) (G K t R : ℕ)
    (hr : ∀ s ≤ t + 1, ∀ i, (read s (coordinates.get i)).2 ≤ R) :
    (preparedBandOptimizerReadWithWork coordinates mass read eta kappa band G K t).1 =
      (preparedBandOptimizerWithWork coordinates mass (fun s j => (read s j).1) eta kappa band G K t).1 ∧
    (preparedBandOptimizerReadWithWork coordinates mass read eta kappa band G K t).2 ≤
      (preparedBandOptimizerWithWork coordinates mass (fun s j => (read s j).1) eta kappa band G K t).2 +
        d * ((3 * t + 1) * R) := by
  have hl := vectorMapWithWork_extra d
    (fun i => onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t (coordinates.get i))
    (fun i => onlineLinearWithWork (fun j => mass.get j) (fun s j => (read s j).1) eta kappa t (coordinates.get i))
    ((3 * t + 1) * R)
    (fun i => (onlineLinearReadWithWork_eq_cost _ read eta kappa t (coordinates.get i) R (fun s hs => hr s hs i)).1)
    (fun i => (onlineLinearReadWithWork_eq_cost _ read eta kappa t (coordinates.get i) R (fun s hs => hr s hs i)).2)
  unfold preparedBandOptimizerReadWithWork preparedBandOptimizerWithWork
  dsimp only
  rw [hl.1]
  exact ⟨rfl, by omega⟩

end BinaryFraction
end EditApproximation

end OAI
