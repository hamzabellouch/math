import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGraphDegree
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridNeighbors

namespace OAI

/-! Bounded vertex density and degree bound the number of nearby edge anchors. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaNearVertexCard_bound {n rows width A : ℕ} (cell : Fin n → QMAGridCell rows width)
    (hc : ∀ p, (Finset.univ.filter (fun v => cell v = p)).card ≤ A) (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun v => cell v ∈ qmaGridNeighbors p)).card ≤ 9*A := by
  let fiber := fun q => Finset.univ.filter (fun v => cell v = q)
  have heq : Finset.univ.filter (fun v => cell v ∈ qmaGridNeighbors p) =
      (qmaGridNeighbors p).biUnion fiber := by
    ext v
    simp [fiber]
  rw [heq]
  calc
    _ ≤ ∑ q ∈ qmaGridNeighbors p, (fiber q).card := Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ qmaGridNeighbors p, A := Finset.sum_le_sum (fun q _ => hc q)
    _ = (qmaGridNeighbors p).card*A := by simp
    _ ≤ 9*A := Nat.mul_le_mul_right A (qmaGridNeighbors_card p)

theorem qmaLeftIncidence_le_degree {ν : Type*} [Fintype ν] {n : ℕ}
    (left right : ν → Fin n) (v : Fin n) :
    (Finset.univ.filter (fun e => left e = v)).card ≤ qmaGraphDegree left right v := by
  have heq : (Finset.univ.filter (fun e => left e = v)).card =
      (∑ e, if left e = v then 1 else 0 : ℕ) := by simp
  rw [heq]
  apply Finset.sum_le_sum
  intro e _
  by_cases h : left e = v
  · simp [h]
  · simp [h]

theorem qmaAnchor_density {ν : Type*} [Fintype ν] {n rows width A D : ℕ}
    (left right : ν → Fin n) (cell : Fin n → QMAGridCell rows width)
    (anchor : ν → QMAGridCell rows width)
    (hnear : ∀ e, QMAGridCellsNear (cell (left e)) (anchor e))
    (hc : ∀ p, (Finset.univ.filter (fun v => cell v = p)).card ≤ A)
    (hd : ∀ v, qmaGraphDegree left right v ≤ D) (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun e => anchor e = p)).card ≤ 9*A*D := by
  let near := Finset.univ.filter (fun v => cell v ∈ qmaGridNeighbors p)
  let fiber := fun v => Finset.univ.filter (fun e => left e = v)
  have hsub : Finset.univ.filter (fun e => anchor e = p) ⊆ near.biUnion fiber := by
    intro e he
    have hp := (Finset.mem_filter.mp he).2
    apply Finset.mem_biUnion.mpr
    refine ⟨left e,?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,(qmaGridNeighbors_mem p _).mpr ?_⟩
      simpa only [hp] using hnear e
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  calc
    _ ≤ (near.biUnion fiber).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ near, (fiber v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ near, D := Finset.sum_le_sum (fun v _ =>
      (qmaLeftIncidence_le_degree left right v).trans (hd v))
    _ = near.card*D := by simp
    _ ≤ (9*A)*D := Nat.mul_le_mul_right D (qmaNearVertexCard_bound cell hc p)

end ContinuumCoulomb

end

end OAI
