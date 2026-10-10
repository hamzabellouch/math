import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Basic.Real.Basic

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def neighbors (A : Finset α) (G : Finset (α × β)) (b : β) : Finset α :=
  A.filter fun a => (a, b) ∈ G

def commonNeighbors (B : Finset β) (G : Finset (α × β)) (a a' : α) : Finset β :=
  B.filter fun b => (a, b) ∈ G ∧ (a', b) ∈ G

def fourWalks (A : Finset α) (B : Finset β) (G : Finset (α × β)) (a a' : α) :
    Finset (Σ _ : α, β × β) :=
  A.sigma fun a₂ => commonNeighbors B G a a₂ ×ˢ commonNeighbors B G a₂ a'

@[simp] theorem mem_neighbors (A : Finset α) (G : Finset (α × β)) (a : α) (b : β) :
    a ∈ neighbors A G b ↔ a ∈ A ∧ (a, b) ∈ G := by
  simp only [neighbors, Finset.mem_filter]

@[simp] theorem mem_commonNeighbors (B : Finset β) (G : Finset (α × β))
    (a a' : α) (b : β) :
    b ∈ commonNeighbors B G a a' ↔ b ∈ B ∧ (a, b) ∈ G ∧ (a', b) ∈ G := by
  simp only [commonNeighbors, Finset.mem_filter]

@[simp] theorem mem_fourWalks (A : Finset α) (B : Finset β) (G : Finset (α × β))
    (a a' : α) (w : Σ _ : α, β × β) :
    w ∈ fourWalks A B G a a' ↔
      w.1 ∈ A ∧ w.2.1 ∈ commonNeighbors B G a w.1 ∧
        w.2.2 ∈ commonNeighbors B G w.1 a' := by
  simp only [fourWalks, Finset.mem_sigma, Finset.mem_product]

theorem neighbors_subset (A : Finset α) (G : Finset (α × β)) (b : β) :
    neighbors A G b ⊆ A := Finset.filter_subset _ _

theorem commonNeighbors_comm (B : Finset β) (G : Finset (α × β)) (a a' : α) :
    commonNeighbors B G a a' = commonNeighbors B G a' a := by
  ext b
  simp only [mem_commonNeighbors, and_comm]

theorem fourWalks_mono {A₀ A : Finset α} (hA : A₀ ⊆ A) (B : Finset β)
    (G : Finset (α × β)) (a a' : α) :
    fourWalks A₀ B G a a' ⊆ fourWalks A B G a a' :=
  Finset.sigma_mono hA (fun _ _ hw => hw)

theorem card_fourWalks (A : Finset α) (B : Finset β) (G : Finset (α × β))
    (a a' : α) :
    (fourWalks A B G a a').card =
      ∑ a₂ ∈ A, (commonNeighbors B G a a₂).card * (commonNeighbors B G a₂ a').card := by
  simp only [fourWalks, Finset.card_sigma, Finset.card_product]

theorem card_edges_eq_sum_neighbors (A : Finset α) (B : Finset β)
    (G : Finset (α × β)) (hG : G ⊆ A ×ˢ B) :
    G.card = ∑ b ∈ B, (neighbors A G b).card := by
  have hfilter : (A ×ˢ B).filter (fun e => e ∈ G) = G := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hG h, h⟩⟩
  calc
    G.card = ((A ×ˢ B).filter (fun e => e ∈ G)).card :=
      congrArg Finset.card hfilter.symm
    _ = ∑ b ∈ B, (neighbors A G b).card := by
      simp only [neighbors, Finset.card_filter, Finset.sum_product_right]

noncomputable section
attribute [local instance] Classical.propDecidable

def badPairs (A : Finset α) (B : Finset β) (G : Finset (α × β)) (t : ℝ) :
    Finset (α × α) :=
  (A ×ˢ A).filter fun p => ((commonNeighbors B G p.1 p.2).card : ℝ) < t

def badPartners (A : Finset α) (B : Finset β) (G : Finset (α × β))
    (t : ℝ) (a : α) : Finset α :=
  A.filter fun a' => ((commonNeighbors B G a a').card : ℝ) < t

def localBad (A : Finset α) (B : Finset β) (G : Finset (α × β))
    (t : ℝ) (b : β) : Finset (α × α) :=
  (badPairs A B G t).filter fun p => (p.1, b) ∈ G ∧ (p.2, b) ∈ G

@[simp] theorem mem_badPairs (A : Finset α) (B : Finset β) (G : Finset (α × β))
    (t : ℝ) (p : α × α) :
    p ∈ badPairs A B G t ↔
      (p.1 ∈ A ∧ p.2 ∈ A) ∧ ((commonNeighbors B G p.1 p.2).card : ℝ) < t := by
  simp only [badPairs, Finset.mem_filter, Finset.mem_product]

@[simp] theorem mem_badPartners (A : Finset α) (B : Finset β)
    (G : Finset (α × β)) (t : ℝ) (a a' : α) :
    a' ∈ badPartners A B G t a ↔
      a' ∈ A ∧ ((commonNeighbors B G a a').card : ℝ) < t := by
  simp only [badPartners, Finset.mem_filter]

theorem badPartners_subset (A : Finset α) (B : Finset β)
    (G : Finset (α × β)) (t : ℝ) (a : α) :
    badPartners A B G t a ⊆ A := Finset.filter_subset _ _

theorem card_badPairs_eq_sum_badPartners (A : Finset α) (B : Finset β)
    (G : Finset (α × β)) (t : ℝ) :
    (badPairs A B G t).card = ∑ a ∈ A, (badPartners A B G t a).card := by
  simp only [badPairs, badPartners, Finset.card_filter, Finset.sum_product]

theorem sum_localBad_card_eq_sum_common (A : Finset α) (B : Finset β)
    (G : Finset (α × β)) (t : ℝ) :
    (∑ b ∈ B, (localBad A B G t b).card) =
      ∑ p ∈ badPairs A B G t, (commonNeighbors B G p.1 p.2).card := by
  simp only [localBad, commonNeighbors, Finset.card_filter]
  exact Finset.sum_comm

theorem localBad_eq_badPairs_neighbors (A : Finset α) (B : Finset β)
    (G : Finset (α × β)) (t : ℝ) (b : β) :
    localBad A B G t b = badPairs (neighbors A G b) B G t := by
  ext p
  simp only [localBad, badPairs, neighbors, Finset.mem_filter, Finset.mem_product]
  simp only [and_assoc, and_left_comm, and_comm]

end

end RyserCoveringCounterexample.Incidence

end OAI
