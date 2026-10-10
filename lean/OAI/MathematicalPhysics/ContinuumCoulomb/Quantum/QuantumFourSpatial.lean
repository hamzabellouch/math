import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBlockEdges
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridNeighbors
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialSubdivision

namespace OAI

/-! Four-spin encoding preserves neighboring-cell geometry and constant density. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
variable {n rows width : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

def qmaFourBlockCell (cell : Fin n → QMAGridCell rows width) (i : Fin (n*4)) :
    QMAGridCell rows width := cell (finProdFinEquiv.symm i).1

def qmaFourExchangeAnchor (cell : Fin n → QMAGridCell rows width)
    (pairAnchor : κ → QMAGridCell rows width) (fieldAnchor : τ → QMAGridCell rows width) :
    QMAFourExchangeIndex n κ τ → QMAGridCell rows width
  | .inl (i,_) => cell i
  | .inr (.inl (e,_)) => pairAnchor e
  | .inr (.inr (.inl (e,_))) => pairAnchor e
  | .inr (.inr (.inr (e,_))) => fieldAnchor e

omit [Fintype κ] [Fintype τ] in
theorem qmaFourExchange_spatial (cell : Fin n → QMAGridCell rows width)
    (pairAnchor : κ → QMAGridCell rows width) (fieldAnchor : τ → QMAGridCell rows width)
    (left right : κ → Fin n) (site : τ → Fin n)
    (hl : ∀ e, QMAGridCellsNear (cell (left e)) (pairAnchor e))
    (hr : ∀ e, QMAGridCellsNear (cell (right e)) (pairAnchor e))
    (hs : ∀ e, QMAGridCellsNear (cell (site e)) (fieldAnchor e))
    (x : QMAFourExchangeIndex n κ τ) :
    QMAGridCellsNear (qmaFourBlockCell cell (qmaFourExchangeLeft left right site x))
      (qmaFourExchangeAnchor cell pairAnchor fieldAnchor x) ∧
    QMAGridCellsNear (qmaFourBlockCell cell (qmaFourExchangeRight left right site x))
      (qmaFourExchangeAnchor cell pairAnchor fieldAnchor x) := by
  rcases x with ⟨i,k⟩ | (⟨e,p,q⟩ | (⟨e,s,k⟩ | ⟨e,k⟩))
  · simp only [qmaFourExchangeLeft,qmaFourExchangeRight,qmaFourBlockCell,
      Equiv.symm_apply_apply,qmaFourExchangeAnchor]
    exact ⟨qmaGridCellsNear_refl _,qmaGridCellsNear_refl _⟩
  · simpa only [qmaFourExchangeLeft,qmaFourExchangeRight,qmaFourBlockCell,
      Equiv.symm_apply_apply,qmaFourExchangeAnchor] using And.intro (hl e) (hr e)
  · simp only [qmaFourExchangeLeft,qmaFourExchangeRight,qmaFourBlockCell,
      Equiv.symm_apply_apply,qmaFourExchangeAnchor]
    split_ifs
    · exact ⟨hl e,hl e⟩
    · exact ⟨hr e,hr e⟩
  · simpa only [qmaFourExchangeLeft,qmaFourExchangeRight,qmaFourBlockCell,
      Equiv.symm_apply_apply,qmaFourExchangeAnchor] using And.intro (hs e) (hs e)

theorem qmaProductFilter_card {α β : Type*} [Fintype α] [Fintype β]
    (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun q : α × β => p q.1)).card =
      Fintype.card β*(Finset.univ.filter p).card := by
  have he : (Finset.univ.filter (fun q : α × β => p q.1)) =
      (Finset.univ.filter p) ×ˢ (Finset.univ : Finset β) := by ext q; simp
  rw [he,Finset.card_product]
  simp only [Finset.card_univ,Nat.mul_comm]

theorem qmaFourBlockCell_density (cell : Fin n → QMAGridCell rows width) {A : ℕ}
    (hcell : ∀ p, (Finset.univ.filter (fun i => cell i = p)).card ≤ A)
    (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun i => qmaFourBlockCell cell i = p)).card ≤ 4*A := by
  have he : (Finset.univ.filter (fun i => qmaFourBlockCell cell i = p)).card =
      (Finset.univ.filter (fun x : Fin n × Fin 4 => cell x.1 = p)).card := by
    apply Finset.card_equiv finProdFinEquiv.symm
    intro i
    constructor
    · intro hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
    · intro hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  rw [he,qmaProdFilter_card (α := Fin n) 4 (fun i => cell i = p)]
  exact Nat.mul_le_mul_left 4 (hcell p)

theorem qmaFourExchangeAnchor_density (cell : Fin n → QMAGridCell rows width)
    (pairAnchor : κ → QMAGridCell rows width) (fieldAnchor : τ → QMAGridCell rows width)
    {A B C : ℕ}
    (hcell : ∀ p, (Finset.univ.filter (fun i => cell i = p)).card ≤ A)
    (hp : ∀ p, (Finset.univ.filter (fun e => pairAnchor e = p)).card ≤ B)
    (hf : ∀ p, (Finset.univ.filter (fun e => fieldAnchor e = p)).card ≤ C)
    (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun e => qmaFourExchangeAnchor cell pairAnchor fieldAnchor e = p)).card ≤
      6*A+22*B+3*C := by
  rw [qmaSumFilter_card,qmaSumFilter_card,qmaSumFilter_card]
  change (Finset.univ.filter (fun x : Fin n × Fin 6 => cell x.1 = p)).card +
    ((Finset.univ.filter (fun x : κ × (Fin 4 × Fin 4) => pairAnchor x.1 = p)).card +
     ((Finset.univ.filter (fun x : κ × (Fin 2 × Fin 3) => pairAnchor x.1 = p)).card +
       (Finset.univ.filter (fun x : τ × Fin 3 => fieldAnchor x.1 = p)).card)) ≤ _
  rw [qmaProductFilter_card (fun i => cell i = p),
    qmaProductFilter_card (β := Fin 4 × Fin 4) (fun e => pairAnchor e = p),
    qmaProductFilter_card (β := Fin 2 × Fin 3) (fun e => pairAnchor e = p),
    qmaProductFilter_card (β := Fin 3) (fun e => fieldAnchor e = p)]
  simp only [Fintype.card_prod,Fintype.card_fin]
  have h1 := Nat.mul_le_mul_left 6 (hcell p)
  have h2 := Nat.mul_le_mul_left 16 (hp p)
  have h3 := Nat.mul_le_mul_left 6 (hp p)
  have h4 := Nat.mul_le_mul_left 3 (hf p)
  omega

end ContinuumCoulomb

end

end OAI
