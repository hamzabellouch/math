import OAI.NumberTheory.Ostmann.Construction.BaseFactors

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
namespace History

def compensationProduct {l : ℕ} (h : History l) : ℕ :=
  (h.internalOccurrences.map SmallSlot.value).prod

def cellWeight (φ : ℝ → ℝ) (G : ℝ) : {l : ℕ} → History l → ℝ
  | _, .leaf _ => 1
  | _, .node _ p _ _ _ left right => φ (Real.log p-G)*cellWeight φ G left*cellWeight φ G right

theorem compensationProduct_node {l : ℕ} (a : State) (p : ℕ)
    (u hp hm : List SmallSlot) (left right : History l) :
    compensationProduct (.node a p u hp hm left right)=
      (u.map SmallSlot.value).prod*compensationProduct left*compensationProduct right := by
  simp only [compensationProduct, internalOccurrences, List.map_append, List.prod_append, mul_assoc]

theorem realWeight_eq_compensation_cellWeight (φ : ℝ → ℝ) (G : ℝ)
    {l : ℕ} (h : History l) : realWeight φ G h=(h.compensationProduct:ℝ)*h.cellWeight φ G := by
  induction h with
  | leaf a => simp [realWeight, compensationProduct, internalOccurrences, cellWeight]
  | @node l a p u hp hm left right ihl ihr =>
    rw [realWeight, compensationProduct_node, cellWeight, ihl, ihr]
    push_cast
    ring

theorem cellWeight_bounds (φ : ℝ → ℝ) (G : ℝ)
    (hφ : ∀ x, 0≤φ x ∧ φ x≤1) {l : ℕ} (h : History l) :
    0≤h.cellWeight φ G ∧ h.cellWeight φ G≤1 := by
  induction h with
  | leaf a => exact ⟨zero_le_one,le_rfl⟩
  | @node l a p u hp hm left right ihl ihr =>
    have hp := hφ (Real.log p-G)
    constructor
    · exact mul_nonneg (mul_nonneg hp.1 ihl.1) ihr.1
    · exact (mul_le_mul (mul_le_mul hp.2 ihl.2 ihl.1 zero_le_one) ihr.2 ihr.1
        (by norm_num : (0:ℝ)≤1*1)).trans_eq (by norm_num)

end History

def smoothHistoryScalar (X : ℝ) (ψhat : ℝ → ℂ) (bins : List ℕ → State → ℝ)
    (outside : List ℕ) (φ : ℝ → ℝ) (G : ℝ) {l : ℕ} (h : History l) : ℂ :=
  (h.cellWeight φ G:ℂ)*h.leafProduct (baseScalar X ψhat bins outside)

theorem history_weight_eq_compensation_smooth_spectator (X : ℝ) (ψhat : ℝ → ℂ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ)
    (outside : List ℕ) (φ : ℝ → ℝ) (G : ℝ) {l : ℕ} (h : History l) :
    h.weight (baseCoefficient X ψhat g bins outside) φ G =
      (h.compensationProduct:ℂ)*smoothHistoryScalar X ψhat bins outside φ G h *
        h.leafProduct (spectatorFactor g outside) := by
  rw [history_weight_eq_scalar_spectator, historyScalar,
    History.realWeight_eq_compensation_cellWeight, Complex.ofReal_mul, Complex.ofReal_natCast]
  unfold smoothHistoryScalar
  ring

end Ostmann.Construction

end

end OAI
