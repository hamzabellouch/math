import OAI.NumberTheory.Ostmann.Construction.Coefficient

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction.History

def realWeight (φ : ℝ → ℝ) (G : ℝ) : {l : ℕ} → History l → ℝ
  | _, .leaf _ => 1
  | _, .node _ p u _ _ left right =>
    ((u.map SmallSlot.value).prod : ℝ)*φ (Real.log p-G)*
      realWeight φ G left*realWeight φ G right

def leafProduct (f : State → ℂ) : {l : ℕ} → History l → ℂ
  | _, .leaf a => f a
  | _, .node _ _ _ _ _ left right => leafProduct f left*conj (leafProduct f right)

theorem weight_eq_realWeight_leafProduct (f : State → ℂ) (φ : ℝ → ℝ) (G : ℝ)
    {l : ℕ} (h : History l) : weight f φ G h=(realWeight φ G h : ℂ)*leafProduct f h := by
  induction h with
  | leaf a => simp [weight, realWeight, leafProduct]
  | @node l a p u hp hm left right ihl ihr =>
    simp only [weight, realWeight, leafProduct, ihl, ihr, Complex.ofReal_mul,
      Complex.ofReal_natCast, map_mul, Complex.conj_ofReal]
    ring

theorem realWeight_nonneg (φ : ℝ → ℝ) (G : ℝ) (hφ : ∀ x, 0≤φ x)
    {l : ℕ} (h : History l) : 0≤realWeight φ G h := by
  induction h with
  | leaf a => exact zero_le_one
  | @node l a p u hp hm left right ihl ihr =>
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hφ _)) ihl) ihr

theorem leafProduct_mul (f g : State → ℂ) {l : ℕ} (h : History l) :
    leafProduct (fun a => f a*g a) h = leafProduct f h*leafProduct g h := by
  induction h with
  | leaf a => rfl
  | @node l a p u hp hm left right ihl ihr =>
    simp only [leafProduct, ihl, ihr, map_mul]
    ring

theorem norm_leafProduct {l : ℕ} (h : History l) (f : State → ℂ) :
    ‖leafProduct f h‖=(h.leafStates.map (fun a => ‖f a‖)).prod := by
  induction h with
  | leaf a => simp [leafProduct, leafStates]
  | @node l a p u hp hm left right ihl ihr =>
    simp only [leafProduct, norm_mul, Complex.norm_conj, leafStates, List.map_append,
      List.prod_append, ihl, ihr]

theorem norm_leafProduct_le {l : ℕ} (h : History l) (f : State → ℂ) (B : State → ℝ)
    (hB : ∀ a∈h.leafStates, ‖f a‖≤B a) :
    ‖leafProduct f h‖≤(h.leafStates.map B).prod := by
  induction h with
  | leaf a => simpa [leafProduct, leafStates] using hB a (by simp [leafStates])
  | @node l a p u hp hm left right ihl ihr =>
    have hl : ∀ a∈left.leafStates, ‖f a‖≤B a := fun a ha => hB a (by simp [leafStates, ha])
    have hr : ∀ a∈right.leafStates, ‖f a‖≤B a := fun a ha => hB a (by simp [leafStates, ha])
    have hleft := ihl hl
    have hright := ihr hr
    simpa only [leafProduct, norm_mul, Complex.norm_conj, leafStates, List.map_append,
      List.prod_append] using mul_le_mul hleft hright (norm_nonneg _)
      ((norm_nonneg _).trans hleft)

end Ostmann.Construction.History

end

end OAI
