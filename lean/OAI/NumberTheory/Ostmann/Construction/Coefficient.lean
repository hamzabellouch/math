import OAI.NumberTheory.Ostmann.Construction.History

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction

def outsideProduct (outside : List ℕ) : ℕ := outside.prod

def modFraction (p : ℕ) (s : ℤ) (denominator : ℕ) : ZMod p :=
  (s : ZMod p) * (denominator : ZMod p)⁻¹

def baseCoefficient (X : ℝ) (ψhat : ℝ → ℂ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ)
    (outside : List ℕ) (a : State) : ℂ :=
  let total := outsideProduct outside * a.product
  (Real.sqrt (X / total) : ℂ) * ψhat (- (a.frequency : ℝ) * X / total) *
    (bins outside a : ℂ) *
    (outside.map fun q => g q (modFraction q a.frequency ((outsideProduct outside / q) * a.product))).prod

namespace History

def internalMass (prior : SmallSlot → ℝ) : {l : ℕ} → History l → ℝ
  | _, .leaf _ => 1
  | _, .node _ _ u _ _ left right =>
      (u.map fun q => prior q).prod *
        internalMass prior left * internalMass prior right

theorem internalMass_eq_occurrences (prior : SmallSlot → ℝ)
    {l : ℕ} (h : History l) :
    h.internalMass prior =
      (h.internalOccurrences.map fun q => prior q).prod := by
  induction h with
  | leaf a => simp [internalMass, internalOccurrences]
  | @node l a p u hp hm left right ihl ihr =>
      simp only [internalMass, internalOccurrences, List.map_append, List.prod_append,
        ihl, ihr, mul_assoc]

theorem internalMass_nonneg (prior : SmallSlot → ℝ)
    (hprior : ∀ q, 0 ≤ prior q) {l : ℕ} (h : History l) :
    0 ≤ h.internalMass prior := by
  rw [internalMass_eq_occurrences]
  apply List.prod_nonneg
  intro x hx
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
  exact hprior _

end History

def coefficient {l : ℕ} (histories : Finset (History l))
    (prior : SmallSlot → ℝ) (V : ℕ → ℕ) (outside : List ℕ)
    (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ) (a : State) : ℂ := by
  classical
  exact ∑ h ∈ histories, if h.root = a then
    (h.internalMass prior : ℂ) * h.supportedWeight V outside base φ G else 0

def regularTransform (g giant : (p : ℕ) → ZMod p → ℂ)
    (outside : List ℕ) (a : State) : ℂ :=
  let R := a.product
  let d := outsideProduct outside
  giant a.giantPlus (modFraction a.giantPlus a.frequency (d * (R / a.giantPlus))) *
    giant a.giantMinus (modFraction a.giantMinus a.frequency (d * (R / a.giantMinus))) *
    (a.small.map fun q => g q.value (modFraction q.value a.frequency (d * (R / q.value)))).prod

def amplitude (states : Finset State)
    (outerMass : State → ℝ) (g giant : (p : ℕ) → ZMod p → ℂ)
    (outside : List ℕ) (A : State → ℂ) : ℂ :=
  ∑ a ∈ states, (outerMass a : ℂ) * regularTransform g giant outside a * A a

@[simp] theorem coefficient_empty {l : ℕ}
    (prior : SmallSlot → ℝ) (V : ℕ → ℕ) (outside : List ℕ)
    (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ) (a : State) :
    coefficient (∅ : Finset (History l)) prior V outside base φ G a = 0 := by
  classical
  simp [coefficient]

end Ostmann.Construction

end

end OAI
