import OAI.NumberTheory.Ostmann.Arithmetic.PrimeMixedLineFamiliesProbability
import OAI.NumberTheory.Ostmann.Arithmetic.RepeatedLabels

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeMixedLineFamilies
open scoped BigOperators

def independentEquiv {κ : Type*} (I : κ → Type*) (K : κ → Type*)
    [∀ k, Field (K k)] (a b : ∀ k, I k → K k) :
    {z : ∀ k, K k × (K k)ˣ // ∀ k, CommonZero (a k) (b k) (z k)} ≃
      ∀ k, Solutions (a k) (b k) where
  toFun z k := ⟨z.val k, z.property k⟩
  invFun z := ⟨fun k => (z k).val, fun k => (z k).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem independent_card {κ : Type*} [Fintype κ] (I : κ → Type*) (K : κ → Type*)
    [∀ k, Field (K k)] (a b : ∀ k, I k → K k) :
    Nat.card {z : ∀ k, K k × (K k)ˣ // ∀ k, CommonZero (a k) (b k) (z k)} =
      ∏ k, Nat.card (Solutions (a k) (b k)) := by
  rw [Nat.card_congr (independentEquiv I K a b), Nat.card_pi]

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (I : κ → Type*) (p : κ → ℕ)
  [∀ k, Fact (p k).Prime]

def independentProbability (a b : ∀ k, I k → ZMod (p k)) : ℝ :=
  (Nat.card {z : ∀ k, ZMod (p k) × (ZMod (p k))ˣ //
    ∀ k, CommonZero (a k) (b k) (z k)} : ℝ) /
      Fintype.card (∀ k, ZMod (p k) × (ZMod (p k))ˣ)

theorem independentProbability_eq (a b : ∀ k, I k → ZMod (p k)) :
    independentProbability I p a b = ∏ k, probability (p k) (a k) (b k) := by
  classical
  simp only [independentProbability, independent_card, Fintype.card_pi,
    Nat.cast_prod, probability, Finset.prod_div_distrib]

theorem weighted_independentProbability {ι : Type*}
    (s : Finset ι) (label : ι → κ) (a b : ∀ k, I k → ZMod (p k)) :
    (∏ i ∈ s, (p (label i) : ℝ)) * independentProbability I p a b =
      ∏ k, (p k : ℝ) ^ RepeatedLabels.multiplicity s label k *
        probability (p k) (a k) (b k) := by
  rw [RepeatedLabels.product_by_multiplicity s label (fun k => (p k : ℝ)),
    independentProbability_eq,
    Finset.prod_mul_distrib]

end Ostmann.Arithmetic.PrimeMixedLineFamilies

end

end OAI
