import OAI.NumberTheory.Ostmann.Arithmetic.MovingOneGiantDiagonal
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateWeightedSupport

namespace OAI

/-! # The original restored coefficient in the grouped diagonal estimate -/

namespace Ostmann
open scoped Classical BigOperators

/-- Every support condition in the grouped diagonal estimate follows from
the original coefficient and the prescribed prime/frequency ranges. Only
the mass of an actual product/frequency fibre remains to be bounded. -/
theorem movingTemplate_restored_diagonal_le {σ A : Type} [Fintype σ] [Fintype A]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → σ) (p : ℕ)
    (X : A → ℕ) (hX : ∀ a, (X a).Prime)
    (y : A → MovingRegularSlot n r m → σ) (v : A → ℤ)
    (α : A → ℝ) (hα : ∀ a, 0 ≤ α a) (θ : ℕ × ℕ × ℤ → ℝ)
    (hv : ∀ a, (v a).natAbs ≤ V n)
    (hvg : ∀ a, V n < X a) (hvr : ∀ a i, V n < value (y a i))
    (hsep : ∀ a b i, X a ≠ value (y b i))
    (hmass : ∀ k, (∑ a, if (X a, (∏ i, value (y a i)), v a) = k then α a else 0) ≤ θ k)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    let _ : ∀ a, Fact (X a).Prime := fun a => ⟨hX a⟩
    let _ : ∀ a i, Fact (((value ∘ y a) i)).Prime := fun a i => ⟨hvalue (y a i)⟩
    let C := fun a => movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n (4 + r) m (v a) (movingRestoreSample n r m u (y a)) p (X a)
    let D := p * (∏ i, value (u i)) * outside.prod
    (pivotDiagonal (fun a => X a * ∏ i, value (y a i)) v
      (fun a => (α a : ℂ) * C a *
        movingRegularTransform (movingOneGiantModuli (X a) (value ∘ y a))
          (movingOneGiantFactors (X a) (value ∘ y a) greg ggiant favorable) D (v a))).re ≤
    ∑ a, α a * θ (X a, (∏ i, value (y a i)), v a) *
      ‖C a * primeProductTransform greg (D * X a) (∏ i, value (y a i)) (v a)‖ ^ 2 := by
  let : ∀ a, Fact (X a).Prime := fun a => ⟨hX a⟩
  let : ∀ a i, Fact (((value ∘ y a) i)).Prime := fun a i => ⟨hvalue (y a i)⟩
  let C := fun a => movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
    n (4 + r) m (v a) (movingRestoreSample n r m u (y a)) p (X a)
  have hc a (ha : (α a : ℂ) * C a ≠ 0) : C a ≠ 0 := right_ne_zero_of_mul ha
  have hi a (ha : (α a : ℂ) * C a ≠ 0) : Function.Injective (value ∘ y a) := by
    have hs := movingTemplateCoefficient_restored_support value outside μ childBound pivotBound V F
      φ G n r m (v a) u (y a) p (X a) (hc a ha)
    intro i j hij
    by_contra hne
    have hh := hs.2.2.1 (show (Sum.inr i : Unit ⊕ MovingRegularSlot n r m) ≠ .inr j from
      fun he => hne (Sum.inr.inj he))
    change (value (y a i)).Coprime (value (y a j)) at hh
    change value (y a i) = value (y a j) at hij
    rw [hij] at hh
    exact (hvalue (y a j)).ne_one (by simpa only [Nat.coprime_self] using hh)
  have hz a (ha : (α a : ℂ) * C a ≠ 0) : v a ≠ 0 := by
    intro he
    apply hc a ha
    simpa only [C, movingTemplateCoefficient, he] using
      movingFrequencyCoefficient_zero value outside μ childBound pivotBound V F hF φ G n
        (treeLeafMap (List.map (movingRestoreSample n r m u (y a))) n
          (movingTemplateSmall n (4 + r) m))
        (treeLeafMap (List.map (movingRestoreSample n r m u (y a))) n
          (bulkSlotLeaves n m (movingTemplateBulk n (4 + r) m))) p (X a)
  exact movingOneGiant_weighted_pivot_diagonal_le X (fun a => value ∘ y a) greg ggiant favorable
    (p * (∏ i, value (u i)) * outside.prod) v α C θ hα hi hz
    (fun a _ => (hv a).trans_lt (hvg a)) (fun a _ i => (hv a).trans_lt (hvr a i))
    (fun a b _ _ i => hsep a b i) hmass

end Ostmann

end OAI
