import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateTransferSupport

namespace OAI

/-! # The original external weight multiplying a restored coefficient -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateTransferWeight {σ A : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (v : A → ℤ) (α : A → ℂ) (X : A → ℕ)
    (y : A → MovingRegularSlot n r m → σ)
    (u : TreeLeafIndex n × Fin 4 → σ) (p : ℕ) (a : A) : ℂ :=
  α a * movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m
    (v a) (movingRestoreSample n r m u (y a)) p (X a)

theorem movingTemplateTransferWeight_support {σ A : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (v : A → ℤ) (α : A → ℂ) (X : A → ℕ)
    (y : A → MovingRegularSlot n r m → σ)
    (u : TreeLeafIndex n × Fin 4 → σ) (p : ℕ) (a : A)
    (h : movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G n r m
      v α X y u p a ≠ 0) :
    let Q := Sum.elim (fun _ : Unit => p) (value ∘ u)
    let L := Sum.elim (fun _ : Unit => X a) (value ∘ y a)
    Pairwise (fun i j => (Q i).Coprime (Q j)) ∧
      (∀ i, outside.prod.Coprime (Q i)) ∧
      Pairwise (fun i j => (L i).Coprime (L j)) ∧
      (∏ i, L i).Coprime (∏ i, Q i) ∧
      (∀ i, outside.prod.Coprime (L i)) :=
  movingTemplateCoefficient_restored_support value outside μ childBound pivotBound V F φ G
    n r m (v a) u (y a) p (X a) (right_ne_zero_of_mul h)

end Ostmann

end OAI
