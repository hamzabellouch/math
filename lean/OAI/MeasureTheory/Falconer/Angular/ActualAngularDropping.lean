import OAI.MeasureTheory.Falconer.Angular.AngularEnergyDropping

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

 theorem actual_inherited_H_drop
    {ι₁ ι₂ : Type*} [DecidableEq ι₁] [DecidableEq ι₂]
    (S₁ : Finset ι₁) (S₂ : Finset ι₂) (b₁ : ι₁ → PolicyDescriptor) (b₂ : ι₂ → PolicyDescriptor)
    (k₁ : ι₁ → ℕ) (k₂ : ι₂ → ℕ) (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side) (ρ₁ ρ₂ : Measure Plane)
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P₁ P₂ : CellPath)
    (h₁ h₂ : Plane → ℂ) (K₁ K₂ : ℕ) (hK₁ : ∑ c ∈ S₁, k₁ c ≤ K₁)
    (hK₂ : ∑ c ∈ S₂, k₂ c ≤ K₂) {z₁ z₂ : Plane}
    (hz₁ : z₁ ∈ (Q₁.descendant P₁).carrier) (hz₂ : z₂ ∈ (Q₂.descendant P₂).carrier)
    (M₁ M₂ a v : ℝ) (Ψ : ℝ → ℝ) :
    sourceAngularH a v Ψ
      (fun z => sourceAngularTransform ρ₁ (Q₁.descendant P₁).carrier M₁
        (inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam sig J i h₁) z.1 z.2)
      (fun z => sourceAngularTransform ρ₂ (Q₂.descendant P₂).carrier M₂
        (inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam sig J i h₂) z.1 z.2) ≤
    (ENNReal.ofReal (symbolDerivativeConstant K₁^K₁)^2 *
      ENNReal.ofReal (symbolDerivativeConstant K₂^K₂)^2) *
    sourceAngularH a v Ψ
      (fun z => sourceAngularTransform ρ₁ (Q₁.descendant P₁).carrier M₁
        (inheritedCircleSymbol (S₁.filter fun c => P₁.length < descriptorAnchor (b₁ c))
          b₁ k₁ Q₁ ρ₁ m₁ N lam sig J i h₁) z.1 z.2)
      (fun z => sourceAngularTransform ρ₂ (Q₂.descendant P₂).carrier M₂
        (inheritedCircleSymbol (S₂.filter fun c => P₂.length < descriptorAnchor (b₂ c))
          b₂ k₂ Q₂ ρ₂ m₂ N lam sig J i h₂) z.1 z.2) := by
  apply sourceAngularH_le_of_enorm _ _ _ _ _ _ _ _ _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · intro z
    exact inherited_transform_drop_enorm S₁ b₁ k₁ Q₁ hQ₁ ρ₁ m₁ N lam sig J i P₁ h₁ K₁ hK₁ hz₁ M₁ z.1 z.2
  · intro z
    exact inherited_transform_drop_enorm S₂ b₂ k₂ Q₂ hQ₂ ρ₂ m₂ N lam sig J i P₂ h₂ K₂ hK₂ hz₂ M₂ z.1 z.2

 theorem remaining_symbol_budget {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (a K : ℕ) (hK : ∑ c ∈ S, k c ≤ K) :
    ∑ c ∈ S.filter (fun c => a < descriptorAnchor (b c)), k c ≤ K :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)).trans hK

end PlanarFalconer

end OAI
