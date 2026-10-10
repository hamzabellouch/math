import OAI.MeasureTheory.Falconer.Angular.AngularTransformSplitting
import OAI.MeasureTheory.Falconer.Fourier.InheritedSymbolMeasurability

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem inheritedCircleSymbol_norm_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (B : ℝ)
    (hh : ∀ x, ‖h x‖ ≤ B) (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K)
    (x : Plane) (ω : UnitCircle) :
    ‖inheritedCircleSymbol S b k Q ρ m N lam sig J i h x ω‖ ≤
      B * symbolDerivativeConstant K^K := by
  unfold inheritedCircleSymbol
  rw [norm_mul, Complex.norm_real]
  exact (mul_le_mul_of_nonneg_right (hh x) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left
      (inheritedMaskProduct_zero_bound S b k Q hQ ρ m N lam sig J i (fun _ => x) K hK _)
      ((norm_nonneg (h x)).trans (hh x)))

theorem actual_inherited_transform_split {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ)
    (hh : Measurable h) (B : ℝ) (hB : ∀ x, ‖h x‖ ≤ B)
    (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K) (A : CellPath) (n : ℕ)
    (Ma Mp r : ℝ) (hMp : Mp ≠ 0) (ω : UnitCircle) :
    sourceAngularTransform ρ (Q.descendant A).carrier Ma
      (inheritedCircleSymbol S b k Q ρ m N lam sig J i h) r ω =
      (Mp / Ma) • ∑ P ∈ occupiedAnchorPaths (Q.descendant A) ρ n,
        sourceAngularTransform ρ ((Q.descendant A).descendant P).carrier Mp
          (inheritedCircleSymbol S b k Q ρ m N lam sig J i h) r ω := by
  exact sourceAngularTransform_split (Q.descendant A) (Q.descendant_side_pos hQ A)
    ρ n Ma Mp hMp _ (measurable_inheritedCircleSymbol S b k Q ρ m N lam sig J i h hh)
    (B * symbolDerivativeConstant K^K)
    (inheritedCircleSymbol_norm_bound S b k Q hQ ρ m N lam sig J i h B hB K hK) r ω

theorem actual_inherited_transform_sum_norm_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ)
    (B : ℝ) (hB : ∀ x, ‖h x‖ ≤ B) (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K)
    (A : CellPath) (n : ℕ) (Mp r : ℝ) (hMp : 0 < Mp) (ω : UnitCircle) :
    (∑ P ∈ occupiedAnchorPaths (Q.descendant A) ρ n,
      ‖sourceAngularTransform ρ ((Q.descendant A).descendant P).carrier Mp
        (inheritedCircleSymbol S b k Q ρ m N lam sig J i h) r ω‖) ≤
      (B * symbolDerivativeConstant K^K) * (ρ (Q.descendant A).carrier).toReal / Mp := by
  exact sourceAngularTransform_sum_norm_le (Q.descendant A) (Q.descendant_side_pos hQ A)
    ρ n Mp hMp _ (B * symbolDerivativeConstant K^K)
    (inheritedCircleSymbol_norm_bound S b k Q hQ ρ m N lam sig J i h B hB K hK) r ω

end PlanarFalconer

end OAI
