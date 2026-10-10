import OAI.MeasureTheory.Falconer.Fourier.ParentInactiveKernel
import OAI.MeasureTheory.Falconer.Recursion.ParentBinSelection
import OAI.MeasureTheory.Falconer.Geometry.CellwiseDistanceForm
import OAI.MeasureTheory.Falconer.Estimates.ActualTransformSplitting

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_parent_discarded_F
    {sig κ T : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ)
    (K₁ K₂ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L n : ℕ) (a p v r : ℝ), p = a+n →
    κ*(N : ℝ) ≤ p-a → p-a ≤ v-p+2*sig*(N : ℝ) → 10*sig*(N : ℝ) ≤ v-p →
    (L : ℝ) ≤ v-p+2*sig*(N : ℝ) →
    ∀ X Y : DyadicSquare, 0 < X.side → 0 < Y.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    100*(2:ℝ)^(-a) ≤ dist X.center Y.center →
    dist X.center Y.center ≤ 2000*(2:ℝ)^(-a) →
    ∀ Ψ : ℝ → ℝ, (∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4) →
    Ψ (r/(2:ℝ)^v) ≠ 0 →
    ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂],
    ∀ (S₁ : Finset ι₁) (b₁ : ι₁ → PolicyDescriptor) (k₁ : ι₁ → ℕ)
      (S₂ : Finset ι₂) (b₂ : ι₂ → PolicyDescriptor) (k₂ : ι₂ → ℕ),
    S₁.card ≤ (N+1)^3+1 → (∑ d ∈ S₁, k₁ d) ≤ K₁ →
    S₂.card ≤ (N+1)^3+1 → (∑ d ∈ S₂, k₂ d) ≤ K₂ →
    (∀ d ∈ S₁, descriptorLength (b₁ d) ≤ L) → (∀ d ∈ S₂, descriptorLength (b₂ d) ≤ L) →
    ∀ Q₁ Q₂ : DyadicSquare, 0 < Q₁.side → 0 < Q₂.side →
    ∀ (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂], ∀ (m₁ m₂ : ℝ → ℝ) (lam₁ lam₂ : ℝ)
      (J₁ i₁ J₂ i₂ : ℕ) (h₁ h₂ : Plane → ℂ),
    Measurable h₁ → Measurable h₂ → (∀ x, ‖h₁ x‖ ≤ 1) → (∀ y, ‖h₂ y‖ ≤ 1) →
    ∀ M₁ M₂ : ℝ, 0 < M₁ → 0 < M₂ →
    ‖sourceCellwiseDistanceF X Y ρ₁ ρ₂ n n M₁ M₂
      (fun A B dir => sourceConeCircle (sourceParentAxis X Y) dir *
        sourceParentInactiveSelection N sig (p-a) X Y A B dir)
      (inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ h₁)
      (inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ h₂) r‖ ≤
      ((2:ℝ)^N)^(-T) * ((ρ₁ X.carrier).toReal/M₁) * ((ρ₂ Y.carrier).toReal/M₂) := by
  obtain ⟨N₀,hN₀⟩ := uniform_parent_inactive_kernel (T := T) (outer := 0) hsig hgap K₁ K₂
  refine ⟨N₀,?_⟩
  intro N hN L n a p v r hp hlow ht hu hL X Y hX hY hXa hYa hlo hhi Ψ hΨ hr
    ι₁ ι₂ inst₁ inst₂ S₁ b₁ k₁ S₂ b₂ k₂ hc₁ hk₁ hc₂ hk₂ hl₁ hl₂ Q₁ Q₂ hQ₁ hQ₂
    ρ₁ ρ₂ hρ₁ hρ₂ m₁ m₂ lam₁ lam₂ J₁ i₁ J₂ i₂ hsp₁ hsp₂ hm₁ hm₂ hb₁ hb₂ M₁ M₂ hM₁ hM₂
  have hmeas₁ := measurable_inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ hsp₁ hm₁
  have hmeas₂ := measurable_inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ hsp₂ hm₂
  have hnorm₁ : ∀ x dir, ‖inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ hsp₁ x dir‖ ≤
      symbolDerivativeConstant K₁^K₁ := by
    intro x dir
    simpa only [one_mul] using inheritedCircleSymbol_norm_bound S₁ b₁ k₁ Q₁ hQ₁ ρ₁ m₁ N
      lam₁ sig J₁ i₁ hsp₁ 1 hb₁ K₁ hk₁ x dir
  have hnorm₂ : ∀ x dir, ‖inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ hsp₂ x dir‖ ≤
      symbolDerivativeConstant K₂^K₂ := by
    intro x dir
    simpa only [one_mul] using inheritedCircleSymbol_norm_bound S₂ b₂ k₂ Q₂ hQ₂ ρ₂ m₂ N
      lam₂ sig J₂ i₂ hsp₂ 1 hb₂ K₂ hk₂ x dir
  apply sourceCellwiseDistanceF_kernel_bound X Y hX hY ρ₁ ρ₂ n n hM₁ hM₂ _ _ _
    (fun A B => (measurable_sourceConeCircle _).mul (sourceParentInactiveSelection_measurable _ _ _ _ _ A B))
    hmeas₁ hmeas₂ (by norm_num : (0:ℝ) ≤ 1)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _)
    (fun A B dir => by
      simp only [Pi.mul_apply, norm_mul]
      exact (mul_le_mul (sourceConeCircle_norm_le _ dir)
        (sourceParentInactiveSelection_norm_le _ _ _ _ _ A B dir) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
    hnorm₁ hnorm₂ r
  intro A hA B hB x hx y hy
  have hlenA : A.length = n := (mem_dyadicPaths n A).mp (Finset.mem_filter.mp hA).1
  have hlenB : B.length = n := (mem_dyadicPaths n B).mp (Finset.mem_filter.mp hB).1
  have hh := hN₀ N hN L a p v r hlow ht hu hL X Y (X.descendant A) (Y.descendant B)
    hX hY (X.descendant_side_pos hX A) (Y.descendant_side_pos hY B) hXa hYa
    (by simpa only [hp] using X.descendant_side_at_depth hXa hlenA)
    (by simpa only [hp] using Y.descendant_side_at_depth hYa hlenB)
    (X.descendant_subset hX A) (Y.descendant_subset hY B) hlo hhi Ψ hΨ hr
    S₁ b₁ k₁ S₂ b₂ k₂ hc₁ hk₁ hc₂ hk₂ hl₁ hl₂ Q₁ Q₂ hQ₁ hQ₂
    ρ₁ ρ₂ m₁ m₂ lam₁ lam₂ J₁ i₁ J₂ i₂ hsp₁ hsp₂ x y hm₁ hm₂ (hb₁ x) (hb₂ y) hx hy
  simpa only [Real.rpow_zero, one_mul, sourceParentInactiveSelection, Pi.mul_def] using hh

end PlanarFalconer

end OAI
