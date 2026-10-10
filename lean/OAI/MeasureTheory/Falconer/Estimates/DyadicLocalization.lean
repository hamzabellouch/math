import OAI.MeasureTheory.Falconer.Estimates.DyadicFailedTests
import OAI.MeasureTheory.Falconer.Angular.IneligibleCapTerms
import OAI.MeasureTheory.Falconer.Estimates.LocalizationSum

namespace OAI

/-!
# Localization of the full original dyadic graph expansion

The discarded-term estimate is derived from the actual three geometric
tests. Ineligible original cell--cap terms vanish. Every remaining error
is estimated only after its complete angular and radial integration.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap
attribute [local instance] Classical.propDecidable

theorem dyadic_localization_error
    (hpublished : PublishedGnomonicSurface) (n m : ℕ) (hn : 1 ≤ n)
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ (Q₁ Q₂ : DyadicCube (n+2)), 0 < Q₁.side → Q₂.side = Q₁.side →
      ∀ (μ ν : Measure (Space (n+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (j : ℕ) (R : ℝ), 1 ≤ R → ∀ (v τ δ H B D : ℝ), 0 < τ → 0 < δ → δ ≤ 1/2 →
      0 ≤ H → 0 ≤ B → 1 ≤ D → δ⁻¹ ≤ D →
      Real.sqrt (n+2 : ℕ)*Q₁.side ≤ (τ/4)*D →
      2*Real.sqrt (n+2 : ℕ)*(Q₁.side/(2 : ℝ)^j)+8*δ*(Real.sqrt (n+2 : ℕ)*Q₁.side) ≤ τ/4 →
      4*Real.pi*R^α ≤ (2 : ℝ)^v*τ →
      ∀ (M₁ M₂ : ℝ), 0 < M₁ → 0 < M₂ →
      ∀ {κ : Type*} (K : Finset κ) (w : κ → Sphere (n+2)) (η : κ → Sphere (n+2) → ℝ),
      (∀ k ∈ K, ChartCapControl m (η k) (w k : Space (n+2)) δ H) →
      (∀ k ∈ K, ∀ z, 0 ≤ η k z) →
      ∀ (b c : Space (n+2) → Sphere (n+2) → ℂ),
      ChartSymbolControl m b B D → ChartSymbolControl m c B D →
      ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
      let S := Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j
      let G := fun k : κ × κ => eligibleDyadicEdge Q₁ Q₂
        (Q₁.eligiblePaths μ j (η k.1) b) (Q₂.eligiblePaths ν j (η k.2) c)
        (w k.1) (w k.2) τ
      let F := fun k : κ × κ => dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c (η k.1) (η k.2)
      ‖(∫ z, ∑ k ∈ K ×ˢ K, ∑ row ∈ S, ∑ col ∈ S, F k row col z ∂angularProductMeasure (n+2) v Ψ) -
        (∫ z, ∑ k ∈ K ×ˢ K, ∑ row ∈ S, ∑ col ∈ S,
          if G k row col then F k row col z else 0 ∂angularProductMeasure (n+2) v Ψ)‖ ≤
        (K.card : ℝ)^2*(S.card : ℝ)^2 *
        (|(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
          (A*(4^m*H*B*B)*(B*B)*(sphereMeasure (n+2)).real univ) *
            (16*D/((2 : ℝ)^v*τ))^m*(4*W) +
        |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
          ((B*B)*(B*B)*C*((sphereMeasure (n+2)).real univ)^2*R^(-T))) := by
  obtain ⟨A,C,hA,hC,hfailed⟩ := dyadic_failed_tests_bound hpublished n m hn φ Ψ
    hφ hΨ hpos hzero hW hΨW hsupp hα T
  refine ⟨A,C,hA,hC,?_⟩
  intro Q₁ Q₂ hQ hside μ ν _ _ j R hR v τ δ H B D hτ hδ hδsmall
    hH hB hD hδD hnorm herr hfreq M₁ M₂ hM₁ hM₂ κ K w η hcap hη b c hb hc _
  dsimp only
  let S := Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j
  let G := fun k : κ × κ => eligibleDyadicEdge Q₁ Q₂
    (Q₁.eligiblePaths μ j (η k.1) b) (Q₂.eligiblePaths ν j (η k.2) c)
    (w k.1) (w k.2) τ
  let F := fun k : κ × κ => dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c (η k.1) (η k.2)
  let ε := |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
    (A*(4^m*H*B*B)*(B*B)*(sphereMeasure (n+2)).real univ) *
      (16*D/((2 : ℝ)^v*τ))^m*(4*W) +
    |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
      ((B*B)*(B*B)*C*((sphereMeasure (n+2)).real univ)^2*R^(-T))
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hi (k : κ × κ) (hk : k ∈ K ×ˢ K) (row : _) (_hr : row ∈ S)
      (col : _) (_hc : col ∈ S) : Integrable (F k row col) (angularProductMeasure (n+2) v Ψ) := by
    obtain ⟨hk₁,hk₂⟩ := Finset.mem_product.mp hk
    exact dyadicCapIntegrand_integrable Q₁ Q₂ μ ν M₁ M₂ v Ψ hM₁ hM₂ b c
      hb.measurable hc.measurable (η k.1) (η k.2) (hcap k.1 hk₁).measurable
      (hcap k.2 hk₂).measurable (hcap k.1 hk₁).bound (hcap k.2 hk₂).bound
      hB hb.bound hc.bound row col
  have he (k : κ × κ) (hk : k ∈ K ×ˢ K) (row : _) (hr : row ∈ S)
      (col : _) (hcol : col ∈ S) (hbad : ¬G k row col) :
      ‖∫ z, F k row col z ∂angularProductMeasure (n+2) v Ψ‖ ≤ ε := by
    obtain ⟨hk₁,hk₂⟩ := Finset.mem_product.mp hk
    have hη₁ := hcap k.1 hk₁
    have hη₂ := hcap k.2 hk₂
    have hηB₁ : ∀ z, η k.1 z ≤ 1 := fun z => (le_abs_self _).trans (hη₁.bound z)
    have hηB₂ : ∀ z, η k.2 z ≤ 1 := fun z => (le_abs_self _).trans (hη₂.bound z)
    by_cases hrow : row ∈ Q₁.eligiblePaths μ j (η k.1) b ×ˢ Q₂.eligiblePaths ν j (η k.2) c
    · by_cases hcol' : col ∈ Q₁.eligiblePaths μ j (η k.1) b ×ˢ Q₂.eligiblePaths ν j (η k.2) c
      · have hg : ¬retainedDyadicEdge Q₁ Q₂ (w k.1) (w k.2) τ row col :=
          fun h => hbad ⟨hrow,hcol',h⟩
        have hlen₁ (p : _) (hp : p ∈ Q₁.occupiedPaths μ j) : p.length = j :=
          (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1
        have hlen₂ (p : _) (hp : p ∈ Q₂.occupiedPaths ν j) : p.length = j :=
          (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1
        dsimp only [F]
        rw [integral_dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ v Ψ hM₁ hM₂ b c
          hb.measurable hc.measurable (η k.1) (η k.2) hη₁.measurable hη₂.measurable
          hη₁.bound hη₂.bound hB hb.bound hc.bound]
        exact hfailed Q₁ Q₂ hQ hside μ ν j row col
          (hlen₁ _ (Finset.mem_product.mp hr).1) (hlen₁ _ (Finset.mem_product.mp hcol).1)
          (hlen₂ _ (Finset.mem_product.mp hr).2) (hlen₂ _ (Finset.mem_product.mp hcol).2)
          R hR v τ δ H B D hτ hδ hδsmall hH hB hD hδD hnorm herr hfreq
          M₁ M₂ hM₁ hM₂ (w k.1) (w k.2) (η k.1) (η k.2) hη₁ hη₂ b c hb hc hg
      · have hz := dyadicCapIntegrand_col_ineligible Q₁ Q₂ μ ν j M₁ M₂ v Ψ b c
          hb.measurable hc.measurable (η k.1) (η k.2) hη₁.measurable hη₂.measurable
          (hη k.1 hk₁) (hη k.2 hk₂) hηB₁ hηB₂ hB hb.bound hc.bound row col hcol hcol'
        rw [integral_congr_ae hz]
        simpa only [Pi.zero_apply,integral_zero,norm_zero] using hε
    · have hz := dyadicCapIntegrand_row_ineligible Q₁ Q₂ μ ν j M₁ M₂ v Ψ b c
        hb.measurable hc.measurable (η k.1) (η k.2) hη₁.measurable hη₂.measurable
        (hη k.1 hk₁) (hη k.2 hk₂) hηB₁ hηB₂ hB hb.bound hc.bound row col hr hrow
      rw [integral_congr_ae hz]
      simpa only [Pi.zero_apply,integral_zero,norm_zero] using hε
  have hmain := integrated_discarded_sum_bound (angularProductMeasure (n+2) v Ψ)
    S (K ×ˢ K) G F hi hε he
  dsimp only [S,ε] at hmain
  convert hmain using 1
  simp only [Finset.card_product,Nat.cast_mul]
  ring

end Falconer

end OAI
