import OAI.Analysis.KadisonKastler.BilateralCocycle
import OAI.Analysis.KadisonKastler.CountableUnitaryL2

namespace OAI

/-! The bilateral cocycle acts isometrically on L2. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

def bilateralTranslateL2 (k : ℤ) (f : Lp K 2 (bilateralWalkLaw G)) : Lp K 2 (bilateralWalkLaw G) :=
  Lp.compMeasurePreserving (bilateralTranslate G k) (bilateralTranslate_measurePreserving G k) f

omit [InnerProductSpace ℂ K] [CompleteSpace K] [TopologicalSpace.SeparableSpace K] in
theorem bilateralTranslateL2_ae (k : ℤ) (f : Lp K 2 (bilateralWalkLaw G)) :
    bilateralTranslateL2 k f =ᵐ[bilateralWalkLaw G] f ∘ bilateralTranslate G k :=
  Lp.coeFn_compMeasurePreserving f (bilateralTranslate_measurePreserving G k)

omit [InnerProductSpace ℂ K] [CompleteSpace K] [TopologicalSpace.SeparableSpace K] in
theorem bilateralTranslateL2_norm (k : ℤ) (f : Lp K 2 (bilateralWalkLaw G)) :
    ‖bilateralTranslateL2 k f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (bilateralTranslate_measurePreserving G k)

omit [CompleteSpace K] [TopologicalSpace.SeparableSpace K] in
theorem bilateralTranslateL2_sub (k : ℤ) (f g : Lp K 2 (bilateralWalkLaw G)) :
    bilateralTranslateL2 k (f - g) = bilateralTranslateL2 k f - bilateralTranslateL2 k g := by
  exact map_sub (Lp.compMeasurePreservingₗᵢ ℂ (bilateralTranslate G k)
    (bilateralTranslate_measurePreserving G k)) f g

theorem bilateral_l2_transport (σ : G →* unitary (K →L[ℂ] K))
    (f : Lp K 2 (bilateralWalkLaw G))
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω)) (n : ℕ) :
    bilateralTranslateL2 n f =
      countableUnitaryL2 σ (bilateralIncrementProduct_measurable G n) f := by
  apply Lp.ext
  have hi := bilateral_transport_iterate σ ht n
  filter_upwards [bilateralTranslateL2_ae n f, hi,
    countableUnitaryL2_ae σ (bilateralIncrementProduct_measurable G n) f] with ω hx hy hz
  exact hx.trans (hy.trans hz.symm)

theorem bilateral_l2_approximation_transport (σ : G →* unitary (K →L[ℂ] K))
    (f g : Lp K 2 (bilateralWalkLaw G))
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω)) (n : ℕ) :
    ‖countableUnitaryL2 σ (bilateralIncrementProduct_measurable G n) g - bilateralTranslateL2 n g‖ ≤
      2 * ‖f - g‖ := by
  let U : Lp K 2 (bilateralWalkLaw G) → Lp K 2 (bilateralWalkLaw G) := countableUnitaryL2 σ (bilateralIncrementProduct_measurable G n)
  have he : U f = bilateralTranslateL2 n f := (bilateral_l2_transport σ f ht n).symm
  calc
    ‖U g - bilateralTranslateL2 n g‖ ≤ ‖U g - U f‖ + ‖U f - bilateralTranslateL2 n g‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖g - f‖ + ‖f - g‖ := by
      rw [← countableUnitaryL2_sub, countableUnitaryL2_norm, he,
        ← bilateralTranslateL2_sub, bilateralTranslateL2_norm]
    _ = 2 * ‖f - g‖ := by rw [norm_sub_rev g f]; ring

end

end KadisonKastler

end OAI
