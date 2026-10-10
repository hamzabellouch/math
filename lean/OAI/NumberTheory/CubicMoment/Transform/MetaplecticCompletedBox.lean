import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrimalFinite

namespace OAI

/-! A compactly supported completed sum can be written over a fixed
finite box of primary pairs. This box is independent of the height. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_pair_box_image (F : ℝ) :
    (((primaryElementBall F).subtype primary).product
      ((primaryElementBall F).subtype primary)).image metaplecticPrimaryPair =
        (primaryElementBall F).product (primaryElementBall F) := by
  ext du
  constructor
  · intro h
    obtain ⟨ev,hev,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hd,hu⟩ := Finset.mem_product.mp hev
    exact Finset.mem_product.mpr ⟨Finset.mem_subtype.mp hd,Finset.mem_subtype.mp hu⟩
  · intro h
    obtain ⟨hd,hu⟩ := Finset.mem_product.mp h
    refine Finset.mem_image.mpr ⟨(⟨du.1,(mem_primaryElementBall.mp hd).1⟩,
      ⟨du.2,(mem_primaryElementBall.mp hu).1⟩),?_,rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_subtype.mpr hd,Finset.mem_subtype.mpr hu⟩

theorem metaplecticHeightCompleted_box (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {X B F : ℝ} (hX : 0 < X) (hBF : B*X ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    metaplecticHeightCompleted r ℓ W X t =
      ∑ c ∈ primaryElementBall F, ∑ u ∈ primaryElementBall F,
        metaplecticPrimalCoefficient r ℓ W X (c,u)*
          mellinPhase t (norm (metaplecticCubeProduct (c,u))) := by
  let P := ((primaryElementBall F).subtype primary).product
    ((primaryElementBall F).subtype primary)
  have he : metaplecticHeightCompleted r ℓ W X t =
      ∑ du ∈ P, metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du)*
        mellinPhase t (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))) := by
    change (∑' du : PrimaryArgument × PrimaryArgument,
      metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du)*
        mellinPhase t (norm (metaplecticCubeProduct (metaplecticPrimaryPair du)))) = _
    apply tsum_eq_sum
    intro du hdu
    have hc : metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du) = 0 := by
      by_contra hn
      have hs := metaplecticPrimalSupport_of_nonzero ℓ W hX hBF hW du hn
      exact hdu (Finset.mem_filter.mp hs).1
    rw [hc,zero_mul]
  rw [he,←Finset.sum_product']
  have himage := primary_pair_box_image F
  change P.image metaplecticPrimaryPair = primaryElementBall F ×ˢ primaryElementBall F at himage
  rw [←himage,Finset.sum_image]
  exact fun _ _ _ _ h => metaplecticPrimaryPair_injective h

end CubicFirstMoment

end

end OAI
