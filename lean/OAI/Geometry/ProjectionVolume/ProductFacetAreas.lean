import OAI.Geometry.ProjectionVolume.FacetAreas
import OAI.Geometry.ProjectionVolume.ProductVolumeGeneral
import OAI.Geometry.ProjectionVolume.ProductProjection
import Mathlib.Analysis.InnerProductSpace.ProdL2

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal Pointwise

namespace Paper092

def splitEuclideanProductL2 (r s : ℕ) :
    Euclidean (r + s) ≃ₗᵢ[ℝ] WithLp 2 (Euclidean r × Euclidean s) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin r ⊕ Fin s => ℝ))

theorem splitEuclideanProductL2_apply (r s : ℕ) (x : Euclidean (r + s)) :
    splitEuclideanProductL2 r s x = WithLp.toLp 2 (splitEuclideanProduct r s x) := rfl

def euclideanProductMap {r s t u : ℕ} (f : Euclidean r →ₗ[ℝ] Euclidean t)
    (g : Euclidean s →ₗ[ℝ] Euclidean u) :
    Euclidean (r + s) →ₗ[ℝ] Euclidean (t + u) :=
  (splitEuclideanProduct t u).symm.toLinearMap.comp
    ((f.prodMap g).comp (splitEuclideanProduct r s).toLinearMap)

theorem euclideanProductMap_apply {r s t u : ℕ} (f : Euclidean r →ₗ[ℝ] Euclidean t)
    (g : Euclidean s →ₗ[ℝ] Euclidean u) (x : Euclidean (r + s)) :
    euclideanProductMap f g x = (splitEuclideanProduct t u).symm
      (f (splitEuclideanProduct r s x).1, g (splitEuclideanProduct r s x).2) := rfl

theorem splitEuclideanProduct_inner (r s : ℕ) (x y : Euclidean (r + s)) :
    ⟪x, y⟫ = ⟪(splitEuclideanProduct r s x).1, (splitEuclideanProduct r s y).1⟫ +
      ⟪(splitEuclideanProduct r s x).2, (splitEuclideanProduct r s y).2⟫ := by
  symm
  exact (splitEuclideanProductL2 r s).inner_map_map x y

theorem euclideanProductMap_inner {r s t u : ℕ} (f : Euclidean r →ₗ[ℝ] Euclidean t)
    (g : Euclidean s →ₗ[ℝ] Euclidean u) (x y : Euclidean (r + s)) :
    ⟪euclideanProductMap f g x, euclideanProductMap f g y⟫ =
      ⟪f (splitEuclideanProduct r s x).1, f (splitEuclideanProduct r s y).1⟫ +
      ⟪g (splitEuclideanProduct r s x).2, g (splitEuclideanProduct r s y).2⟫ := by
  rw [splitEuclideanProduct_inner t u]
  simp only [euclideanProductMap_apply, ContinuousLinearEquiv.apply_symm_apply]

def productOrthonormalBasis (r s : ℕ) :
    OrthonormalBasis (Fin r ⊕ Fin s) ℝ (Euclidean (r + s)) :=
  ((EuclideanSpace.basisFun (Fin r) ℝ).prod (EuclideanSpace.basisFun (Fin s) ℝ)).map
    (splitEuclideanProductL2 r s).symm

theorem split_productOrthonormalBasis_inl (r s : ℕ) (i : Fin r) :
    splitEuclideanProduct r s (productOrthonormalBasis r s (.inl i)) =
      (EuclideanSpace.basisFun (Fin r) ℝ i, 0) := by
  have h := (splitEuclideanProductL2 r s).apply_symm_apply
    (((EuclideanSpace.basisFun (Fin r) ℝ).prod (EuclideanSpace.basisFun (Fin s) ℝ)) (.inl i))
  simpa only [productOrthonormalBasis, OrthonormalBasis.map_apply,
    OrthonormalBasis.prod_apply, Sum.elim_inl, Function.comp_apply,
    LinearMap.inl_apply, splitEuclideanProductL2_apply] using congrArg WithLp.ofLp h

theorem split_productOrthonormalBasis_inr (r s : ℕ) (i : Fin s) :
    splitEuclideanProduct r s (productOrthonormalBasis r s (.inr i)) =
      (0, EuclideanSpace.basisFun (Fin s) ℝ i) := by
  have h := (splitEuclideanProductL2 r s).apply_symm_apply
    (((EuclideanSpace.basisFun (Fin r) ℝ).prod (EuclideanSpace.basisFun (Fin s) ℝ)) (.inr i))
  simpa only [productOrthonormalBasis, OrthonormalBasis.map_apply,
    OrthonormalBasis.prod_apply, Sum.elim_inr, Function.comp_apply,
    LinearMap.inr_apply, splitEuclideanProductL2_apply] using congrArg WithLp.ofLp h

theorem euclideanProductMap_normDet {r s t u : ℕ} (f : Euclidean r →ₗ[ℝ] Euclidean t)
    (g : Euclidean s →ₗ[ℝ] Euclidean u) :
    (euclideanProductMap f g).normDet = f.normDet * g.normDet := by
  have hgram : Matrix.gram ℝ (fun i => euclideanProductMap f g (productOrthonormalBasis r s i)) =
      Matrix.fromBlocks
        (Matrix.gram ℝ (fun i => f (EuclideanSpace.basisFun (Fin r) ℝ i))) 0 0
        (Matrix.gram ℝ (fun i => g (EuclideanSpace.basisFun (Fin s) ℝ i))) := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.gram_apply, euclideanProductMap_inner,
        split_productOrthonormalBasis_inl, split_productOrthonormalBasis_inr]
  have h := (euclideanProductMap f g).normDet_sq_eq_det_gram (productOrthonormalBasis r s)
  have hf := f.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin r) ℝ)
  have hg := g.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin s) ℝ)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h hf hg
  rw [hgram, Matrix.det_fromBlocks_zero₂₁, ← hf, ← hg] at h
  have hn := (euclideanProductMap f g).normDet_nonneg
  have hp := mul_nonneg f.normDet_nonneg g.normDet_nonneg
  nlinarith

theorem euclideanProductMap_image {r s t u : ℕ} (f : Euclidean r →ₗ[ℝ] Euclidean t)
    (g : Euclidean s →ₗ[ℝ] Euclidean u) (A : Set (Euclidean r)) (B : Set (Euclidean s)) :
    euclideanProductMap f g '' (splitEuclideanProduct r s ⁻¹' (A ×ˢ B)) =
      splitEuclideanProduct t u ⁻¹' ((f '' A) ×ˢ (g '' B)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (splitEuclideanProduct t u (euclideanProductMap f g x)).1 ∈ f '' A ∧
      (splitEuclideanProduct t u (euclideanProductMap f g x)).2 ∈ g '' B
    rw [euclideanProductMap_apply, ContinuousLinearEquiv.apply_symm_apply]
    exact ⟨⟨_, hx.1, rfl⟩, ⟨_, hx.2, rfl⟩⟩
  · rintro ⟨⟨a, ha, hea⟩, ⟨b, hb, heb⟩⟩
    refine ⟨(splitEuclideanProduct r s).symm (a, b), ?_, ?_⟩
    · simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply,
        Set.mem_prod] using And.intro ha hb
    · apply (splitEuclideanProduct t u).injective
      simp only [euclideanProductMap_apply, ContinuousLinearEquiv.apply_symm_apply,
        hea, heb, Prod.mk.eta]

theorem euclideanProductMap_image_area {r s t u : ℕ}
    (f : Euclidean r →ₗ[ℝ] Euclidean t) (g : Euclidean s →ₗ[ℝ] Euclidean u)
    (A : Set (Euclidean r)) (B : Set (Euclidean s))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μHE[r + s] (splitEuclideanProduct t u ⁻¹' ((f '' A) ×ˢ (g '' B))) =
      ENNReal.ofReal (f.normDet * g.normDet) * (volume A * volume B) := by
  have h := (euclideanProductMap f g).euclideanHausdorffMeasure_image_eq_normDet_mul_volume
    (splitEuclideanProduct r s ⁻¹' (A ×ˢ B))
  simpa only [finrank_euclideanSpace_fin, euclideanProductMap_image,
    euclideanProductMap_normDet, splitEuclideanProduct_volume r s A B hA hB] using h

theorem splitEuclideanProduct_preimage_vadd {r s : ℕ}
    (a : Euclidean r) (b : Euclidean s) (A : Set (Euclidean r)) (B : Set (Euclidean s)) :
    splitEuclideanProduct r s ⁻¹' ((a +ᵥ A) ×ˢ (b +ᵥ B)) =
      (splitEuclideanProduct r s).symm (a, b) +ᵥ
        (splitEuclideanProduct r s ⁻¹' (A ×ˢ B)) := by
  ext x
  constructor
  · rintro ⟨⟨a', ha, hea⟩, ⟨b', hb, heb⟩⟩
    refine ⟨(splitEuclideanProduct r s).symm (a', b'), ?_, ?_⟩
    · simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply,
        Set.mem_prod] using And.intro ha hb
    · apply (splitEuclideanProduct r s).injective
      simp only [vadd_eq_add, map_add, ContinuousLinearEquiv.apply_symm_apply]
      exact Prod.ext hea heb
  · rintro ⟨y, hy, rfl⟩
    change (splitEuclideanProduct r s ((splitEuclideanProduct r s).symm (a, b) + y)).1 ∈
        a +ᵥ A ∧
      (splitEuclideanProduct r s ((splitEuclideanProduct r s).symm (a, b) + y)).2 ∈ b +ᵥ B
    simp only [map_add, ContinuousLinearEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add]
    exact ⟨⟨_, hy.1, rfl⟩, ⟨_, hy.2, rfl⟩⟩

theorem simplexFacet_diagonal_eq_vadd (n : ℕ) (i : Fin (n + 1)) :
    simplexFacet (n + 1) none = EuclideanSpace.single i (1 : ℝ) +ᵥ
      (facetEmbedding n i (-1) '' standardSimplex n) := by
  rw [← diagonalFacetChart_image n i]
  change diagonalFacetChart n i '' standardSimplex n =
    (fun x => EuclideanSpace.single i (1 : ℝ) + x) ''
      (facetEmbedding n i (-1) '' standardSimplex n)
  rw [image_image]
  congr 1
  funext x
  exact (diagonalFacetChart_eq n i x).trans (add_comm _ _)

theorem simplexProduct_coordinate_facet_area_left (r s : ℕ) (i : Fin (r + 1)) :
    μHE[r + s] (splitEuclideanProduct (r + 1) s ⁻¹'
      (simplexFacet (r + 1) (some i) ×ˢ standardSimplex s)) =
      ENNReal.ofReal ((1 / (Nat.factorial r : ℝ)) * (1 / (Nat.factorial s : ℝ))) := by
  have h := euclideanProductMap_image_area (facetEmbedding r i 0)
    (LinearMap.id : Euclidean s →ₗ[ℝ] Euclidean s)
    (standardSimplex r) (standardSimplex s)
    (standardSimplex_isCompact r).measurableSet (standardSimplex_isCompact s).measurableSet
  simpa only [facetEmbedding_zero_image, LinearMap.id_coe, Set.image_id,
    facetEmbedding_normDet_zero, LinearMap.normDet_id, one_mul, ENNReal.ofReal_one,
    standardSimplex_volume, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (Nat.factorial r : ℝ))]
    using h

theorem simplexProduct_coordinate_facet_area_right (r s : ℕ) (i : Fin (s + 1)) :
    μHE[r + s] (splitEuclideanProduct r (s + 1) ⁻¹'
      (standardSimplex r ×ˢ simplexFacet (s + 1) (some i))) =
      ENNReal.ofReal ((1 / (Nat.factorial r : ℝ)) * (1 / (Nat.factorial s : ℝ))) := by
  have h := euclideanProductMap_image_area
    (LinearMap.id : Euclidean r →ₗ[ℝ] Euclidean r) (facetEmbedding s i 0)
    (standardSimplex r) (standardSimplex s)
    (standardSimplex_isCompact r).measurableSet (standardSimplex_isCompact s).measurableSet
  simpa only [facetEmbedding_zero_image, LinearMap.id_coe, Set.image_id,
    facetEmbedding_normDet_zero, LinearMap.normDet_id, one_mul, ENNReal.ofReal_one,
    standardSimplex_volume, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (Nat.factorial r : ℝ))]
    using h

theorem simplexProduct_diagonal_facet_area_left (r s : ℕ) :
    μHE[r + s] (splitEuclideanProduct (r + 1) s ⁻¹'
      (simplexFacet (r + 1) none ×ˢ standardSimplex s)) =
      ENNReal.ofReal (Real.sqrt (r + 1) *
        ((1 / (Nat.factorial r : ℝ)) * (1 / (Nat.factorial s : ℝ)))) := by
  let i : Fin (r + 1) := Fin.last r
  rw [simplexFacet_diagonal_eq_vadd r i]
  rw [← zero_vadd (Euclidean s) (standardSimplex s)]
  rw [splitEuclideanProduct_preimage_vadd, measure_vadd]
  have h := euclideanProductMap_image_area (facetEmbedding r i (-1))
    (LinearMap.id : Euclidean s →ₗ[ℝ] Euclidean s)
    (standardSimplex r) (standardSimplex s)
    (standardSimplex_isCompact r).measurableSet (standardSimplex_isCompact s).measurableSet
  simpa only [LinearMap.id_coe, Set.image_id, facetEmbedding_normDet_neg_one,
    LinearMap.normDet_id, mul_one, standardSimplex_volume,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (Nat.factorial r : ℝ)),
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] using h

theorem simplexProduct_diagonal_facet_area_right (r s : ℕ) :
    μHE[r + s] (splitEuclideanProduct r (s + 1) ⁻¹'
      (standardSimplex r ×ˢ simplexFacet (s + 1) none)) =
      ENNReal.ofReal (Real.sqrt (s + 1) *
        ((1 / (Nat.factorial r : ℝ)) * (1 / (Nat.factorial s : ℝ)))) := by
  let i : Fin (s + 1) := Fin.last s
  rw [simplexFacet_diagonal_eq_vadd s i]
  rw [← zero_vadd (Euclidean r) (standardSimplex r)]
  rw [splitEuclideanProduct_preimage_vadd, measure_vadd]
  have h := euclideanProductMap_image_area
    (LinearMap.id : Euclidean r →ₗ[ℝ] Euclidean r) (facetEmbedding s i (-1))
    (standardSimplex r) (standardSimplex s)
    (standardSimplex_isCompact r).measurableSet (standardSimplex_isCompact s).measurableSet
  simpa only [LinearMap.id_coe, Set.image_id, facetEmbedding_normDet_neg_one,
    LinearMap.normDet_id, one_mul, standardSimplex_volume,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (Nat.factorial r : ℝ)),
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] using h

end Paper092

end

end OAI
