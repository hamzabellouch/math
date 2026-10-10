import OAI.Geometry.ProjectionBody.ProductFacets
import OAI.Geometry.ProjectionBody.SimplexFacetCharts
import OAI.Geometry.Zonotope.Product

namespace OAI

/-! Explicit nineteen-dimensional affine charts on the twenty-two product facets. -/
noncomputable section
open Set

namespace ProjectionCounterexample

/-- The product-simplex parameter domain for a facet in the selected block. -/
def productFacetDomain : Bool → Set (E 19)
  | false => (@EuclideanSpace.finAddEquivProd ℝ _ 9 10) ⁻¹'
      (simplex 9 ×ˢ simplex 10)
  | true => (@EuclideanSpace.finAddEquivProd ℝ _ 10 9) ⁻¹'
      (simplex 10 ×ˢ simplex 9)

/-- Linear part of the affine product facet chart. -/
def productFacetLinear : Bool × Option (Fin 10) → E 19 →ₗ[ℝ] E 20
  | (false, i) => (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).symm.toLinearMap.comp
      (((simplexFacetLinear 9 i).prodMap (LinearMap.id : E 10 →ₗ[ℝ] E 10)).comp
        (@EuclideanSpace.finAddEquivProd ℝ _ 9 10).toLinearMap)
  | (true, i) => (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).symm.toLinearMap.comp
      (((LinearMap.id : E 10 →ₗ[ℝ] E 10).prodMap (simplexFacetLinear 9 i)).comp
        (@EuclideanSpace.finAddEquivProd ℝ _ 10 9).toLinearMap)

def productFacetCenter : Bool × Option (Fin 10) → E 20
  | (false, i) => (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).symm (simplexFacetCenter 9 i, 0)
  | (true, i) => (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).symm (0, simplexFacetCenter 9 i)

@[simp] lemma firstBlock_finAdd (x : E 20) :
    ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) x).1 = firstBlock x := rfl

@[simp] lemma secondBlock_finAdd (x : E 20) :
    ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) x).2 = secondBlock x := rfl

lemma productFacetChart_first (i : Option (Fin 10)) (x : E 19) :
    (@EuclideanSpace.finAddEquivProd ℝ _ 10 10)
      (productFacetCenter (false, i) + productFacetLinear (false, i) x) =
      (simplexFacetCenter 9 i + simplexFacetLinear 9 i
        ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10) x).1,
       ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10) x).2) := by
  simp [productFacetCenter, productFacetLinear, map_add, LinearMap.prodMap_apply]
  rfl

lemma productFacetChart_second (i : Option (Fin 10)) (x : E 19) :
    (@EuclideanSpace.finAddEquivProd ℝ _ 10 10)
      (productFacetCenter (true, i) + productFacetLinear (true, i) x) =
      (((@EuclideanSpace.finAddEquivProd ℝ _ 10 9) x).1,
       simplexFacetCenter 9 i + simplexFacetLinear 9 i
        ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9) x).2) := by
  simp [productFacetCenter, productFacetLinear, map_add, LinearMap.prodMap_apply]
  rfl

/-- Each product facet is exactly the image of the appropriate product simplex. -/
theorem product_facet_eq_affine_image (i : Bool × Option (Fin 10)) :
    boundingFace productFunctional productLevel i =
      (fun x => productFacetCenter i + productFacetLinear i x) '' productFacetDomain i.1 := by
  rcases i with ⟨b, i⟩
  cases b
  · rw [product_boundingFace_first, simplex_facet_eq_affine_image]
    ext x
    constructor
    · rintro ⟨⟨a, ha, heq⟩, hb⟩
      let z : E 19 := (@EuclideanSpace.finAddEquivProd ℝ _ 9 10).symm (a, secondBlock x)
      refine ⟨z, ?_, ?_⟩
      · change (@EuclideanSpace.finAddEquivProd ℝ _ 9 10) z ∈ simplex 9 ×ˢ simplex 10
        simpa only [z, ContinuousLinearEquiv.apply_symm_apply, Set.mem_prod] using And.intro ha hb
      · apply (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).injective
        rw [productFacetChart_first]
        simp only [z, ContinuousLinearEquiv.apply_symm_apply]
        apply Prod.ext
        · exact heq
        · rfl
    · rintro ⟨z, hz, rfl⟩
      have heq := productFacetChart_first i z
      have hfirst := congrArg Prod.fst heq
      have hsecond := congrArg Prod.snd heq
      rw [firstBlock_finAdd] at hfirst
      rw [secondBlock_finAdd] at hsecond
      change ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10) z).1 ∈ simplex 9 ∧
        ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10) z).2 ∈ simplex 10 at hz
      refine ⟨⟨_, hz.1, hfirst.symm⟩, ?_⟩
      rw [hsecond]
      exact hz.2
  · rw [product_boundingFace_second, simplex_facet_eq_affine_image]
    ext x
    constructor
    · rintro ⟨ha, ⟨b, hb, heq⟩⟩
      let z : E 19 := (@EuclideanSpace.finAddEquivProd ℝ _ 10 9).symm (firstBlock x, b)
      refine ⟨z, ?_, ?_⟩
      · change (@EuclideanSpace.finAddEquivProd ℝ _ 10 9) z ∈ simplex 10 ×ˢ simplex 9
        simpa only [z, ContinuousLinearEquiv.apply_symm_apply, Set.mem_prod] using And.intro ha hb
      · apply (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).injective
        rw [productFacetChart_second]
        simp only [z, ContinuousLinearEquiv.apply_symm_apply]
        apply Prod.ext
        · rfl
        · exact heq
    · rintro ⟨z, hz, rfl⟩
      have heq := productFacetChart_second i z
      have hfirst := congrArg Prod.fst heq
      have hsecond := congrArg Prod.snd heq
      rw [firstBlock_finAdd] at hfirst
      rw [secondBlock_finAdd] at hsecond
      change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9) z).1 ∈ simplex 10 ∧
        ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9) z).2 ∈ simplex 9 at hz
      refine ⟨?_, ⟨_, hz.2, hsecond.symm⟩⟩
      rw [hfirst]
      exact hz.1

@[simp] lemma productFacetLinear_first_first (i : Option (Fin 10)) (z : E 9) (w : E 10) :
    firstBlock (productFacetLinear (false, i)
      ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10).symm (z, w))) = simplexFacetLinear 9 i z := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (false, i) _)).1 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]

@[simp] lemma productFacetLinear_first_second (i : Option (Fin 10)) (z : E 9) (w : E 10) :
    secondBlock (productFacetLinear (false, i)
      ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10).symm (z, w))) = w := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (false, i) _)).2 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]

@[simp] lemma productFacetLinear_second_first (i : Option (Fin 10)) (z : E 10) (w : E 9) :
    firstBlock (productFacetLinear (true, i)
      ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9).symm (z, w))) = z := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (true, i) _)).1 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]

@[simp] lemma productFacetLinear_second_second (i : Option (Fin 10)) (z : E 10) (w : E 9) :
    secondBlock (productFacetLinear (true, i)
      ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9).symm (z, w))) = simplexFacetLinear 9 i w := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (true, i) _)).2 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]

private lemma simplexFunctional_ten_ne_zero (j : Option (Fin 10)) :
    simplexFunctional 10 j ≠ 0 := by
  intro heq
  cases j with
  | none =>
    have h := LinearMap.congr_fun heq (EuclideanSpace.single (0 : Fin 10) 1)
    simp at h
  | some j =>
    have h := LinearMap.congr_fun heq (EuclideanSpace.single j 1)
    simp at h

/-- Every other defining hyperplane cuts a product facet chart transversely. -/
theorem product_facet_transverse (i j : Bool × Option (Fin 10)) (hij : i ≠ j) :
    (productFunctional j).comp (productFacetLinear i) ≠ 0 := by
  rcases i with ⟨bi, i⟩
  rcases j with ⟨bj, j⟩
  intro heq
  cases bi <;> cases bj
  · apply simplex_facet_transverse (n := 9) (by decide) i j
      (fun h => hij (congrArg (fun k => (false, k)) h))
    ext z
    have h := LinearMap.congr_fun heq
      ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10).symm (z, 0))
    simpa only [LinearMap.comp_apply, productFunctional_first,
      productFacetLinear_first_first, LinearMap.zero_apply] using h
  · apply simplexFunctional_ten_ne_zero j
    ext w
    have h := LinearMap.congr_fun heq
      ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10).symm (0, w))
    simpa only [LinearMap.comp_apply, productFunctional_second,
      productFacetLinear_first_second, LinearMap.zero_apply] using h
  · apply simplexFunctional_ten_ne_zero j
    ext z
    have h := LinearMap.congr_fun heq
      ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9).symm (z, 0))
    simpa only [LinearMap.comp_apply, productFunctional_first,
      productFacetLinear_second_first, LinearMap.zero_apply] using h
  · apply simplex_facet_transverse (n := 9) (by decide) i j
      (fun h => hij (congrArg (fun k => (true, k)) h))
    ext w
    have h := LinearMap.congr_fun heq
      ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9).symm (0, w))
    simpa only [LinearMap.comp_apply, productFunctional_second,
      productFacetLinear_second_second, LinearMap.zero_apply] using h

end ProjectionCounterexample

end

end OAI
