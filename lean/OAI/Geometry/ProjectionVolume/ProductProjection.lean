import OAI.Geometry.ProjectionVolume.SimplexProjection

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Paper092

abbrev ProductFacetIndex := Option (Fin 10) ⊕ Option (Fin 10)

def productCoordinates (x : Euclidean 20) : ProductFacetIndex → ℝ
  | .inl a => simplexCoordinates (firstBlock x) a
  | .inr a => simplexCoordinates (secondBlock x) a

def productVelocity (u : Euclidean 20) : ProductFacetIndex → ℝ
  | .inl a => simplexVelocity (firstBlock u) a
  | .inr a => simplexVelocity (secondBlock u) a

theorem productCoordinates_add_smul (x u : Euclidean 20) (t : ℝ) (a : ProductFacetIndex) :
    productCoordinates (x + t • u) a = productCoordinates x a + t * productVelocity u a := by
  cases a with
  | inl a => exact simplexCoordinates_add_smul (firstBlock x) (firstBlock u) t a
  | inr a => exact simplexCoordinates_add_smul (secondBlock x) (secondBlock u) t a

theorem mem_productWitness_iff_coordinates (x : Euclidean 20) :
    x ∈ productWitness ↔ ∀ a, 0 ≤ productCoordinates x a := by
  change (firstBlock x ∈ standardSimplex 10 ∧ secondBlock x ∈ standardSimplex 10) ↔ _
  rw [mem_standardSimplex_iff_coordinates, mem_standardSimplex_iff_coordinates]
  constructor
  · rintro ⟨h1, h2⟩ a
    cases a with
    | inl a => exact h1 a
    | inr a => exact h2 a
  · intro h
    exact ⟨fun a => h (.inl a), fun a => h (.inr a)⟩

theorem productVelocity_neg_exists (u : Euclidean 20) (hu : u ≠ 0) :
    ∃ a, productVelocity u a < 0 := by
  by_cases h1 : firstBlock u = 0
  · have h2 : secondBlock u ≠ 0 := by
      intro h2
      apply hu
      apply splitBlocks.injective
      change (firstBlock u, secondBlock u) = (firstBlock 0, secondBlock 0)
      rw [h1, h2]
      rfl
    obtain ⟨a, ha⟩ := simplexVelocity_neg_exists (secondBlock u) h2
    exact ⟨.inr a, ha⟩
  · obtain ⟨a, ha⟩ := simplexVelocity_neg_exists (firstBlock u) h1
    exact ⟨.inl a, ha⟩

theorem exists_product_front_point (x u : Euclidean 20) (hu : u ≠ 0)
    (hx : ∀ a, 0 ≤ productCoordinates x a) :
    ∃ t : ℝ, 0 ≤ t ∧ (∀ a, 0 ≤ productCoordinates (x + t • u) a) ∧
      ∃ a, productVelocity u a < 0 ∧ productCoordinates (x + t • u) a = 0 := by
  obtain ⟨t, ht, hq, a, ha, hqa⟩ :=
    exists_step_to_boundary (productCoordinates x) (productVelocity u) hx
      (productVelocity_neg_exists u hu)
  refine ⟨t, ht, ?_, a, ha, ?_⟩
  · simpa only [productCoordinates_add_smul] using hq
  · simpa only [productCoordinates_add_smul] using hqa

theorem projection_injective_on_product_front (u x z : Euclidean 20)
    (hx : ∀ a, 0 ≤ productCoordinates x a) (hz : ∀ a, 0 ≤ productCoordinates z a)
    (hxf : ∃ a, productVelocity u a < 0 ∧ productCoordinates x a = 0)
    (hzf : ∃ a, productVelocity u a < 0 ∧ productCoordinates z a = 0)
    (hp : (normalHyperplane u).orthogonalProjectionOnto x =
      (normalHyperplane u).orthogonalProjectionOnto z) : x = z := by
  obtain ⟨t, rfl⟩ := (projection_eq_iff_parallel u x z).mp hp
  obtain ⟨a, ha, hxa⟩ := hxf
  obtain ⟨b, hb, hzb⟩ := hzf
  rw [productCoordinates_add_smul] at hxa
  have ht0 : 0 ≤ t := by
    by_contra ht
    have hprod := mul_pos_of_neg_of_neg (lt_of_not_ge ht) ha
    linarith [hz a]
  have ht1 : t ≤ 0 := by
    by_contra ht
    have hprod := mul_neg_of_pos_of_neg (lt_of_not_ge ht) hb
    have hxb := hx b
    rw [productCoordinates_add_smul, hzb] at hxb
    linarith
  simp [le_antisymm ht1 ht0]

def productFacet (a : ProductFacetIndex) : Set (Euclidean 20) :=
  {x | x ∈ productWitness ∧ productCoordinates x a = 0}

theorem product_projection_eq_front_cover (u : Euclidean 20) (hu : u ≠ 0) :
    (normalHyperplane u).orthogonalProjectionOnto '' productWitness =
      ⋃ a : {a : ProductFacetIndex // productVelocity u a < 0},
        (normalHyperplane u).orthogonalProjectionOnto '' productFacet a.val := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, _, hq, a, ha, hqa⟩ :=
      exists_product_front_point x u hu ((mem_productWitness_iff_coordinates x).mp hx)
    refine mem_iUnion.mpr ⟨⟨a, ha⟩, x + t • u, ?_, ?_⟩
    · exact ⟨(mem_productWitness_iff_coordinates _).mpr hq, hqa⟩
    · exact (projection_eq_iff_parallel u (x + t • u) x).mpr ⟨t, rfl⟩
  · intro hy
    obtain ⟨a, x, hx, hpx⟩ := mem_iUnion.mp hy
    exact ⟨x, hx.1, hpx⟩

theorem product_front_facets_projection_inter_eq (u : Euclidean 20)
    (a b : ProductFacetIndex) (ha : productVelocity u a < 0)
    (hb : productVelocity u b < 0) :
    ((normalHyperplane u).orthogonalProjectionOnto '' productFacet a) ∩
      ((normalHyperplane u).orthogonalProjectionOnto '' productFacet b) =
        (normalHyperplane u).orthogonalProjectionOnto '' (productFacet a ∩ productFacet b) := by
  apply le_antisymm
  · rintro y ⟨⟨x, hx, hpx⟩, ⟨z, hz, hpz⟩⟩
    have heq : x = z := projection_injective_on_product_front u x z
      ((mem_productWitness_iff_coordinates x).mp hx.1)
      ((mem_productWitness_iff_coordinates z).mp hz.1)
      ⟨a, ha, hx.2⟩ ⟨b, hb, hz.2⟩ (hpx.trans hpz.symm)
    subst z
    exact ⟨x, ⟨hx, hz⟩, hpx⟩
  · exact image_inter_subset _ _ _

def productCoordinateAffine : ProductFacetIndex → Euclidean 20 →ᵃ[ℝ] ℝ
  | .inl a => (simplexCoordinateAffine a).comp
      (((LinearMap.fst ℝ (Euclidean 10) (Euclidean 10)).comp splitBlocks.toLinearMap).toAffineMap)
  | .inr a => (simplexCoordinateAffine a).comp
      (((LinearMap.snd ℝ (Euclidean 10) (Euclidean 10)).comp splitBlocks.toLinearMap).toAffineMap)

theorem productCoordinateAffine_apply (a : ProductFacetIndex) (x : Euclidean 20) :
    productCoordinateAffine a x = productCoordinates x a := by
  cases a with
  | inl a => exact simplexCoordinateAffine_apply a (firstBlock x)
  | inr a => exact simplexCoordinateAffine_apply a (secondBlock x)

def productVertex (a b : Option (Fin 10)) : Euclidean 20 :=
  splitBlocks.symm (simplexVertex a, simplexVertex b)

theorem firstBlock_productVertex (a b : Option (Fin 10)) :
    firstBlock (productVertex a b) = simplexVertex a := by
  change (splitBlocks (splitBlocks.symm _)).1 = _
  simp

theorem secondBlock_productVertex (a b : Option (Fin 10)) :
    secondBlock (productVertex a b) = simplexVertex b := by
  change (splitBlocks (splitBlocks.symm _)).2 = _
  simp

theorem exists_product_coordinate_separator (a b : ProductFacetIndex) (hab : a ≠ b) :
    ∃ x : Euclidean 20, productCoordinates x a = 1 ∧ productCoordinates x b = 0 := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      refine ⟨productVertex a none, ?_⟩
      simp_all [productCoordinates, firstBlock_productVertex, simplexCoordinates_vertex]
    | inr b =>
      obtain ⟨c, hc⟩ := exists_ne b
      refine ⟨productVertex a c, ?_⟩
      simp [productCoordinates, firstBlock_productVertex, secondBlock_productVertex,
        simplexCoordinates_vertex, hc]
  | inr a =>
    cases b with
    | inl b =>
      obtain ⟨c, hc⟩ := exists_ne b
      refine ⟨productVertex c a, ?_⟩
      simp [productCoordinates, firstBlock_productVertex, secondBlock_productVertex,
        simplexCoordinates_vertex, hc]
    | inr b =>
      refine ⟨productVertex none a, ?_⟩
      simp_all [productCoordinates, secondBlock_productVertex, simplexCoordinates_vertex]

theorem product_facet_seam_projection_invariant (u x : Euclidean 20)
    (a b : ProductFacetIndex) :
    productVelocity u b * productCoordinates
        ((normalHyperplane u).orthogonalProjectionOnto x : Euclidean 20) a -
      productVelocity u a * productCoordinates
        ((normalHyperplane u).orthogonalProjectionOnto x : Euclidean 20) b =
      productVelocity u b * productCoordinates x a -
        productVelocity u a * productCoordinates x b := by
  obtain ⟨t, ht⟩ := (projection_eq_iff_parallel u x
    ((normalHyperplane u).orthogonalProjectionOnto x)).mp
      ((normalHyperplane u).orthogonalProjectionOnto_mem_subspace_eq_self
        ((normalHyperplane u).orthogonalProjectionOnto x)).symm
  conv_rhs => rw [ht, productCoordinates_add_smul, productCoordinates_add_smul]
  ring

theorem projected_product_facet_seam_null (u : Euclidean 20) (a b : ProductFacetIndex)
    (hab : a ≠ b) (hb : productVelocity u b ≠ 0) :
    volume {y : normalHyperplane u |
      productVelocity u b * productCoordinates y.val a -
        productVelocity u a * productCoordinates y.val b = 0} = 0 := by
  let f : normalHyperplane u →ᵃ[ℝ] ℝ :=
    productVelocity u b • ((productCoordinateAffine a).comp
      (normalHyperplane u).subtype.toAffineMap) -
    productVelocity u a • ((productCoordinateAffine b).comp
      (normalHyperplane u).subtype.toAffineMap)
  let S : AffineSubspace ℝ (normalHyperplane u) :=
    (affineSpan ℝ ({0} : Set ℝ)).comap f
  have hmem (y : normalHyperplane u) : y ∈ S ↔
      productVelocity u b * productCoordinates y.val a -
        productVelocity u a * productCoordinates y.val b = 0 := by
    simp [S, f, productCoordinateAffine_apply, smul_eq_mul]
  have hproper : S ≠ ⊤ := by
    intro htop
    obtain ⟨x, hxa, hxb⟩ := exists_product_coordinate_separator a b hab
    have hy : (normalHyperplane u).orthogonalProjectionOnto x ∈ S := by
      rw [htop]
      exact AffineSubspace.mem_top ℝ _ _
    have hz := (hmem _).mp hy
    rw [product_facet_seam_projection_invariant, hxa, hxb] at hz
    simp only [mul_one, mul_zero, sub_zero] at hz
    exact hb hz
  have hset : {y : normalHyperplane u |
      productVelocity u b * productCoordinates y.val a -
        productVelocity u a * productCoordinates y.val b = 0} = S := by
    ext y
    exact (hmem y).symm
  rw [hset]
  exact Measure.addHaar_affineSubspace volume S hproper

theorem projected_product_front_facets_aedisjoint (u : Euclidean 20)
    (a b : ProductFacetIndex) (hab : a ≠ b)
    (ha : productVelocity u a < 0) (hb : productVelocity u b < 0) :
    AEDisjoint volume
      ((normalHyperplane u).orthogonalProjectionOnto '' productFacet a)
      ((normalHyperplane u).orthogonalProjectionOnto '' productFacet b) := by
  rw [AEDisjoint, product_front_facets_projection_inter_eq u a b ha hb]
  apply measure_mono_null _ (projected_product_facet_seam_null u a b hab (ne_of_lt hb))
  rintro y ⟨x, hx, rfl⟩
  change productVelocity u b * productCoordinates
      ((normalHyperplane u).orthogonalProjectionOnto x : Euclidean 20) a -
    productVelocity u a * productCoordinates
      ((normalHyperplane u).orthogonalProjectionOnto x : Euclidean 20) b = 0
  rw [product_facet_seam_projection_invariant, hx.1.2, hx.2.2]
  simp

theorem productFacet_isCompact (a : ProductFacetIndex) : IsCompact (productFacet a) := by
  have hfun : (fun x : Euclidean 20 => productCoordinates x a) = productCoordinateAffine a := by
    funext x
    exact (productCoordinateAffine_apply a x).symm
  have hc : Continuous (fun x : Euclidean 20 => productCoordinates x a) := by
    rw [hfun]
    exact (productCoordinateAffine a).continuous_of_finiteDimensional
  exact productWitness_isCompact.inter_right (isClosed_eq hc continuous_const)

theorem projected_productFacet_isCompact (u : Euclidean 20) (a : ProductFacetIndex) :
    IsCompact ((normalHyperplane u).orthogonalProjectionOnto '' productFacet a) :=
  (productFacet_isCompact a).image (normalHyperplane u).orthogonalProjectionOnto.continuous

theorem projectionVolume_product_eq_front_sum (u : Euclidean 20) (hu : u ≠ 0) :
    projectionVolume productWitness u =
      ∑ a : {a : ProductFacetIndex // productVelocity u a < 0},
        volume ((normalHyperplane u).orthogonalProjectionOnto '' productFacet a.val) := by
  unfold projectionVolume
  rw [product_projection_eq_front_cover u hu]
  have hd : Pairwise (fun a b : {a : ProductFacetIndex // productVelocity u a < 0} =>
      AEDisjoint volume
        ((normalHyperplane u).orthogonalProjectionOnto '' productFacet a.val)
        ((normalHyperplane u).orthogonalProjectionOnto '' productFacet b.val)) := by
    intro a b hab
    exact projected_product_front_facets_aedisjoint u a.val b.val (Subtype.coe_injective.ne hab)
      a.property b.property
  rw [measure_iUnion₀ hd (fun a =>
    (projected_productFacet_isCompact u a.val).measurableSet.nullMeasurableSet)]
  exact tsum_fintype _

theorem brightness_product_eq_front_sum (u : Euclidean 20) (hu : u ≠ 0) :
    brightness productWitness u = ‖u‖ *
      ∑ a : {a : ProductFacetIndex // productVelocity u a < 0},
        (volume ((normalHyperplane u).orthogonalProjectionOnto '' productFacet a.val)).toReal := by
  unfold brightness
  rw [projectionVolume_product_eq_front_sum u hu, ENNReal.toReal_sum]
  intro a _
  exact (projected_productFacet_isCompact u a.val).measure_lt_top.ne

end Paper092

end

end OAI
