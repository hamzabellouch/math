import Mathlib
import OAI.GroupTheory.FiniteType.BinaryPrefixOperators

namespace OAI

noncomputable section
namespace ListChains
section

variable (G : Type*) [Group G] {C : Type*}

def shiftOrigin (f : G →* G) (σ : C → C) (δ : C → G) : ℕ → C → G
  | 0, _ => 1
  | k+1, c => δ (σ^[k] c) * f (shiftOrigin f σ δ k c)

def cosetShift (f : G →* G) (σ : C → C) (δ : C → G) :
    (C →₀ Chain G) →ₗ[ℤ] (C →₀ Chain G) :=
  cosetMap G σ (fun c x => δ c * f x)

lemma cosetShift_iterate (f : G →* G) (σ : C → C) (δ : C → G)
    (k : ℕ) (z : C →₀ Chain G) :
    (cosetShift G f σ δ : (C →₀ Chain G) → C →₀ Chain G)^[k] z =
      cosetMap G (σ^[k]) (fun c x => shiftOrigin G f σ δ k c * iterateHom G f k x) z := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero,shiftOrigin,iterateHom_zero,MonoidHom.id_apply,one_mul]
    change z = cosetMap G id (fun _ => id) z
    exact (cosetMap_id G z).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih]
    change cosetMap G σ (fun c x => δ c*f x) _ = _
    rw [cosetMap_comp]
    have hs : σ ∘ σ^[k] = σ^[k+1] := by
      funext c
      exact (Function.iterate_succ_apply' σ k c).symm
    rw [hs]
    apply congrArg (fun ψ : C → G → G => cosetMap G (σ^[k+1]) ψ z)
    funext c x
    simp only [Function.comp_apply,shiftOrigin,iterateHom,MonoidHom.comp_apply,map_mul,mul_assoc]

lemma cosetShift_mem_controlled (f : G →* G) (σ : C → C) (δ : C → G)
    {A : Set G} {z : C →₀ Chain G}
    (hz : z ∈ cosetModule G (controlledModule G A)) :
    cosetShift G f σ δ z ∈ cosetModule G (controlledModule G (f '' A)) := by
  apply cosetMap_mem G _ _ _ _ _ hz
  intro c x hx
  have h := leftTranslate_mem_controlled G (δ c) (mapChain_mem_controlled G G f hx)
  simpa only [mapChain_comp,Function.comp_def] using h

lemma cosetShift_mem_degree (f : G →* G) (σ : C → C) (δ : C → G)
    {n : ℕ} {z : C →₀ Chain G} (hz : z ∈ cosetModule G (degreeModule G n)) :
    cosetShift G f σ δ z ∈ cosetModule G (degreeModule G n) :=
  cosetMap_mem G _ _ _ _ (fun _ _ hx => mapChain_mem_degree G _ hx) hz

lemma cosetBoundary_shift (f : G →* G) (σ : C → C) (δ : C → G) (z : C →₀ Chain G) :
    cosetBoundary G (cosetShift G f σ δ z) =
      cosetShift G f σ δ (cosetBoundary G z) :=
  cosetBoundary_cosetMap G _ _ z

theorem UniformFillings.coset_products {f : G →* G} {n : ℕ}
    (hf : UniformFillings G f n) (hn : 0 < n)
    (σ : C → C) (δ : C → G) {I : Type*} (z : I → C →₀ Chain G)
    (hd : ∀ i, z i ∈ cosetModule G (degreeModule G n))
    (hc : ∀ i, cosetBoundary G (z i) = 0)
    {A : Set G} (hA : IsBound G A)
    (ha : ∀ i, z i ∈ cosetModule G (controlledModule G A)) :
    ∃ k : ℕ, ∃ B : Set G, IsBound G B ∧ ∃ w : I → C →₀ Chain G,
      (∀ i, w i ∈ cosetModule G (degreeModule G (n+1))) ∧
      (∀ i, w i ∈ cosetModule G (controlledModule G B)) ∧
      (∀ i, cosetBoundary G (w i) =
        (cosetShift G f σ δ : (C →₀ Chain G) → C →₀ Chain G)^[k] (z i)) := by
  classical
  obtain ⟨k,B,hB,v,hv⟩ := hf.translated_families G hn z hd
    (fun i c => congrArg (fun z : C →₀ Chain G => z c) (hc i)) hA ha
    (fun k _ c => shiftOrigin G f σ δ k c)
  let w (i : I) := mergeCosets G (σ^[k]) (v i)
  refine ⟨k,B,hB,w,?_,?_,?_⟩
  · intro i
    rw [show w i = cosetMap G (σ^[k]) (fun _ => id) (v i) by rw [← mergeCosets_eq]]
    exact cosetMap_mem G _ _ _ _ (fun _ _ hx => by simpa only [mapChain_id] using hx)
      (fun c => (hv i c).1)
  · intro i
    rw [show w i = cosetMap G (σ^[k]) (fun _ => id) (v i) by rw [← mergeCosets_eq]]
    exact cosetMap_mem G _ _ _ _ (fun _ _ hx => by simpa only [mapChain_id] using hx)
      (fun c => (hv i c).2.1)
  · intro i
    rw [cosetShift_iterate]
    change cosetBoundary G (mergeCosets G (σ^[k]) (v i)) = _
    rw [cosetBoundary_mergeCosets,mergeCosets_eq]
    have he : cosetBoundary G (v i) =
        cosetMap G id (fun c x => shiftOrigin G f σ δ k c * iterateHom G f k x) (z i) := by
      have hmap (c : C) :
          cosetMap G id (fun c x => shiftOrigin G f σ δ k c * iterateHom G f k x) (z i) c =
            mapChain G (fun x => shiftOrigin G f σ δ k c * iterateHom G f k x) (z i c) := by
        rw [cosetMap,Finsupp.lsum_apply,Finsupp.sum_apply]
        simp only [LinearMap.comp_apply,Finsupp.lsingle_apply,id_eq]
        rw [Finsupp.sum_eq_single c]
        · simp
        · intro d _ hdc
          simp [Finsupp.single_eq_of_ne (Ne.symm hdc)]
        · intro h
          simp only [map_zero,Finsupp.single_zero,Finsupp.zero_apply]
      ext c s
      exact congrArg (fun x : Chain G => x s) (by rw [cosetBoundary_apply,hmap];exact (hv i c).2.2)
    rw [he,cosetMap_comp]
    rfl

end

section

variable (G I C : Type*) [Group G]

abbrev ProductAmbient := I → C →₀ Chain G

def boundedProducts : Submodule ℤ (ProductAmbient G I C) where
  carrier := {z | ∃ A : Set G, IsBound G A ∧
    ∀ i, z i ∈ cosetModule G (controlledModule G A)}
  zero_mem' := by
    refine ⟨{1},⟨Set.finite_singleton 1,by simp,by intro a ha;simpa using ha⟩,?_⟩
    intro i
    exact Submodule.zero_mem _
  add_mem' := by
    rintro z w ⟨A,hA,hz⟩ ⟨B,hB,hw⟩
    refine ⟨A ∪ B,hA.union G hB,?_⟩
    intro i c
    exact Submodule.add_mem _
      (controlledModule_mono G Set.subset_union_left (hz i c))
      (controlledModule_mono G Set.subset_union_right (hw i c))
  smul_mem' := by
    rintro r z ⟨A,hA,hz⟩
    exact ⟨A,hA,fun i => Submodule.smul_mem _ r (hz i)⟩

def degreeProducts (n : ℕ) : Submodule ℤ (ProductAmbient G I C) where
  carrier := {z | ∀ i, z i ∈ cosetModule G (degreeModule G n)}
  zero_mem' := fun _ => Submodule.zero_mem _
  add_mem' := fun hz hw i => Submodule.add_mem _ (hz i) (hw i)
  smul_mem' := fun r _ hz i => Submodule.smul_mem _ r (hz i)

def productBoundary : ProductAmbient G I C →ₗ[ℤ] ProductAmbient G I C :=
  LinearMap.pi (fun i => (cosetBoundary G).comp (LinearMap.proj i))

omit [Group G] in
@[simp] lemma productBoundary_apply (z : ProductAmbient G I C) (i : I) :
    productBoundary G I C z i = cosetBoundary G (z i) := rfl

omit [Group G] in
@[simp] lemma productBoundary_squared (z : ProductAmbient G I C) :
    productBoundary G I C (productBoundary G I C z) = 0 := by
  funext i
  exact cosetBoundary_squared G (z i)

lemma productBoundary_mem_bounded {z : ProductAmbient G I C}
    (hz : z ∈ boundedProducts G I C) : productBoundary G I C z ∈ boundedProducts G I C := by
  obtain ⟨A,hA,hz⟩ := hz
  exact ⟨A,hA,fun i c => boundary_mem_controlledModule G (hz i c)⟩

omit [Group G] in
lemma productBoundary_mem_degree {n : ℕ} {z : ProductAmbient G I C}
    (hz : z ∈ degreeProducts G I C (n+1)) : productBoundary G I C z ∈ degreeProducts G I C n :=
  fun i c => boundary_mem_degreeModule G (hz i c)

def productChains (n : ℕ) : Submodule ℤ (ProductAmbient G I C) :=
  boundedProducts G I C ⊓ degreeProducts G I C n

def productCycles (n : ℕ) : Submodule ℤ (ProductAmbient G I C) :=
  productChains G I C n ⊓ LinearMap.ker (productBoundary G I C)

def productDifferential (n : ℕ) : productChains G I C (n+1) →ₗ[ℤ] productCycles G I C n where
  toFun w := ⟨productBoundary G I C w.val,
    ⟨⟨productBoundary_mem_bounded G I C w.property.1,
      productBoundary_mem_degree G I C w.property.2⟩,productBoundary_squared G I C w.val⟩⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

def productBoundaries (n : ℕ) : Submodule ℤ (productCycles G I C n) :=
  LinearMap.range (productDifferential G I C n)

abbrev BoundedProductHomology (n : ℕ) :=
  productCycles G I C n ⧸ productBoundaries G I C n

def productShift (f : G →* G) (σ : C → C) (δ : C → G) :
    ProductAmbient G I C →ₗ[ℤ] ProductAmbient G I C :=
  LinearMap.pi (fun i => (cosetShift G f σ δ).comp (LinearMap.proj i))

@[simp] lemma productShift_apply (f : G →* G) (σ : C → C) (δ : C → G)
    (z : ProductAmbient G I C) (i : I) :
    productShift G I C f σ δ z i = cosetShift G f σ δ (z i) := rfl

lemma productShift_iterate_apply (f : G →* G) (σ : C → C) (δ : C → G)
    (z : ProductAmbient G I C) (k : ℕ) (i : I) :
    (productShift G I C f σ δ : ProductAmbient G I C → ProductAmbient G I C)^[k] z i =
      (cosetShift G f σ δ : (C →₀ Chain G) → C →₀ Chain G)^[k] (z i) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply',productShift_apply,ih]

lemma productBoundary_shift (f : G →* G) (σ : C → C) (δ : C → G)
    (z : ProductAmbient G I C) :
    productBoundary G I C (productShift G I C f σ δ z) =
      productShift G I C f σ δ (productBoundary G I C z) := by
  funext i
  exact cosetBoundary_shift G f σ δ (z i)

lemma productShift_mem_chains (f : G →* G) (σ : C → C) (δ : C → G)
    {n : ℕ} {z : ProductAmbient G I C} (hz : z ∈ productChains G I C n) :
    productShift G I C f σ δ z ∈ productChains G I C n := by
  obtain ⟨⟨A,hA,hzA⟩,hzd⟩ := hz
  exact ⟨⟨f '' A,hA.image G f,fun i => cosetShift_mem_controlled G f σ δ (hzA i)⟩,
    fun i => cosetShift_mem_degree G f σ δ (hzd i)⟩

lemma productShift_mem_cycles (f : G →* G) (σ : C → C) (δ : C → G)
    {n : ℕ} {z : ProductAmbient G I C} (hz : z ∈ productCycles G I C n) :
    productShift G I C f σ δ z ∈ productCycles G I C n := by
  refine ⟨productShift_mem_chains G I C f σ δ hz.1,?_⟩
  change productBoundary G I C _ = 0
  rw [productBoundary_shift,show productBoundary G I C z = 0 from hz.2,map_zero]

def shiftChains (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    productChains G I C n →ₗ[ℤ] productChains G I C n :=
  (productShift G I C f σ δ).restrict (fun _ hz => productShift_mem_chains G I C f σ δ hz)

def shiftCycles (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    productCycles G I C n →ₗ[ℤ] productCycles G I C n :=
  (productShift G I C f σ δ).restrict (fun _ hz => productShift_mem_cycles G I C f σ δ hz)

lemma shiftCycles_iterate_val (f : G →* G) (σ : C → C) (δ : C → G) (n k : ℕ)
    (z : productCycles G I C n) :
    ((shiftCycles G I C f σ δ n : productCycles G I C n → productCycles G I C n)^[k] z).val =
      (productShift G I C f σ δ : ProductAmbient G I C → ProductAmbient G I C)^[k] z.val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change productShift G I C f σ δ _ = _
    change productShift G I C f σ δ ((shiftCycles G I C f σ δ n : _ → _)^[k] z).val = _
    rw [ih]

lemma shiftCycles_mem_boundaries (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    productBoundaries G I C n ≤
      (productBoundaries G I C n).comap (shiftCycles G I C f σ δ n) := by
  rintro z ⟨w,rfl⟩
  refine ⟨shiftChains G I C f σ δ (n+1) w,?_⟩
  apply Subtype.ext
  exact productBoundary_shift G I C f σ δ w.val

def shiftHomology (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    BoundedProductHomology G I C n →ₗ[ℤ] BoundedProductHomology G I C n :=
  (productBoundaries G I C n).mapQ (productBoundaries G I C n)
    (shiftCycles G I C f σ δ n) (shiftCycles_mem_boundaries G I C f σ δ n)

lemma shiftHomology_iterate_mk (f : G →* G) (σ : C → C) (δ : C → G) (n k : ℕ)
    (z : productCycles G I C n) :
    (shiftHomology G I C f σ δ n : BoundedProductHomology G I C n →
      BoundedProductHomology G I C n)^[k] (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
      ((shiftCycles G I C f σ δ n : productCycles G I C n → productCycles G I C n)^[k] z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih]
    rfl

theorem UniformFillings.product_local_nilpotence {f : G →* G} {n : ℕ}
    (hf : UniformFillings G f n) (hn : 0 < n) (σ : C → C) (δ : C → G) :
    ∀ x : BoundedProductHomology G I C n, ∃ k : ℕ,
      (shiftHomology G I C f σ δ n : BoundedProductHomology G I C n →
        BoundedProductHomology G I C n)^[k] x = 0 := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    obtain ⟨A,hA,hzA⟩ := z.property.1.1
    obtain ⟨k,B,hB,w,hwd,hwa,hwb⟩ := hf.coset_products G hn σ δ z.val z.property.1.2
      (fun i => congrFun z.property.2 i) hA hzA
    refine ⟨k,?_⟩
    rw [shiftHomology_iterate_mk,Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨w,⟨⟨B,hB,hwa⟩,hwd⟩⟩,?_⟩
    apply Subtype.ext
    rw [shiftCycles_iterate_val]
    funext i
    exact (hwb i).trans (productShift_iterate_apply G I C f σ δ z.val k i).symm

end

section

variable (G : Type*) [Group G]

def relativeType (s : Simplex G) : List G := s.2.map (fun x => s.1⁻¹ * x)

@[simp] lemma relativeType_length (s : Simplex G) :
    (relativeType G s).length = degree G s := by simp [relativeType,degree]

def simplexTypes (A : Set G) (n : ℕ) : Set (List G) :=
  {l | l.length = n ∧ ∀ x ∈ l, x ∈ A}

omit [Group G] in
lemma simplexTypes_finite {A : Set G} (hA : A.Finite) (n : ℕ) :
    (simplexTypes G A n).Finite := by
  induction n with
  | zero =>
    apply (Set.finite_singleton []).subset
    intro l hl
    exact List.length_eq_zero_iff.mp hl.1
  | succ n ih =>
    apply ((hA.prod ih).image (fun p : G × List G => p.1 :: p.2)).subset
    intro l hl
    cases l with
    | nil => simp [simplexTypes] at hl
    | cons a l =>
      refine ⟨(a,l),⟨hl.2 a (List.mem_cons_self),?_⟩,rfl⟩
      refine ⟨by simpa using hl.1,fun x hx => hl.2 x ?_⟩
      exact List.mem_cons_of_mem _ hx

lemma relativeType_mem {s : Simplex G} {A : Set G}
    (hs : hasPropagation G A s) : relativeType G s ∈ simplexTypes G A (degree G s) := by
  refine ⟨relativeType_length G s,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  exact hs s.1 (head_mem_vertices G s) y (Or.inr hy)

theorem finite_shapes_bound {T : Set (List G)} (hT : T.Finite) :
    ∃ B : Set G, IsBound G B ∧
      ∀ s : Simplex G, relativeType G s ∈ T → hasPropagation G B s := by
  let V : Set G := insert 1 (⋃ l ∈ T, {x | x ∈ l})
  have hV : V.Finite := (hT.biUnion (fun l _ => List.finite_toSet l)).insert 1
  let B : Set G := (fun p : G × G => p.1⁻¹*p.2) '' (V ×ˢ V)
  have hB : IsBound G B := {
    finite := (hV.prod hV).image _
    one_mem := ⟨(1,1),⟨Set.mem_insert _ _,Set.mem_insert _ _⟩,by simp⟩
    inv_mem := by
      rintro _ ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
      exact ⟨(y,x),⟨hy,hx⟩,by simp⟩ }
  refine ⟨B,hB,?_⟩
  intro s hs x hx y hy
  have hv (x : G) (hx : x ∈ vertices G s) : s.1⁻¹*x ∈ V := by
    rcases hx with rfl | hx
    · simp [V]
    · apply Set.mem_insert_of_mem
      exact Set.mem_iUnion.mpr ⟨relativeType G s,Set.mem_iUnion.mpr ⟨hs,
        List.mem_map.mpr ⟨x,hx,rfl⟩⟩⟩
  refine ⟨(s.1⁻¹*x,s.1⁻¹*y),⟨hv x hx,hv y hy⟩,?_⟩
  simp [mul_assoc]

theorem uniform_shapes_iff {I : Type*} {n : ℕ} (z : I → Chain G)
    (hd : ∀ i, z i ∈ degreeModule G n) :
    (∃ A : Set G, IsBound G A ∧ ∀ i, z i ∈ controlledModule G A) ↔
      ∃ T : Set (List G), T.Finite ∧
        ∀ i s, s ∈ (z i).support → relativeType G s ∈ T := by
  constructor
  · rintro ⟨A,hA,hz⟩
    refine ⟨simplexTypes G A n,simplexTypes_finite G hA.finite n,?_⟩
    intro i s hs
    have h := relativeType_mem G (hz i hs)
    rwa [hd i hs] at h
  · rintro ⟨T,hT,hz⟩
    obtain ⟨B,hB,h⟩ := finite_shapes_bound G hT
    exact ⟨B,hB,fun i s hs => h s (hz i s hs)⟩

end

variable (G C : Type*) [Group G]

def shapeBasisEquiv : (C × Simplex G) ≃ (List G × (C × G)) where
  toFun cs := (relativeType G cs.2,(cs.1,cs.2.1))
  invFun lc := (lc.2.1,(lc.2.2,lc.1.map (fun x => lc.2.2*x)))
  left_inv := by
    rintro ⟨c,g,l⟩
    simp only [relativeType,List.map_map]
    simp
  right_inv := by
    rintro ⟨l,c,g⟩
    simp only [relativeType,List.map_map]
    simp

def shapeCoordinates : (C →₀ Chain G) ≃ₗ[ℤ] (List G →₀ (C × G →₀ ℤ)) :=
  (Finsupp.curryLinearEquiv ℤ).symm.trans
    ((Finsupp.lcongr (shapeBasisEquiv G C) (LinearEquiv.refl ℤ ℤ)).trans
      (Finsupp.curryLinearEquiv ℤ))

@[simp] lemma shapeCoordinates_apply (z : C →₀ Chain G) (l : List G) (c : C) (g : G) :
    shapeCoordinates G C z l (c,g) = z c (g,l.map (fun x => g*x)) := rfl

lemma shapeCoordinates_at_relative (z : C →₀ Chain G) (c : C) (s : Simplex G) :
    shapeCoordinates G C z (relativeType G s) (c,s.1) = z c s := by
  rw [shapeCoordinates_apply]
  congr 1
  cases s with
  | mk g l => simp [relativeType,List.map_map]

lemma relativeType_translate (g : G) (l : List G) :
    relativeType G (g,l.map (fun x => g*x)) = l := by
  simp [relativeType,List.map_map]

lemma shapeCoordinates_support_iff (z : C →₀ Chain G) (T : Set (List G)) :
    (↑(shapeCoordinates G C z).support : Set (List G)) ⊆ T ↔
      ∀ c s, s ∈ (z c).support → relativeType G s ∈ T := by
  constructor
  · intro h c s hs
    apply h
    apply Finsupp.mem_support_iff.mpr
    intro hz
    have he := congrArg (fun a : C × G →₀ ℤ => a (c,s.1)) hz
    rw [shapeCoordinates_at_relative] at he
    exact Finsupp.mem_support_iff.mp hs he
  · intro h l hl
    by_contra hn
    apply Finsupp.mem_support_iff.mp hl
    ext ⟨c,g⟩
    rw [shapeCoordinates_apply]
    apply Finsupp.notMem_support_iff.mp
    intro hs
    have he := h c (g,l.map (fun x => g*x)) hs
    rw [relativeType_translate] at he
    exact hn he

end ListChains

end

end OAI
