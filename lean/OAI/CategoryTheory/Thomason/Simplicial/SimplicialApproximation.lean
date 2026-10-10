import OAI.CategoryTheory.Thomason.Simplicial.BarycentricSupportInclusion
import OAI.CategoryTheory.Thomason.Simplicial.FaceSimplexLift
import OAI.CategoryTheory.Thomason.Simplicial.FixedInternalPathMaps
import OAI.CategoryTheory.Thomason.Simplicial.LastVertexWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.RealizationCellClosure

namespace OAI

section

/-! # Support control for the barycentric comparison homotopy

Order maps preserve inclusions of positive supports. In particular the
comparison from a barycentric parameter to its exact last vertex stays
in the original carrier even after the prescribed boundary order map.
-/

namespace Thomason.Construction

open CategoryTheory PartialOrder

noncomputable section

theorem coordinates_map_support_mono {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (g : P →o Q) (x y : SSet.toTop.obj (nerve P))
    (h : (PosetGeometry.coordinates P x).weights.support ⊆
      (PosetGeometry.coordinates P y).weights.support) :
    (PosetGeometry.coordinates Q ((SSet.toTop.map (nerveMap g.monotone.functor)).hom x)).weights.support ⊆
      (PosetGeometry.coordinates Q ((SSet.toTop.map (nerveMap g.monotone.functor)).hom y)).weights.support := by
  classical
  rw [PosetGeometry.coordinates_nerveMap, PosetGeometry.coordinates_nerveMap]
  change ((PosetGeometry.coordinates P x).weights.mapDomain g).support ⊆
    ((PosetGeometry.coordinates P y).weights.mapDomain g).support
  rw [Finsupp.support_mapDomain_of_nonneg (PosetGeometry.coordinates P x).nonneg,
    Finsupp.support_mapDomain_of_nonneg (PosetGeometry.coordinates P y).nonneg]
  exact Finset.image_subset_image h

namespace SubdivisionBarycentric

theorem iteratedCarrierHomotopy_support (P : PartOrd.{0}) [Finite P] (r : ℕ)
    (t : unitInterval) (z : SSet.toTop.obj (nerve (iteratedChainPoset P r))) :
    (PosetGeometry.coordinates P (iteratedCarrierHomotopy P r (t, z))).weights.support ⊆
      (PosetGeometry.coordinates P (iteratedChainRealization P r z)).weights.support := by
  exact PosetGeometry.commonChainHomotopy_support _ _ _
    (fun z => PosetGeometry.coordinates P (iteratedChainRealization P r z))
    (fun _ => Finset.Subset.refl _) (iterated_lastVertex_support_subset P r) t z

theorem iteratedCarrierHomotopy_map_support (P : PartOrd.{0}) [Finite P] (r : ℕ)
    {Q : Type} [PartialOrder Q] (g : P →o Q)
    (t : unitInterval) (z : SSet.toTop.obj (nerve (iteratedChainPoset P r))) :
    (PosetGeometry.coordinates Q
      ((SSet.toTop.map (nerveMap g.monotone.functor)).hom
        (iteratedCarrierHomotopy P r (t, z)))).weights.support ⊆
      (PosetGeometry.coordinates Q
        ((SSet.toTop.map (nerveMap g.monotone.functor)).hom
          (iteratedChainRealization P r z))).weights.support :=
  coordinates_map_support_mono g _ _ (iteratedCarrierHomotopy_support P r t z)

end SubdivisionBarycentric

namespace PosetGeometry

/-- Three paths in one carrier satisfy the endpoint-fixed triangle
coherence needed by a relative simplicial approximation. -/
def carrierTriangle {P : Type} [PartialOrder P] [Finite P]
    {X : Type} [TopologicalSpace X]
    {f g h : C(X, SSet.toTop.obj (nerve P))}
    (H : f.Homotopy g) (G : g.Homotopy h) (D : f.Homotopy h)
    (c : C(X, SSet.toTop.obj (nerve P)))
    (hH : ∀ t x, (coordinates P (H (t, x))).weights.support ⊆ (coordinates P (c x)).weights.support)
    (hG : ∀ t x, (coordinates P (G (t, x))).weights.support ⊆ (coordinates P (c x)).weights.support)
    (hD : ∀ t x, (coordinates P (D (t, x))).weights.support ⊆ (coordinates P (c x)).weights.support) :
    (H.trans G).toContinuousMap.HomotopyRel D.toContinuousMap
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ (∅ : Set X)} :=
  commonCarrierHomotopyRel (H.trans G) D ∅ (by simp)
    (c.comp ⟨Prod.snd, continuous_snd⟩)
    (fun z => homotopy_trans_support H G (fun x => coordinates P (c x)) hH hG z.1 z.2)
    (fun z => hD z.1 z.2)

end PosetGeometry

end

end Thomason.Construction

end

section

/-! # Naturality of barycentric realization under injective order maps

Injectivity preserves the number of vertices of each face and hence its
uniform barycenter. It is the hypothesis needed for the actual shrinking
parameter maps to commute with boundary inclusions.
-/

namespace Thomason.Construction.RelativeLabelCarrier

open CategoryTheory PartialOrder Convexity
open SubdivisionBarycentric

noncomputable section

theorem chainDistribution_map {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (hf : Function.Injective f) (C : NonemptyFiniteChains P) :
    StdSimplex.map f (chainDistribution C) = chainDistribution (C.map f) := by
  classical
  apply StdSimplex.ext
  simp only [StdSimplex.weights_map, chainDistribution, StdSimplex.weights_subBarycenter,
    Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
  change (∑ x ∈ C.finset, Finsupp.single (f x) (C.finset.card : ℝ)⁻¹) =
    ∑ y ∈ C.finset.image f, Finsupp.single y ((C.finset.image f).card : ℝ)⁻¹
  rw [Finset.card_image_of_injective _ hf, Finset.sum_image]
  exact fun x _ y _ h => hf h

theorem chainMap_injective {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (hf : Function.Injective f) :
    Function.Injective (NonemptyFiniteChains.orderHomMap f) := by
  classical
  intro C D h
  apply NonemptyFiniteChains.ext
  exact Finset.image_injective hf (congrArg NonemptyFiniteChains.finset h)

theorem chainRealizationMap_naturality {P Q : Type} [PartialOrder P] [PartialOrder Q]
    [Fintype P] [Fintype Q] (f : P →o Q) (hf : Function.Injective f)
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) :
    (SSet.toTop.map (nerveMap f.monotone.functor)).hom (chainRealizationMap P z) =
      chainRealizationMap Q ((SSet.toTop.map
        (nerveMap (NonemptyFiniteChains.orderHomMap f).monotone.functor)).hom z) := by
  apply PosetGeometry.coordinates_injective Q
  rw [PosetGeometry.coordinates_nerveMap, coordinates_chainRealizationMap,
    coordinates_chainRealizationMap]
  unfold chainPoint
  rw [PosetGeometry.coordinates_nerveMap, StdSimplex.map_sConvexComb,
    ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  congr 1
  apply congrArg (fun g => StdSimplex.map g (PosetGeometry.coordinates (NonemptyFiniteChains P) z))
  funext C
  exact chainDistribution_map f hf C

/-- The induced order map on every iterated chain stage. -/
def iteratedMap {P Q : PartOrd.{0}} (f : P →o Q) (r : ℕ) :
    iteratedChainPoset P r →o iteratedChainPoset Q r :=
  match r with
  | 0 => f
  | r+1 => NonemptyFiniteChains.orderHomMap (iteratedMap f r)

theorem iteratedMap_injective {P Q : PartOrd.{0}} (f : P →o Q)
    (hf : Function.Injective f) (r : ℕ) : Function.Injective (iteratedMap f r) := by
  induction r with
  | zero => exact hf
  | succ r ih => exact chainMap_injective (iteratedMap f r) ih

/-- The chain-nerve identification is natural for arbitrary monotone maps.
No injectivity is needed for this simplicial identity. -/
theorem iteratedSubdivisionNerveIso_naturality {P Q : PartOrd.{0}} [Finite P] [Finite Q]
    (f : P →o Q) (r : ℕ) :
    (iteratedSubdivision r).map (nerveMap f.monotone.functor) ≫
        (iteratedSubdivisionNerveIso Q r).hom =
      (iteratedSubdivisionNerveIso P r).hom ≫ nerveMap (iteratedMap f r).monotone.functor := by
  induction r with
  | zero =>
      change nerveMap f.monotone.functor ≫ 𝟙 _ = 𝟙 _ ≫ nerveMap f.monotone.functor
      simp only [Category.comp_id, Category.id_comp]
  | succ r ih =>
      change SSet.sd.map ((iteratedSubdivision r).map (nerveMap f.monotone.functor)) ≫
          (SSet.sd.map (iteratedSubdivisionNerveIso Q r).hom ≫
            NerveSubdivisionMap.map (iteratedChainPoset Q r)) =
        (SSet.sd.map (iteratedSubdivisionNerveIso P r).hom ≫
          NerveSubdivisionMap.map (iteratedChainPoset P r)) ≫
            nerveMap (NonemptyFiniteChains.orderHomMap (iteratedMap f r)).monotone.functor
      rw [← Category.assoc, ← SSet.sd.map_comp, ih, SSet.sd.map_comp,
        Category.assoc, NerveSubdivisionMap.map_naturality, ← Category.assoc]

/-- Boundary inclusions commute with the actual iterated barycentric
maps, not only with their homotopy classes. -/
theorem iteratedChainRealization_naturality {P Q : PartOrd.{0}} [Finite P] [Finite Q]
    (f : P →o Q) (hf : Function.Injective f) (r : ℕ)
    (z : SSet.toTop.obj (nerve (iteratedChainPoset P r))) :
    (SSet.toTop.map (nerveMap f.monotone.functor)).hom (iteratedChainRealization P r z) =
      iteratedChainRealization Q r ((SSet.toTop.map
        (nerveMap (iteratedMap f r).monotone.functor)).hom z) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      let := Fintype.ofFinite (iteratedChainPoset P r)
      let := Fintype.ofFinite (iteratedChainPoset Q r)
      change SSet.toTop.obj (nerve (NonemptyFiniteChains (iteratedChainPoset P r))) at z
      change (SSet.toTop.map (nerveMap f.monotone.functor)).hom
        (iteratedChainRealization P r (chainRealizationMap (iteratedChainPoset P r) z)) =
          iteratedChainRealization Q r (chainRealizationMap (iteratedChainPoset Q r)
            ((SSet.toTop.map (nerveMap (NonemptyFiniteChains.orderHomMap
              (iteratedMap f r)).monotone.functor)).hom z))
      rw [ih]
      exact congrArg (iteratedChainRealization Q r)
        (chainRealizationMap_naturality (iteratedMap f r) (iteratedMap_injective f hf r) z)

theorem posetVertexPoint_map {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (v : P) :
    (SSet.toTop.map (nerveMap f.monotone.functor)).hom (posetVertexPoint v) =
      posetVertexPoint (f v) := by
  unfold posetVertexPoint
  rw [RealizationPrism.simplexPoint_naturality]
  rfl

/-- Labels selected on the full parameter space compare to the prescribed
order map on its injected boundary parameter space. -/
theorem boundary_label_le {A B : PartOrd.{0}} [Finite A] [Finite B]
    {P : Type} [PartialOrder P] (i : A →o B) (hi : Function.Injective i)
    (g : A →o P) (F : C(SSet.toTop.obj (nerve B), SSet.toTop.obj (nerve P)))
    (hF : ∀ z, F ((SSet.toTop.map (nerveMap i.monotone.functor)).hom z) =
      (SSet.toTop.map (nerveMap g.monotone.functor)).hom z)
    (r : ℕ) (label : iteratedChainPoset B r → P)
    (hl : ∀ v, 0 < (PosetGeometry.coordinates P
      (F (iteratedChainRealization B r (posetVertexPoint v)))).weights (label v))
    (v : iteratedChainPoset A r) :
    label (iteratedMap i r v) ≤ g (greatestVertex A r v) := by
  apply label_le_prescribed A g r v
  have hp := hl (iteratedMap i r v)
  have hn := iteratedChainRealization_naturality i hi r (posetVertexPoint v)
  rw [posetVertexPoint_map] at hn
  rw [← hn, hF] at hp
  exact hp

end

end Thomason.Construction.RelativeLabelCarrier

end

section

/-! # Naturality of the carrier comparison on an injected boundary

Both endpoints and the entire affine interpolation commute with the
boundary embedding. Thus a continuous map whose restriction is an order
map has the same prescribed boundary path throughout the comparison.
-/

namespace Thomason.Construction

open CategoryTheory PartialOrder Convexity

noncomputable section

namespace PosetGeometry

theorem map_blend {P Q : Type} (f : P → Q) (p q : StdSimplex ℝ P) (t : unitInterval) :
    StdSimplex.map f (blend p q t) = blend (StdSimplex.map f p) (StdSimplex.map f q) t := by
  exact (StdSimplex.isAffineMap_map ℝ f).map_convexCombPair _ _ _ p q

theorem interpolate_map_of_eq {P Q : Type} [PartialOrder P] [PartialOrder Q]
    [Finite P] [Finite Q] (f : P →o Q)
    (x y : SSet.toTop.obj (nerve P)) (x' y' : SSet.toTop.obj (nerve Q))
    (hp : CompatibleSupport (coordinates P x) (coordinates P y))
    (hq : CompatibleSupport (coordinates Q x') (coordinates Q y'))
    (hx : (SSet.toTop.map (nerveMap f.monotone.functor)).hom x = x')
    (hy : (SSet.toTop.map (nerveMap f.monotone.functor)).hom y = y') (t : unitInterval) :
    (SSet.toTop.map (nerveMap f.monotone.functor)).hom (interpolate x y hp t) =
      interpolate x' y' hq t := by
  apply coordinates_injective Q
  rw [coordinates_nerveMap, coordinates_interpolate, map_blend, coordinates_interpolate]
  rw [← coordinates_nerveMap f x, ← coordinates_nerveMap f y, hx, hy]

end PosetGeometry

namespace SubdivisionBarycentric

open RelativeLabelCarrier ChainLabelApproximation

theorem greatestVertex_map {P Q : PartOrd.{0}} (f : P →o Q) (r : ℕ)
    (v : iteratedChainPoset P r) :
    f (greatestVertex P r v) = greatestVertex Q r (iteratedMap f r v) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change NonemptyFiniteChains (iteratedChainPoset P r) at v
      change f (greatestVertex P r (greatest v)) =
        greatestVertex Q r (greatest (v.map (iteratedMap f r)))
      rw [greatest_map]
      exact ih _

theorem greatestVertex_realization_naturality {P Q : PartOrd.{0}}
    [Finite P] [Finite Q] (f : P →o Q) (r : ℕ)
    (z : SSet.toTop.obj (nerve (iteratedChainPoset P r))) :
    (SSet.toTop.map (nerveMap f.monotone.functor)).hom
        ((SSet.toTop.map (nerveMap (greatestVertex P r).monotone.functor)).hom z) =
      (SSet.toTop.map (nerveMap (greatestVertex Q r).monotone.functor)).hom
        ((SSet.toTop.map (nerveMap (iteratedMap f r).monotone.functor)).hom z) := by
  have he : nerveMap (greatestVertex P r).monotone.functor ≫ nerveMap f.monotone.functor =
      nerveMap (iteratedMap f r).monotone.functor ≫
        nerveMap (greatestVertex Q r).monotone.functor := by
    rw [← orderNerveMap_comp, ← orderNerveMap_comp]
    have h : f.comp (greatestVertex P r) = (greatestVertex Q r).comp (iteratedMap f r) := by
      ext v
      exact greatestVertex_map f r v
    exact congrArg (fun k => nerveMap k.monotone.functor) h
  exact congrArg (fun k => k.hom z)
    (((SSet.toTop.map_comp (nerveMap (greatestVertex P r).monotone.functor)
      (nerveMap f.monotone.functor)).symm.trans (congrArg SSet.toTop.map he)).trans
      (SSet.toTop.map_comp (nerveMap (iteratedMap f r).monotone.functor)
        (nerveMap (greatestVertex Q r).monotone.functor)))

theorem iteratedCarrierHomotopy_naturality {P Q : PartOrd.{0}} [Finite P] [Finite Q]
    (f : P →o Q) (hf : Function.Injective f) (r : ℕ)
    (t : unitInterval) (z : SSet.toTop.obj (nerve (iteratedChainPoset P r))) :
    (SSet.toTop.map (nerveMap f.monotone.functor)).hom (iteratedCarrierHomotopy P r (t, z)) =
      iteratedCarrierHomotopy Q r
        (t, (SSet.toTop.map (nerveMap (iteratedMap f r).monotone.functor)).hom z) := by
  apply PosetGeometry.interpolate_map_of_eq f _ _ _ _ _ _
    (iteratedChainRealization_naturality f hf r z)
    (greatestVertex_realization_naturality f r z) t
  · exact PosetGeometry.compatibleSupport_of_subset _ _
      (PosetGeometry.coordinates_chainSupported _) (iterated_lastVertex_support_subset P r z)
  · exact PosetGeometry.compatibleSupport_of_subset _ _
      (PosetGeometry.coordinates_chainSupported _) (iterated_lastVertex_support_subset Q r _)

end SubdivisionBarycentric

end

end Thomason.Construction

end

section

/-! # Simplicial approximation into arbitrary simplicial realizations

The face-simplex resolution is nonsingular and weakly equivalent to the
original target. Its continuous inverse has compact image in a finite
subcomplex, where nonsingular approximation applies.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder

noncomputable section

/-- The target is the original arbitrary simplicial set. No Kan or
nonsingularity hypothesis is imposed on it. -/
theorem exists_simplicial_approximation (Q : PartOrd.{0}) [Fintype Q]
    (K : SSet.{0}) (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj K)) :
    ∃ (r : ℕ) (g : nerve (NonemptyFiniteChains (iteratedChainPoset Q r)) ⟶ K),
      letI := Fintype.ofFinite (iteratedChainPoset Q r)
      Nonempty (((f.comp (iteratedChainRealization Q r)).comp
        (chainRealizationMap (iteratedChainPoset Q r))).Homotopy (SSet.toTop.map g).hom) := by
  let R := FaceSimplexResolution.functor.obj K
  let a := FaceSimplexResolution.augmentation K
  let e := realizationWhiteheadEquiv (SSet.toTop.map a)
    (FaceSimplexResolution.augmentation_weak K)
  let f' := e.invFun.comp f
  let := PosetGeometry.nerve_finite Q
  let := RealizationPrism.compactSpace_of_finite (nerve Q)
  obtain ⟨A, hA, fA, hfA⟩ := RealizationPrism.compact_map_factors R f'
  let := hA
  obtain ⟨r, gA, _, hH⟩ := exists_nonsingular_weak_simplicial_approximation Q A.toSSet fA
  let := Fintype.ofFinite (iteratedChainPoset Q r)
  obtain ⟨H⟩ := hH
  let p := (iteratedChainRealization Q r).comp
    (chainRealizationMap (iteratedChainPoset Q r))
  let k := A.ι ≫ a
  have H₀ : (f.comp p).Homotopy (e.toFun.comp (f'.comp p)) :=
    ((Classical.choice e.right_inv).symm.comp
      (ContinuousMap.Homotopy.refl (f.comp p))).cast (by ext; rfl) (by ext; rfl)
  have hsource : (SSet.toTop.map k).hom.comp (fA.comp p) =
      e.toFun.comp (f'.comp p) := by
    rw [← hfA]
    change (SSet.toTop.map (A.ι ≫ a)).hom.comp (fA.comp p) = _
    rw [SSet.toTop.map_comp]
    rfl
  have htarget : (SSet.toTop.map k).hom.comp (SSet.toTop.map gA).hom =
      (SSet.toTop.map (gA ≫ k)).hom := by
    change (SSet.toTop.map gA ≫ SSet.toTop.map k).hom = _
    exact congrArg TopCat.Hom.hom (SSet.toTop.map_comp gA k).symm
  have H₁ := ((ContinuousMap.Homotopy.refl (SSet.toTop.map k).hom).comp H).cast
    hsource htarget
  exact ⟨r, gA ≫ k, ⟨H₀.trans H₁⟩⟩

/-- The approximation keeps the actual weak-homotopy-equivalence test. -/
theorem exists_weak_simplicial_approximation (Q : PartOrd.{0}) [Fintype Q]
    (K : SSet.{0}) (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj K)) :
    ∃ (r : ℕ) (g : nerve (NonemptyFiniteChains (iteratedChainPoset Q r)) ⟶ K),
      IsWeakHomotopyEquivalence f ↔ realizationWeakEquivalences g := by
  obtain ⟨r, g, ⟨H⟩⟩ := exists_simplicial_approximation Q K f
  let := Fintype.ofFinite (iteratedChainPoset Q r)
  have h := isWeakHomotopyEquivalence_homotopy_iff H
  refine ⟨r, g, ?_⟩
  constructor
  · intro hf
    apply h.mp
    exact (chainRealizationMap_weak (iteratedChainPoset Q r)).comp
      ((iteratedChainRealization_weak Q r).comp hf)
  · intro hg
    have hh := h.mpr hg
    exact IsWeakHomotopyEquivalence.of_precomp (iteratedChainRealization_weak Q r)
      (IsWeakHomotopyEquivalence.of_precomp (chainRealizationMap_weak (iteratedChainPoset Q r)) hh)

theorem exists_iterated_weak_approximation (Q : PartOrd.{0}) [Fintype Q]
    (K : SSet.{0}) (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj K)) :
    ∃ (r : ℕ) (g : (iteratedSubdivision r).obj (nerve Q) ⟶ K),
      IsWeakHomotopyEquivalence f ↔ realizationWeakEquivalences g := by
  obtain ⟨r, g, hg⟩ := exists_weak_simplicial_approximation Q K f
  let e : (iteratedSubdivision (r+1)).obj (nerve Q) ≅
      nerve (NonemptyFiniteChains (iteratedChainPoset Q r)) :=
    iteratedSubdivisionNerveIso Q (r+1)
  exact ⟨r+1, e.hom ≫ g,
    hg.trans (realizationWeakEquivalences.cancel_left_of_respectsIso e.hom g).symm⟩

end

end Thomason.Construction.SubdivisionBarycentric

end

end OAI
