import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.SingularCubeNaturality
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import Mathlib.Data.Fintype.Sort
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import Mathlib.Order.Comparable

namespace OAI

section

/-! # The barycentric image of a poset realization

The image consists exactly of finite probability distributions whose
support is a chain. The converse constructs an actual nerve simplex and
its coordinates rather than assuming an abstract triangulation theorem.
-/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory Opposite Convexity RealizationPrism
open scoped Simplicial

noncomputable section

variable {P : Type} [PartialOrder P]

def ChainSupported (p : StdSimplex ℝ P) : Prop :=
  ∀ x ∈ p.weights.support, ∀ y ∈ p.weights.support, x ≤ y ∨ y ≤ x

omit [PartialOrder P] in
theorem probability_support_nonempty (p : StdSimplex ℝ P) : p.weights.support.Nonempty := by
  apply Finsupp.support_nonempty_iff.mpr
  intro he
  have ht := p.total
  rw [he] at ht
  simp at ht

def chainDimension (p : StdSimplex ℝ P) : ℕ := p.weights.support.card - 1

omit [PartialOrder P] in
theorem chain_card (p : StdSimplex ℝ P) : p.weights.support.card = chainDimension p + 1 := by
  have hp := Finset.card_pos.mpr (probability_support_nonempty p)
  unfold chainDimension
  omega

def chainEnumerationData (p : StdSimplex ℝ P) (hp : ChainSupported p) :
    {e : Fin (chainDimension p + 1) ↪o P //
      Set.range e = (p.weights.support : Set P)} := by
  classical
  let : LinearOrder p.weights.support := Relation.linearOrderOfSymmGen
    (fun x y => hp x.val x.property y.val y.property)
  let e : Fin (chainDimension p + 1) ≃o p.weights.support :=
    monoEquivOfFin p.weights.support (by simpa using chain_card p)
  refine ⟨e.toOrderEmbedding.trans (OrderEmbedding.subtype _), ?_⟩
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).property
  · intro hx
    obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
    exact ⟨i, congrArg Subtype.val hi⟩

/-- Increasing enumeration of the support, with the original partial order. -/
def chainEnumeration (p : StdSimplex ℝ P) (hp : ChainSupported p) :
    Fin (chainDimension p + 1) ↪o P := (chainEnumerationData p hp).val

theorem chainEnumeration_range (p : StdSimplex ℝ P) (hp : ChainSupported p) :
    Set.range (chainEnumeration p hp) = (p.weights.support : Set P) :=
  (chainEnumerationData p hp).property

def chainCoordinates (p : StdSimplex ℝ P) (hp : ChainSupported p) :
    StdSimplex ℝ (Fin (chainDimension p + 1)) :=
  StdSimplex.map (Function.invFun (chainEnumeration p hp)) p

/-- Reinserting the enumerated support recovers the original distribution. -/
theorem chainCoordinates_recover (p : StdSimplex ℝ P) (hp : ChainSupported p) :
    StdSimplex.map (chainEnumeration p hp) (chainCoordinates p hp) = p := by
  apply StdSimplex.ext
  change (p.weights.mapDomain (Function.invFun (chainEnumeration p hp))).mapDomain
    (chainEnumeration p hp) = p.weights
  rw [← Finsupp.mapDomain_comp]
  have he : p.weights.mapDomain ((chainEnumeration p hp) ∘
      Function.invFun (chainEnumeration p hp)) = p.weights.mapDomain id := by
    apply Finsupp.mapDomain_congr
    intro x hx
    have hr : x ∈ Set.range (chainEnumeration p hp) := by
      rw [chainEnumeration_range]
      exact hx
    obtain ⟨i, rfl⟩ := hr
    change chainEnumeration p hp (Function.invFun (chainEnumeration p hp)
      (chainEnumeration p hp i)) = chainEnumeration p hp i
    rw [Function.leftInverse_invFun (chainEnumeration p hp).injective]
  exact he.trans Finsupp.mapDomain_id

theorem coordinates_chainSupported (x : SSet.toTop.obj (nerve P)) :
    ChainSupported (coordinates P x) := by
  obtain ⟨n, s, p, rfl⟩ := point_representation_simplex (nerve P) x
  rw [coordinates_simplexPoint]
  intro a ha b hb
  classical
  change a ∈ (p.weights.mapDomain s.obj).support at ha
  change b ∈ (p.weights.mapDomain s.obj).support at hb
  rw [Finsupp.support_mapDomain_of_nonneg p.nonneg] at ha hb
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
  exact (le_total i j).elim (fun h => Or.inl (s.monotone h))
    (fun h => Or.inr (s.monotone h))

/-- Exact image theorem for the actual geometric realization coordinates. -/
theorem mem_range_coordinates_iff (p : StdSimplex ℝ P) :
    p ∈ Set.range (coordinates P) ↔ ChainSupported p := by
  constructor
  · rintro ⟨x, rfl⟩
    exact coordinates_chainSupported x
  · intro hp
    refine ⟨simplexPoint (nerve P)
      (NormalizedSimplexIdentities.orderSimplex (chainEnumeration p hp).toOrderHom)
      (chainCoordinates p hp), ?_⟩
    rw [coordinates_simplexPoint]
    exact chainCoordinates_recover p hp

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Interpolation inside a common chain of a poset realization -/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory Convexity RealizationPrism
open scoped Simplicial

noncomputable section

variable {P : Type} [PartialOrder P]

/-- The union of two positive supports is a chain. -/
def CompatibleSupport (p q : StdSimplex ℝ P) : Prop :=
  ∀ x, (p.weights x ≠ 0 ∨ q.weights x ≠ 0) →
    ∀ y, (p.weights y ≠ 0 ∨ q.weights y ≠ 0) → x ≤ y ∨ y ≤ x

def blend (p q : StdSimplex ℝ P) (t : unitInterval) : StdSimplex ℝ P :=
  convexCombPair (R := ℝ) (unitInterval.symm t) t
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) p q

omit [PartialOrder P] in
theorem blend_zero (p q : StdSimplex ℝ P) : blend p q 0 = p := by
  ext x
  simp [blend]

omit [PartialOrder P] in
theorem blend_one (p q : StdSimplex ℝ P) : blend p q 1 = q := by
  ext x
  simp [blend]

omit [PartialOrder P] in
theorem blend_self (p : StdSimplex ℝ P) (t : unitInterval) : blend p p t = p := by
  ext x
  simp only [blend, StdSimplex.weights_convexCombPair, Finsupp.coe_add,
    Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitInterval.coe_symm_eq]
  ring

/-- The whole interpolation stays in the geometric image when the two
    supports lie in a common chain. -/
theorem blend_chainSupported (p q : StdSimplex ℝ P) (h : CompatibleSupport p q)
    (t : unitInterval) : ChainSupported (blend p q t) := by
  have hs (x : P) (hx : (blend p q t).weights x ≠ 0) :
      p.weights x ≠ 0 ∨ q.weights x ≠ 0 := by
    by_contra he
    push Not at he
    apply hx
    simp [blend, he.1, he.2]
  intro x hx y hy
  exact h x (hs x (Finsupp.mem_support_iff.mp hx)) y (hs y (Finsupp.mem_support_iff.mp hy))

theorem compatibleSupport_of_subset (p q : StdSimplex ℝ P) (hp : ChainSupported p)
    (hq : q.weights.support ⊆ p.weights.support) : CompatibleSupport p q := by
  intro x hx y hy
  exact hp x
    (hx.elim Finsupp.mem_support_iff.mpr (fun h => hq (Finsupp.mem_support_iff.mpr h))) y
    (hy.elim Finsupp.mem_support_iff.mpr (fun h => hq (Finsupp.mem_support_iff.mpr h)))

variable [Finite P]

/-- Continuous interpolation in the barycentric image, with its actual
    finite-poset realization topology. -/
def interpolate (x y : SSet.toTop.obj (nerve P))
    (h : CompatibleSupport (coordinates P x) (coordinates P y)) (t : unitInterval) :
    SSet.toTop.obj (nerve P) :=
  (coordinatesHomeomorph P).symm
    ⟨blend (coordinates P x) (coordinates P y) t,
      (mem_range_coordinates_iff _).mpr (blend_chainSupported _ _ h t)⟩

theorem coordinates_interpolate (x y : SSet.toTop.obj (nerve P))
    (h : CompatibleSupport (coordinates P x) (coordinates P y)) (t : unitInterval) :
    coordinates P (interpolate x y h t) = blend (coordinates P x) (coordinates P y) t :=
  congrArg Subtype.val ((coordinatesHomeomorph P).apply_symm_apply _)

theorem interpolate_zero (x y : SSet.toTop.obj (nerve P))
    (h : CompatibleSupport (coordinates P x) (coordinates P y)) : interpolate x y h 0 = x := by
  apply coordinates_injective P
  rw [coordinates_interpolate, blend_zero]

theorem interpolate_one (x y : SSet.toTop.obj (nerve P))
    (h : CompatibleSupport (coordinates P x) (coordinates P y)) : interpolate x y h 1 = y := by
  apply coordinates_injective P
  rw [coordinates_interpolate, blend_one]

theorem interpolate_self (x : SSet.toTop.obj (nerve P))
    (h : CompatibleSupport (coordinates P x) (coordinates P x)) (t : unitInterval) :
    interpolate x x h t = x := by
  apply coordinates_injective P
  rw [coordinates_interpolate, blend_self]

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Relative homotopies from compatible poset coordinates -/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory Convexity RealizationPrism
open scoped Simplicial

noncomputable section

variable {P : Type} [PartialOrder P] [Finite P]
variable {X : Type} [TopologicalSpace X]

def blendMap (f g : C(X, SSet.toTop.obj (nerve P))) :
    C(unitInterval × X, StdSimplex ℝ P) where
  toFun p := blend (coordinates P (f p.2)) (coordinates P (g p.2)) p.1
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ P).continuous_iff]
    apply continuous_pi
    intro v
    simp only [Function.comp_def, blend, StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      unitInterval.coe_symm_eq]
    have hf : Continuous (fun p : unitInterval × X => (coordinates P (f p.2)).weights v) :=
      (StdSimplex.continuous_weights_apply ℝ v).comp
        ((coordinates P).continuous.comp (f.continuous.comp continuous_snd))
    have hg : Continuous (fun p : unitInterval × X => (coordinates P (g p.2)).weights v) :=
      (StdSimplex.continuous_weights_apply ℝ v).comp
        ((coordinates P).continuous.comp (g.continuous.comp continuous_snd))
    exact ((continuous_const.sub continuous_fst.subtype_val).mul hf).add
      (continuous_fst.subtype_val.mul hg)

/-- Two maps with pointwise compatible positive supports are homotopic
    by straight-line interpolation in the proved barycentric image. -/
def commonChainHomotopy (f g : C(X, SSet.toTop.obj (nerve P)))
    (h : ∀ x, CompatibleSupport (coordinates P (f x)) (coordinates P (g x))) :
    f.Homotopy g where
  toFun p := interpolate (f p.2) (g p.2) (h p.2) p.1
  continuous_toFun := (coordinatesHomeomorph P).symm.continuous.comp
    ((blendMap f g).continuous.subtype_mk
      (fun p => (mem_range_coordinates_iff _).mpr (blend_chainSupported _ _ (h p.2) p.1)))
  map_zero_left x := interpolate_zero (f x) (g x) (h x)
  map_one_left x := interpolate_one (f x) (g x) (h x)

/-- The interpolation fixes the full set where the endpoint maps agree. -/
def commonChainHomotopyRel (f g : C(X, SSet.toTop.obj (nerve P)))
    (h : ∀ x, CompatibleSupport (coordinates P (f x)) (coordinates P (g x)))
    (A : Set X) (hA : ∀ x ∈ A, f x = g x) : f.HomotopyRel g A where
  toHomotopy := commonChainHomotopy f g h
  prop' t x hx := by
    apply coordinates_injective P
    change coordinates P (interpolate (f x) (g x) (h x) t) = coordinates P (f x)
    rw [coordinates_interpolate, hA x hx, blend_self]

/-- In particular compatible-support changes preserve the actual weak
    homotopy-equivalence test; no model-category input occurs. -/
theorem compatible_support_weak_iff (f g : C(X, SSet.toTop.obj (nerve P)))
    (h : ∀ x, CompatibleSupport (coordinates P (f x)) (coordinates P (g x))) :
    IsWeakHomotopyEquivalence f ↔ IsWeakHomotopyEquivalence g :=
  isWeakHomotopyEquivalence_homotopy_iff (commonChainHomotopy f g h)

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Coherence inside a common poset carrier

Two paths whose coordinates remain in a common chain are homotopic
with their endpoints fixed. The same construction fixes any prescribed
stationary side of a family of paths.
-/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory Convexity

noncomputable section

theorem blend_support_subset_union {P : Type} [PartialOrder P] [DecidableEq P]
    (p q : StdSimplex ℝ P) (t : unitInterval) :
    (blend p q t).weights.support ⊆ p.weights.support ∪ q.weights.support := by
  intro x hx
  by_contra h
  have hx' : x ∉ p.weights.support ∧ x ∉ q.weights.support := by
    simpa only [Finset.mem_union, not_or] using h
  have hp : p.weights x = 0 := by
    simpa only [Finsupp.mem_support_iff, not_not] using hx'.1
  have hq : q.weights x = 0 := by
    simpa only [Finsupp.mem_support_iff, not_not] using hx'.2
  have hn := Finsupp.mem_support_iff.mp hx
  exact hn (by simp [blend, hp, hq])

theorem compatibleSupport_of_subsets {P : Type} [PartialOrder P]
    (p q c : StdSimplex ℝ P) (hc : ChainSupported c)
    (hp : p.weights.support ⊆ c.weights.support)
    (hq : q.weights.support ⊆ c.weights.support) : CompatibleSupport p q := by
  intro x hx y hy
  apply hc
  · rcases hx with hx | hx
    · exact hp (Finsupp.mem_support_iff.mpr hx)
    · exact hq (Finsupp.mem_support_iff.mpr hx)
  · rcases hy with hy | hy
    · exact hp (Finsupp.mem_support_iff.mpr hy)
    · exact hq (Finsupp.mem_support_iff.mpr hy)

variable {P : Type} [PartialOrder P] [Finite P]
variable {X : Type} [TopologicalSpace X]

theorem commonChainHomotopy_support
    (f g : C(X, SSet.toTop.obj (nerve P)))
    (h : ∀ x, CompatibleSupport (coordinates P (f x)) (coordinates P (g x)))
    (c : X → StdSimplex ℝ P)
    (hf : ∀ x, (coordinates P (f x)).weights.support ⊆ (c x).weights.support)
    (hg : ∀ x, (coordinates P (g x)).weights.support ⊆ (c x).weights.support)
    (t : unitInterval) (x : X) :
    (coordinates P (commonChainHomotopy f g h (t, x))).weights.support ⊆
      (c x).weights.support := by
  classical
  change (coordinates P (interpolate (f x) (g x) (h x) t)).weights.support ⊆ _
  rw [coordinates_interpolate]
  exact (blend_support_subset_union _ _ t).trans (Finset.union_subset (hf x) (hg x))

omit [Finite P] in
theorem homotopy_trans_support {f g h : C(X, SSet.toTop.obj (nerve P))}
    (H : f.Homotopy g) (G : g.Homotopy h) (c : X → StdSimplex ℝ P)
    (hH : ∀ t x, (coordinates P (H (t, x))).weights.support ⊆ (c x).weights.support)
    (hG : ∀ t x, (coordinates P (G (t, x))).weights.support ⊆ (c x).weights.support)
    (t : unitInterval) (x : X) :
    (coordinates P (H.trans G (t, x))).weights.support ⊆ (c x).weights.support := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hH _ x
  · exact hG _ x

/-- A homotopy of paths with exactly fixed ends and stationary side.
All interpolation occurs in the given common carrier. -/
def commonCarrierHomotopyRel {f g : C(X, SSet.toTop.obj (nerve P))}
    (H G : f.Homotopy g) (A : Set X)
    (hA : ∀ t x, x ∈ A → H (t, x) = G (t, x))
    (c : C(unitInterval × X, SSet.toTop.obj (nerve P)))
    (hH : ∀ z, (coordinates P (H z)).weights.support ⊆ (coordinates P (c z)).weights.support)
    (hG : ∀ z, (coordinates P (G z)).weights.support ⊆ (coordinates P (c z)).weights.support) :
    H.toContinuousMap.HomotopyRel G.toContinuousMap
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ A} :=
  commonChainHomotopyRel H.toContinuousMap G.toContinuousMap
    (fun z => compatibleSupport_of_subsets _ _ _ (coordinates_chainSupported (c z))
      (hH z) (hG z)) _ (by
        intro z hz
        rcases hz with hz | hz | hz
        · rcases z with ⟨t, x⟩
          dsimp only at hz
          subst t
          exact (H.map_zero_left x).trans (G.map_zero_left x).symm
        · rcases z with ⟨t, x⟩
          dsimp only at hz
          subst t
          exact (H.map_one_left x).trans (G.map_one_left x).symm
        · exact hA z.1 z.2 hz)

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Coordinate naturality for actual poset nerve maps -/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory Convexity RealizationPrism

noncomputable section

theorem coordinates_nerveMap {Q P : Type} [PartialOrder Q] [PartialOrder P]
    (f : Q →o P) (z : SSet.toTop.obj (nerve Q)) :
    coordinates P ((SSet.toTop.map (nerveMap f.monotone.functor)).hom z) =
      StdSimplex.map f (coordinates Q z) := by
  obtain ⟨n, s, p, rfl⟩ := point_representation_simplex (nerve Q) z
  calc
    _ = coordinates P (simplexPoint (nerve P)
        ((nerveMap f.monotone.functor).app _ s) p) :=
      congrArg (coordinates P) (simplexPoint_naturality (nerveMap f.monotone.functor) s p)
    _ = StdSimplex.map ((nerveMap f.monotone.functor).app _ s).obj p :=
      coordinates_simplexPoint P _ p
    _ = StdSimplex.map f (StdSimplex.map s.obj p) := by
      rw [← StdSimplex.map_comp]
      rfl
    _ = _ := congrArg (StdSimplex.map f) (coordinates_simplexPoint Q s p).symm

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Nonempty intersections in the finite-poset open vertex cover -/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory Convexity RealizationPrism
open scoped Simplicial

noncomputable section

variable {P : Type} [PartialOrder P]

def openFace (S : Finset P) : Set (SSet.toTop.obj (nerve P)) :=
  Set.ofPred (fun x => ∀ v ∈ S, 0 < (coordinates P x).weights v)

theorem openFace_isOpen (S : Finset P) : IsOpen (openFace S) := by
  classical
  have he : openFace S = ⋂ v ∈ S, Set.ofPred
      (fun x : SSet.toTop.obj (nerve P) => 0 < (coordinates P x).weights v) := by
    ext x
    simp [openFace]
  rw [he]
  apply isOpen_biInter_finset
  intro v hv
  exact isOpen_lt continuous_const
    ((StdSimplex.continuous_weights_apply ℝ v).comp (coordinates P).continuous)

/-- A nonempty intersection forces its vertex labels to form a chain. -/
theorem chain_of_openFace_nonempty (S : Finset P) (hS : (openFace S).Nonempty) :
    ∀ v ∈ S, ∀ w ∈ S, v ≤ w ∨ w ≤ v := by
  obtain ⟨x, hx⟩ := hS
  intro v hv w hw
  exact coordinates_chainSupported x v (Finsupp.mem_support_iff.mpr (ne_of_gt (hx v hv)))
    w (Finsupp.mem_support_iff.mpr (ne_of_gt (hx w hw)))

omit [PartialOrder P] in
theorem subBarycenter_weights (S : Finset P) (hS : S.Nonempty) (v : P) (hv : v ∈ S) :
    (StdSimplex.subBarycenter (K := ℝ) S hS).weights v =
      (S.card : ℝ)⁻¹ := by
  classical
  simp [StdSimplex.weights_subBarycenter, Finsupp.single_apply, hv]

omit [PartialOrder P] in
theorem subBarycenter_support (S : Finset P) (hS : S.Nonempty) :
    (StdSimplex.subBarycenter (K := ℝ) S hS).weights.support = S := by
  classical
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
  ext v
  rw [Finsupp.mem_support_iff]
  by_cases hv : v ∈ S
  · rw [subBarycenter_weights S hS v hv]
    simp [hv, hc]
  · rw [StdSimplex.subBarycenter_weights_apply_eq_zero S hS v hv]
    simp [hv]

theorem subBarycenter_chainSupported (S : Finset P) (hS : S.Nonempty)
    (hchain : ∀ v ∈ S, ∀ w ∈ S, v ≤ w ∨ w ≤ v) :
    ChainSupported (StdSimplex.subBarycenter (K := ℝ) S hS) := by
  intro v hv w hw
  rw [subBarycenter_support] at hv hw
  exact hchain v hv w hw

variable [Finite P]

def openFaceCenter (S : Finset P) (hS : S.Nonempty)
    (hchain : ∀ v ∈ S, ∀ w ∈ S, v ≤ w ∨ w ≤ v) : SSet.toTop.obj (nerve P) :=
  (coordinatesHomeomorph P).symm
    ⟨StdSimplex.subBarycenter (K := ℝ) S hS,
      (mem_range_coordinates_iff _).mpr (subBarycenter_chainSupported S hS hchain)⟩

theorem coordinates_openFaceCenter (S : Finset P) (hS : S.Nonempty)
    (hchain : ∀ v ∈ S, ∀ w ∈ S, v ≤ w ∨ w ≤ v) :
    coordinates P (openFaceCenter S hS hchain) = StdSimplex.subBarycenter (K := ℝ) S hS :=
  congrArg Subtype.val ((coordinatesHomeomorph P).apply_symm_apply _)

theorem openFaceCenter_mem (S : Finset P) (hS : S.Nonempty)
    (hchain : ∀ v ∈ S, ∀ w ∈ S, v ≤ w ∨ w ≤ v) :
    openFaceCenter S hS hchain ∈ openFace S := by
  intro v hv
  rw [coordinates_openFaceCenter, subBarycenter_weights S hS v hv]
  exact inv_pos.mpr (by exact_mod_cast Finset.card_pos.mpr hS)

/-- The open-cover nerve has exactly the nonempty chains as simplices. -/
theorem openFace_nonempty_iff (S : Finset P) (hS : S.Nonempty) :
    (openFace S).Nonempty ↔ ∀ v ∈ S, ∀ w ∈ S, v ≤ w ∨ w ≤ v :=
  ⟨chain_of_openFace_nonempty S, fun h => ⟨openFaceCenter S hS h, openFaceCenter_mem S hS h⟩⟩

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Contractible finite intersections of poset vertex stars -/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory Convexity RealizationPrism
open scoped Simplicial

noncomputable section

variable {P : Type} [PartialOrder P]

omit [PartialOrder P] in
theorem blend_positive (p q : StdSimplex ℝ P) (t : unitInterval) (v : P)
    (hp : 0 < p.weights v) (hq : 0 < q.weights v) :
    0 < (blend p q t).weights v := by
  simp only [blend, StdSimplex.weights_convexCombPair, Finsupp.coe_add,
    Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitInterval.coe_symm_eq]
  by_cases ht : (t : ℝ) = 0
  · simpa only [ht, sub_zero, one_mul, zero_mul, add_zero] using hp
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr t.property.2) hp.le)
      (mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)) hq)

variable [Finite P]

theorem compatible_openFace_center (S : Finset P) (hS : S.Nonempty)
    (hchain : ∀ v ∈ S, ∀ w ∈ S, v ≤ w ∨ w ≤ v) (x : openFace S) :
    CompatibleSupport (coordinates P x.val)
      (coordinates P (openFaceCenter S hS hchain)) := by
  apply compatibleSupport_of_subset _ _ (coordinates_chainSupported x.val)
  rw [coordinates_openFaceCenter, subBarycenter_support]
  intro v hv
  exact Finsupp.mem_support_iff.mpr (ne_of_gt (x.property v hv))

/-- The explicit contraction to the barycenter keeps every prescribed
    star coordinate strictly positive at every time, including endpoints. -/
def openFaceContraction (S : Finset P) (hS : S.Nonempty)
    (hchain : ∀ v ∈ S, ∀ w ∈ S, v ≤ w ∨ w ≤ v) :
    (ContinuousMap.id (openFace S)).Homotopy
      (ContinuousMap.const _ ⟨openFaceCenter S hS hchain, openFaceCenter_mem S hS hchain⟩) := by
  let f : C(openFace S, SSet.toTop.obj (nerve P)) := ⟨Subtype.val, continuous_subtype_val⟩
  let g : C(openFace S, SSet.toTop.obj (nerve P)) := ContinuousMap.const _ (openFaceCenter S hS hchain)
  let H := commonChainHomotopy f g (compatible_openFace_center S hS hchain)
  have hH (z : unitInterval × openFace S) : H z ∈ openFace S := by
    intro v hv
    change 0 < (coordinates P
      (interpolate z.2.val (openFaceCenter S hS hchain)
        (compatible_openFace_center S hS hchain z.2) z.1)).weights v
    rw [coordinates_interpolate]
    exact blend_positive _ _ z.1 v (z.2.property v hv) (openFaceCenter_mem S hS hchain v hv)
  exact {
    toFun := fun z => ⟨H z, hH z⟩
    continuous_toFun := H.continuous.subtype_mk hH
    map_zero_left := fun x => Subtype.ext (H.map_zero_left x)
    map_one_left := fun x => Subtype.ext (H.map_one_left x) }

theorem openFace_contractible (S : Finset P) (hS : S.Nonempty)
    (hchain : ∀ v ∈ S, ∀ w ∈ S, v ≤ w ∨ w ≤ v) : ContractibleSpace (openFace S) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨⟨openFaceCenter S hS hchain, openFaceCenter_mem S hS hchain⟩,
      ⟨openFaceContraction S hS hchain⟩⟩

/-- Every nonempty finite intersection in this open cover has a proved
    actual singular-counit weak equivalence. -/
theorem openFace_singular_counit_weak (S : Finset P) (hS : S.Nonempty)
    (hx : (openFace S).Nonempty) :
    topologicalWeakEquivalences (sSetTopAdj.counit.app (TopCat.of (openFace S))) := by
  let := openFace_contractible S hS (chain_of_openFace_nonempty S hx)
  exact singular_counit_weak_contractible _

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Restricting a poset vertex star to the comparable full subposet -/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory Opposite RealizationPrism Topology
open scoped Simplicial

noncomputable section

variable {P : Type} [PartialOrder P]

theorem eq_vertex_iff (s : (nerve P).obj (.op (.mk 0))) (v : P) :
    s = vertex v ↔ s.obj 0 = v := by
  constructor
  · intro h
    exact congrArg (fun s => s.obj 0) h
  · intro h
    apply nerve.ext_of_isThin
    funext i
    have hi : i = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance _ _
    subst i
    exact h

def comparableVertex (v : P) : comparable v := ⟨v, Or.inl le_rfl⟩

theorem comparable_inclusion_vertex (v : P) :
    (nerveMap (fullSubposetInclusion (comparable v))).app (.op (.mk 0))
      (vertex (comparableVertex v)) = vertex v := by
  apply (eq_vertex_iff _ _).mpr
  rfl

theorem comparable_preimage_vertexStar (v : P) :
    (SSet.toTop.map (nerveMap (fullSubposetInclusion (comparable v)))).hom ⁻¹'
      vertexStar (nerve P) (vertex v) =
        vertexStar (nerve (comparable v)) (vertex (comparableVertex v)) := by
  ext x
  rw [Set.mem_preimage, map_mem_vertexStar_iff]
  constructor
  · rintro ⟨u, hu, hx⟩
    have huv : u = vertex (comparableVertex v) := by
      apply (eq_vertex_iff _ _).mpr
      apply Subtype.ext
      exact congrArg (fun z : (nerve P).obj (.op (.mk 0)) => z.obj 0) hu
    rwa [huv] at hx
  · intro hx
    exact ⟨vertex (comparableVertex v), comparable_inclusion_vertex v, hx⟩

/-- The ambient star lies in the actual realization of the comparable subposet. -/
theorem comparable_range_contains_vertexStar (v : P) :
    vertexStar (nerve P) (vertex v) ⊆
      Set.range (SSet.toTop.map (nerveMap (fullSubposetInclusion (comparable v)))).hom := by
  intro x hx
  let e := fullSubposetCarrierHomeomorph (comparable v)
  let y := e.symm ⟨x, vertexStar_carrier v x hx⟩
  refine ⟨y, ?_⟩
  have he := e.apply_symm_apply ⟨x, vertexStar_carrier v x hx⟩
  exact (fullSubposetCarrierHomeomorph_inclusion (comparable v) y).symm.trans
    (congrArg Subtype.val he)

/-- Removing vertices incomparable with `v` does not alter its open star,
    including the topology inherited from the actual realization. -/
def comparableStarHomeomorph (v : P) :
    vertexStar (nerve (comparable v)) (vertex (comparableVertex v)) ≃ₜ
      vertexStar (nerve P) (vertex v) :=
  (Homeomorph.setCongr (comparable_preimage_vertexStar v).symm).trans
    ((fullSubposet_realization_isClosedEmbedding (comparable v)).isEmbedding.homeomorphOfSubsetRange
      (comparable_range_contains_vertexStar v))

end

end Thomason.Construction.PosetGeometry

end

section

/-! # A monotone clamp on the subposet comparable with a vertex -/

namespace Thomason.Construction.PosetGeometry

noncomputable section

variable {P : Type} [PartialOrder P]

/-- On the comparable subposet, raise vertices below `v` to `v`. -/
def upperClamp (v : P) : comparable v →o comparable v := by
  classical
  refine { toFun := fun x => if x.val ≤ v then comparableVertex v else x, monotone' := ?_ }
  ·
    intro x y hxy
    have hxy' : x.val ≤ y.val := hxy
    dsimp
    split_ifs with hx hy hy
    · exact le_rfl
    · exact y.property.resolve_left hy
    · exact False.elim (hx (hxy'.trans hy))
    · exact hxy

theorem le_upperClamp (v : P) (x : comparable v) : x ≤ upperClamp v x := by
  classical
  change x.val ≤ (if x.val ≤ v then comparableVertex v else x).val
  split_ifs with h
  · exact h
  · exact le_rfl

theorem comparableVertex_le_upperClamp (v : P) (x : comparable v) :
    comparableVertex v ≤ upperClamp v x := by
  classical
  change v ≤ (if x.val ≤ v then comparableVertex v else x).val
  split_ifs with h
  · exact le_rfl
  · exact x.property.resolve_left h

theorem upperClamp_vertex (v : P) :
    upperClamp v (comparableVertex v) = comparableVertex v := by
  classical
  simp [upperClamp, comparableVertex]

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Realized vertices and constant simplicial maps -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

def vertexPoint (K : SSet.{0}) (v : K.obj (.op (.mk 0))) : SSet.toTop.obj K :=
  simplexPoint K v (StdSimplex.single (0 : Fin 1))

theorem vertexPoint_mem_vertexStar (K : SSet.{0}) (v : K.obj (.op (.mk 0))) :
    vertexPoint K v ∈ vertexStar K v := by
  apply (simplexPoint_mem_vertexStar_iff K v _ v).mpr
  refine ⟨0, by simp, ?_⟩
  have he : vertexOperator (0 : Fin 1) = 𝟙 (SimplexCategory.mk 0) := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  change K.map (vertexOperator (0 : Fin 1)).op v = v
  rw [he]
  exact ConcreteCategory.congr_hom (K.map_id _) v

theorem map_vertexPoint {K L : SSet.{0}} (f : K ⟶ L)
    (v : K.obj (.op (.mk 0))) :
    (SSet.toTop.map f).hom (vertexPoint K v) = vertexPoint L (f.app _ v) :=
  simplexPoint_naturality f v _

/-- A constant simplicial map realizes to the constant continuous map at
    the same actual vertex, even on simplices of arbitrary dimension. -/
theorem realization_const {K L : SSet.{0}} (v : L.obj (.op (.mk 0)))
    (x : SSet.toTop.obj K) :
    (SSet.toTop.map (SSet.const (X := K) v)).hom x = vertexPoint L v := by
  obtain ⟨n, s, p, rfl⟩ := point_representation_simplex K x
  rw [simplexPoint_naturality]
  change simplexPoint L (L.map ((SimplexCategory.mk n).const _ 0).op v) p = _
  rw [simplexPoint_map]
  exact congrArg (simplexPoint L v)
    (@Subsingleton.elim (StdSimplex ℝ (Fin 1)) inferInstance _ _)

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Actual fixed-endpoint internal path complexes -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The subcomplex of internal paths having the two specified constant
endpoint simplices. -/
def fixedInternalPathSubcomplex (X : SSet.{0}) (x y : X _⦋0⦌) :
    (internalPathObject X).Subcomplex :=
  (SSet.Subcomplex.ofSimplex x).preimage (internalPathStart X) ⊓
    (SSet.Subcomplex.ofSimplex y).preimage (internalPathEnd X)

abbrev fixedInternalPaths (X : SSet.{0}) (x y : X _⦋0⦌) : SSet.{0} :=
  (fixedInternalPathSubcomplex X x y).toSSet

theorem fixedInternalPaths_start (X : SSet.{0}) (x y : X _⦋0⦌) :
    (fixedInternalPathSubcomplex X x y).ι ≫ internalPathStart X = SSet.const x := by
  let a := SSet.Subcomplex.homOfLE (show fixedInternalPathSubcomplex X x y ≤
    (SSet.Subcomplex.ofSimplex x).preimage (internalPathStart X) from inf_le_left)
  have he : (fixedInternalPathSubcomplex X x y).ι ≫ internalPathStart X =
      a ≫ (SSet.Subcomplex.ofSimplex x).fromPreimage (internalPathStart X) ≫
        (SSet.Subcomplex.ofSimplex x).ι := rfl
  rw [he, SSet.Subcomplex.ofSimplex_ι, SSet.comp_const, SSet.comp_const]

theorem fixedInternalPaths_end (X : SSet.{0}) (x y : X _⦋0⦌) :
    (fixedInternalPathSubcomplex X x y).ι ≫ internalPathEnd X = SSet.const y := by
  let a := SSet.Subcomplex.homOfLE (show fixedInternalPathSubcomplex X x y ≤
    (SSet.Subcomplex.ofSimplex y).preimage (internalPathEnd X) from inf_le_right)
  have he : (fixedInternalPathSubcomplex X x y).ι ≫ internalPathEnd X =
      a ≫ (SSet.Subcomplex.ofSimplex y).fromPreimage (internalPathEnd X) ≫
        (SSet.Subcomplex.ofSimplex y).ι := rfl
  rw [he, SSet.Subcomplex.ofSimplex_ι, SSet.comp_const, SSet.comp_const]

/-- A map of internal paths with constant endpoints lands in the actual
fixed-endpoint subcomplex. -/
def fixedInternalPathsLift {K X : SSet.{0}} (x y : X _⦋0⦌)
    (a : K ⟶ internalPathObject X)
    (h₀ : a ≫ internalPathStart X = SSet.const x)
    (h₁ : a ≫ internalPathEnd X = SSet.const y) : K ⟶ fixedInternalPaths X x y :=
  SSet.Subcomplex.lift a (by
    intro d z hz
    obtain ⟨u, rfl⟩ := hz
    constructor
    · change (a ≫ internalPathStart X).app d u ∈ (SSet.Subcomplex.ofSimplex x).obj d
      rw [h₀]
      exact ⟨_, rfl⟩
    · change (a ≫ internalPathEnd X).app d u ∈ (SSet.Subcomplex.ofSimplex y).obj d
      rw [h₁]
      exact ⟨_, rfl⟩)

theorem fixedInternalPathsLift_ι {K X : SSet.{0}} (x y : X _⦋0⦌)
    (a : K ⟶ internalPathObject X)
    (h₀ : a ≫ internalPathStart X = SSet.const x)
    (h₁ : a ≫ internalPathEnd X = SSet.const y) :
    fixedInternalPathsLift x y a h₀ h₁ ≫ (fixedInternalPathSubcomplex X x y).ι = a := rfl

/-- Fixed-endpoint internal path complexes of Kan complexes are Kan. The
proof fixes both ends throughout the actual horn lift. -/
theorem fixedInternalPaths_kan (X : SSet.{0}) [SSet.KanComplex X] (x y : X _⦋0⦌) :
    SSet.KanComplex (fixedInternalPaths X x y) := by
  apply (SSet.KanComplex.iff).mpr
  intro n j f hf
  let a := hf.desc ≫ (fixedInternalPathSubcomplex X x y).ι
  have ha₀ : SSet.ι₀ ≫ internalPathCylinder a = SSet.const x := by
    rw [internalPathCylinder_start, Category.assoc, fixedInternalPaths_start, SSet.comp_const]
  have ha₁ : SSet.ι₁ ≫ internalPathCylinder a = SSet.const y := by
    rw [internalPathCylinder_end, Category.assoc, fixedInternalPaths_end, SSet.comp_const]
  let p := terminal.from X
  let b : (Δ[n+1] : SSet.{0}) ⊗ Δ[1] ⟶ ⊤_ SSet.{0} := terminal.from _
  have hb₀ : SSet.ι₀ ≫ b = SSet.const (p.app _ x) := terminal.hom_ext _ _
  have hb₁ : SSet.ι₁ ≫ b = SSet.const (p.app _ y) := terminal.hom_ext _ _
  obtain ⟨e, hei, _, he₀, he₁⟩ := exists_kan_fixed_endpoint_lift
    (SSet.horn (n+1) j).ι (SSet.anodyneExtensions.horn_ι j) p x y
    (internalPathCylinder a) b ha₀ ha₁ hb₀ hb₁ (terminal.hom_ext _ _)
  let l := internalPathTranspose e
  have hl₀ : l ≫ internalPathStart X = SSet.const x := by
    rw [← internalPathCylinder_start, internalPathCylinder_transpose, he₀]
  have hl₁ : l ≫ internalPathEnd X = SSet.const y := by
    rw [← internalPathCylinder_end, internalPathCylinder_transpose, he₁]
  let q := fixedInternalPathsLift x y l hl₀ hl₁
  refine ⟨q, ?_⟩
  intro k hk
  apply (cancel_mono (fixedInternalPathSubcomplex X x y).ι).mp
  rw [Category.assoc, fixedInternalPathsLift_ι]
  have hl : (SSet.horn (n+1) j).ι ≫ l = a := by
    apply internalPathCylinder_injective _ X
    rw [internalPathCylinder_naturality, internalPathCylinder_transpose, hei]
  rw [← SSet.horn.ι_ι j k hk, Category.assoc, hl]
  dsimp [a]
  rw [← Category.assoc, SSet.horn.IsCompatible.ι_desc]

end

end Thomason.Construction

end

section

/-! # Maps of fixed-endpoint internal path complexes -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory MonoidalClosed
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

def fixedInternalPathMap {X Y : SSet.{0}} (p : X ⟶ Y) (x y : X _⦋0⦌) :
    fixedInternalPaths X x y ⟶ fixedInternalPaths Y (p.app _ x) (p.app _ y) :=
  fixedInternalPathsLift _ _
    ((fixedInternalPathSubcomplex X x y).ι ≫ (ihom (Δ[1] : SSet.{0})).map p)
    (by rw [Category.assoc, internalPathStart_naturality, ← Category.assoc,
        fixedInternalPaths_start, SSet.const_comp])
    (by rw [Category.assoc, internalPathEnd_naturality, ← Category.assoc,
        fixedInternalPaths_end, SSet.const_comp])

@[reassoc]
theorem fixedInternalPathMap_ι {X Y : SSet.{0}} (p : X ⟶ Y) (x y : X _⦋0⦌) :
    fixedInternalPathMap p x y ≫ (fixedInternalPathSubcomplex Y (p.app _ x) (p.app _ y)).ι =
      (fixedInternalPathSubcomplex X x y).ι ≫ (ihom (Δ[1] : SSet.{0})).map p := rfl

/-- A fibration gives exact relative lifts in its fixed-endpoint path map.
Only the anodyne pushout-product theorem is used. -/
theorem fixedInternalPathMap_lifting {X Y A B : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] (x y : X _⦋0⦌)
    (i : A ⟶ B) (hi : SSet.anodyneExtensions i) :
    HasLiftingProperty i (fixedInternalPathMap p x y) := by
  refine ⟨fun {a b} sq => ?_⟩
  let a' := a ≫ (fixedInternalPathSubcomplex X x y).ι
  let b' := b ≫ (fixedInternalPathSubcomplex Y (p.app _ x) (p.app _ y)).ι
  have ha₀ : SSet.ι₀ ≫ internalPathCylinder a' = SSet.const x := by
    rw [internalPathCylinder_start, Category.assoc, fixedInternalPaths_start, SSet.comp_const]
  have ha₁ : SSet.ι₁ ≫ internalPathCylinder a' = SSet.const y := by
    rw [internalPathCylinder_end, Category.assoc, fixedInternalPaths_end, SSet.comp_const]
  have hb₀ : SSet.ι₀ ≫ internalPathCylinder b' = SSet.const (p.app _ x) := by
    rw [internalPathCylinder_start, Category.assoc, fixedInternalPaths_start, SSet.comp_const]
  have hb₁ : SSet.ι₁ ≫ internalPathCylinder b' = SSet.const (p.app _ y) := by
    rw [internalPathCylinder_end, Category.assoc, fixedInternalPaths_end, SSet.comp_const]
  have hab : internalPathCylinder a' ≫ p = i ▷ Δ[1] ≫ internalPathCylinder b' := by
    rw [← internalPathCylinder_postcomp, ← internalPathCylinder_naturality]
    congr 1
    dsimp only [a', b']
    rw [Category.assoc, ← fixedInternalPathMap_ι, ← Category.assoc, sq.w, Category.assoc]
  obtain ⟨e, hei, hep, he₀, he₁⟩ := exists_kan_fixed_endpoint_lift i hi p x y
    (internalPathCylinder a') (internalPathCylinder b') ha₀ ha₁ hb₀ hb₁ hab
  let q := internalPathTranspose e
  have hq₀ : q ≫ internalPathStart X = SSet.const x := by
    rw [← internalPathCylinder_start, internalPathCylinder_transpose, he₀]
  have hq₁ : q ≫ internalPathEnd X = SSet.const y := by
    rw [← internalPathCylinder_end, internalPathCylinder_transpose, he₁]
  refine ⟨⟨{ l := fixedInternalPathsLift x y q hq₀ hq₁,
             fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply (cancel_mono (fixedInternalPathSubcomplex X x y).ι).mp
    rw [Category.assoc, fixedInternalPathsLift_ι]
    apply internalPathCylinder_injective
    rw [internalPathCylinder_naturality, internalPathCylinder_transpose, hei]
  · apply (cancel_mono (fixedInternalPathSubcomplex Y (p.app _ x) (p.app _ y)).ι).mp
    rw [Category.assoc, fixedInternalPathMap_ι, ← Category.assoc, fixedInternalPathsLift_ι]
    apply internalPathCylinder_injective
    rw [internalPathCylinder_postcomp, internalPathCylinder_transpose, hep]

theorem fixedInternalPathMap_fibration {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] (x y : X _⦋0⦌) :
    HomotopicalAlgebra.Fibration (fixedInternalPathMap p x y) := by
  rw [fibration_iff]
  intro A B i hi
  exact fixedInternalPathMap_lifting p x y i
    (MorphismProperty.le_llp_rlp J _ hi)

end

end Thomason.Construction

end

end OAI
