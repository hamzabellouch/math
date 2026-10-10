import OAI.CategoryTheory.Thomason.Chains.NormalizedCubicalLifting
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionCartesian
import OAI.CategoryTheory.Thomason.Simplicial.ConstructedPosetCosieves
import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetUnitInduction
import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift
import OAI.CategoryTheory.Thomason.Simplicial.PosetSieveNaturality
import OAI.CategoryTheory.Thomason.Simplicial.SingularAcyclicFibers
import OAI.CategoryTheory.Thomason.Simplicial.TopologicalDeformationTransport
import OAI.CategoryTheory.Thomason.Simplicial.TruncatedLocalPresentability
import OAI.CategoryTheory.Thomason.Transfer.FiniteStreetSievePushouts
import OAI.CategoryTheory.Thomason.Transfer.HornAttachmentWeakEquivalences
import OAI.CategoryTheory.Thomason.Transfer.SimplicialRangeGluing
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OAI

section

/-! # Discharging the finite-poset unit input

This proves the needed specialization of Gagna's unit theorem from the
constructed Gray contractions and the published full-sieve and simplicial
gluing inputs. Neither the unit theorem, the Thomason transfer conclusion,
nor a localization equivalence is used in the proof.
-/

namespace Thomason.Construction

open CategoryTheory

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The actual omega-categorification unit is weak on every finite poset. -/
theorem unit_finite_poset
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput) (kq : KanQuillenPublishedInput.{0})
    (P : Type) [PartialOrder P] [Finite P] :
    realizationWeakEquivalences (h.categorificationAdjunction.unit.app (nerve P)) := by
  have := kq.weakEquivalences_retracts
  refine finite_poset_comparison_induction h.categorificationAdjunction.unit g
    ?_ ?_ ?_ ?_ P
  · intro Q _ _
    have := h.unit_empty_isIso Q
    exact realizationWeakEquivalences.of_isIso _
  · intro Q _ x hx
    exact h.unit_greatestElement G aw kq x hx
  · intro Q _ _ A hA
    exact s.omega_nerve_mono A hA
  · intro Q _ _ A B hA hB hc
    exact h.street_sieve_maps_isPushout s A B hA hB hc

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The same comparison is weak in every positive finite strict dimension. -/
theorem unit_finite_poset
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput) (kq : KanQuillenPublishedInput.{0})
    (P : Type) [PartialOrder P] [Finite P] :
    realizationWeakEquivalences ((r.categorificationAdjunction h).unit.app (nerve P)) := by
  have := kq.weakEquivalences_retracts
  refine finite_poset_comparison_induction (r.categorificationAdjunction h).unit g
    ?_ ?_ ?_ ?_ P
  · intro Q _ _
    have := r.unit_empty_isIso h Q
    exact realizationWeakEquivalences.of_isIso _
  · intro Q _ x hx
    exact r.unit_greatestElement h G t aw kq x hx
  · intro Q _ _ A hA
    exact r.posetStreet_mono h s A hA
  · intro Q _ _ A B hA hB hc
    exact r.street_sieve_maps_isPushout h s A B hA hB hc

end FiniteReflectionInput

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The finite-poset unit comparison follows from the specified
simplicial and strict-category inputs. -/
theorem finitePosetUnitInput
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput) (kq : KanQuillenPublishedInput.{0}) :
    PublishedFinitePosetUnitInput h where
  omega P := h.unit_finite_poset G aw s g kq P
  finite _ r P := r.unit_finite_poset h G t aw s g kq P

end NormalizedSimplexIdentities
end Thomason.Construction

end

section

/-! # Finite-poset weak equivalences detected by strict categorification

The adjunction units identify the actual Kan–Quillen weak
equivalences with the actual Street weak equivalences on all maps between
finite-poset nerves. This uses neither a transferred model structure nor
the published localization theorem.
-/

namespace Thomason.Construction

open CategoryTheory

/-- The two unit components, rather than a global unit hypothesis, suffice
to compare a map with its image under the endofunctor. -/
theorem map_iff_of_unit_components {C : Type*} [Category* C]
    (W : MorphismProperty C) [W.HasTwoOutOfThreeProperty]
    {F : C ⥤ C} (η : 𝟭 C ⟶ F) {X Y : C} (f : X ⟶ Y)
    (hx : W (η.app X)) (hy : W (η.app Y)) : W (F.map f) ↔ W f := by
  have hn : f ≫ η.app Y = η.app X ≫ F.map f := η.naturality f
  constructor
  · intro hf
    apply W.of_postcomp f (η.app Y) hy
    rw [hn]
    exact W.comp_mem _ _ hx hf
  · intro hf
    apply W.of_precomp (η.app X) (F.map f) hx
    rw [← hn]
    exact W.comp_mem _ _ hf hy

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Categorification preserves and reflects the actual weak-equivalence
property on arbitrary simplicial maps between finite-poset nerves. -/
theorem finite_poset_map_weakEquivalence_iff
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput) (kq : KanQuillenPublishedInput.{0})
    {P Q : Type} [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q]
    (f : nerve P ⟶ nerve Q) :
    h.streetWeakEquivalences (h.categorification.map f) ↔ realizationWeakEquivalences f := by
  have : realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty := kq.twoOutOfThree
  exact map_iff_of_unit_components realizationWeakEquivalences
    h.categorificationAdjunction.unit f (h.unit_finite_poset G aw s g kq P)
    (h.unit_finite_poset G aw s g kq Q)

/-- The same equivalences are detected by the actual Thomason right adjoint Ex²N. -/
theorem finite_poset_map_extended_weakEquivalence_iff
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput) (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X : SSet.{0}, realizationWeakEquivalences (canonicalExtension.app X))
    {P Q : Type} [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q]
    (f : nerve P ⟶ nerve Q) :
    realizationWeakEquivalences (h.thomasonRight.map (h.categorification.map f)) ↔
      realizationWeakEquivalences f := by
  have : realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty := kq.twoOutOfThree
  exact (realization_ex_twice_iff hj (h.streetNerve.map (h.categorification.map f))).trans
    (h.finite_poset_map_weakEquivalence_iff G aw s g kq f)

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Finite reflection preserves and reflects these equivalences as well. -/
theorem finite_poset_map_weakEquivalence_iff
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput) (kq : KanQuillenPublishedInput.{0})
    {P Q : Type} [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q]
    (f : nerve P ⟶ nerve Q) :
    realizationWeakEquivalences ((h.finiteStreetNerve (n + 1)).map
      ((r.categorification h).map f)) ↔ realizationWeakEquivalences f := by
  have : realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty := kq.twoOutOfThree
  exact map_iff_of_unit_components realizationWeakEquivalences
    (r.categorificationAdjunction h).unit f (r.unit_finite_poset h G t aw s g kq P)
    (r.unit_finite_poset h G t aw s g kq Q)

/-- Ex² of the finite Street nerve gives the same test on these maps. -/
theorem finite_poset_map_extended_weakEquivalence_iff
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput) (kq : KanQuillenPublishedInput.{0})
    (hj : ∀ X : SSet.{0}, realizationWeakEquivalences (canonicalExtension.app X))
    {P Q : Type} [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q]
    (f : nerve P ⟶ nerve Q) :
    realizationWeakEquivalences ((h.finiteStreetNerve (n + 1) ⋙ SSet.ex ⋙ SSet.ex).map
      ((r.categorification h).map f)) ↔ realizationWeakEquivalences f := by
  have : realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty := kq.twoOutOfThree
  exact (realization_ex_twice_iff hj ((h.finiteStreetNerve (n + 1)).map
    ((r.categorification h).map f))).trans
      (r.finite_poset_map_weakEquivalence_iff h G t aw s g kq f)

end FiniteReflectionInput
end Thomason.Construction

end

section

/-! # Weak equivalences of actual full sieve fibres

The natural full-fibre identification compares the original strict
restriction with the ordinary restricted poset map. Finite-poset units
then identify its Street weak equivalences with geometric-realization
weak equivalences of that ordinary nerve. No transfer or localization
conclusion is used.
-/

namespace Thomason.Construction.SieveMap

open CategoryTheory

variable {P Q : Type} [PartialOrder P] [PartialOrder Q]
  (A : Set P) (B : Set Q) (f : P →o Q) (hf : ∀ x, f x ∈ B ↔ x ∈ A)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]
  (hA : IsLowerSet A) (hB : IsLowerSet B)

/-- The actual fibre map and the categorified restricted map have the same
Street weak-equivalence property. -/
theorem fiberMap_weak_iff :
    h.streetWeakEquivalences (fiberMap A B f hf h hA hB) ↔
      h.streetWeakEquivalences (h.posetMap (restriction A B f hf)) := by
  have : IsIso (h.posetFiberMap A hA) := (h.posetSieveIso A hA).isIso_hom
  have : IsIso (h.posetFiberMap B hB) := (h.posetSieveIso B hB).isIso_hom
  let i := h.streetNerve.map (h.posetFiberMap A hA)
  let j := h.streetNerve.map (h.posetFiberMap B hB)
  let u := h.streetNerve.map (fiberMap A B f hf h hA hB)
  let v := h.streetNerve.map (h.posetMap (restriction A B f hf))
  have hn : i ≫ u = v ≫ j := by
    exact (h.streetNerve.map_comp _ _).symm.trans
      ((congrArg h.streetNerve.map (naturality A B f hf h hA hB)).trans
        (h.streetNerve.map_comp _ _))
  change realizationWeakEquivalences u ↔ realizationWeakEquivalences v
  calc
    _ ↔ realizationWeakEquivalences (i ≫ u) :=
      (realizationWeakEquivalences.cancel_left_of_respectsIso i u).symm
    _ ↔ realizationWeakEquivalences (v ≫ j) := by rw [hn]
    _ ↔ _ := realizationWeakEquivalences.cancel_right_of_respectsIso v j

/-- For finite posets the full-fibre map is weak exactly when the ordinary
restricted poset nerve is a Kan–Quillen weak equivalence. -/
theorem fiberMap_weak_iff_nerve [Finite P] [Finite Q]
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (kq : KanQuillenPublishedInput.{0}) :
    h.streetWeakEquivalences (fiberMap A B f hf h hA hB) ↔
      realizationWeakEquivalences (nerveMap (restriction A B f hf).monotone.functor) :=
  (fiberMap_weak_iff A B f hf h hA hB).trans
    (h.finite_poset_map_weakEquivalence_iff G aw
      h.constructedOmegaPosetSieveInput.allDimensions (constructedSimplicialGluing kq) kq _)

end Thomason.Construction.SieveMap

end

section

/-! # Full acyclic boundary lifting on actual finite cubes -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- A singular Kan fibration which is an actual weak equivalence lifts
arbitrary cubical boundary squares in every positive dimension. -/
theorem singular_fibration_boundary_lifting (n : ℕ) {X Y : TopCat.{0}}
    (p : X ⟶ Y) [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) :
    HasLiftingProperty (boundaryInclusion n) p := by
  induction n generalizing X Y with
  | zero => exact singular_fibration_interval_boundary_lifting p hp
  | succ n ih =>
    refine ⟨fun {a b} sq => ?_⟩
    have hab (z : Cube.boundary (Fin (n+2))) : p.hom (a.hom z) = b.hom z.val :=
      congrArg (fun f => f.hom z) sq.w
    obtain ⟨F, B, hF₀, hB₀, hFB, hFe⟩ := boundary_square_normalization p (n+1) a.hom b.hom hab
    let x₀ := a.hom (boundaryFacePoint (n+1) false (fun _ => 0))
    let x₁ := a.hom (boundaryFacePoint (n+1) true (fun _ => 0))
    let P : TopCat.of (Path x₀ x₁) ⟶ TopCat.of (Path (p.hom x₀) (p.hom x₁)) :=
      TopCat.ofHom (PathSpace.map p.hom)
    let : HomotopicalAlgebra.Fibration (TopCat.toSSet.map P) :=
      fixedPath_singular_fibration p x₀ x₁
    have hP : IsWeakHomotopyEquivalence P.hom := PathSpace.map_weak p.hom hp x₀ x₁
    let a₁ : C(Cube.boundary (Fin (n+2)), X) :=
      ⟨fun z => F (1, z), F.continuous.comp (by fun_prop)⟩
    let b₁ : C(Fin (n+2) → unitInterval, Y) :=
      ⟨fun z => B (1, z), B.continuous.comp (by fun_prop)⟩
    obtain ⟨l, hl, hlp⟩ := normalized_cube_lift p n (ih P hP) a₁ b₁
      (hFe false) (hFe true) (hFB 1)
    let A' : C(unitInterval × Cube.boundary (Fin (n+2)), X) :=
      F.comp ⟨fun z => (unitInterval.symm z.1, z.2), by fun_prop⟩
    let B' : C(unitInterval × (Fin (n+2) → unitInterval), Y) :=
      B.comp ⟨fun z => (unitInterval.symm z.1, z.2), by fun_prop⟩
    have hA₀ (z : Cube.boundary (Fin (n+2))) : A' (0, z) = l z.val := by
      change F (unitInterval.symm 0, z) = l z.val
      simpa [a₁] using (hl z).symm
    have hAB (t : unitInterval) (z : Cube.boundary (Fin (n+2))) :
        p.hom (A' (t, z)) = B' (t, z.val) := hFB (unitInterval.symm t) z
    have hl₀ (z : Fin (n+2) → unitInterval) : p.hom (l z) = B' (0, z) := by
      simpa [B', b₁] using hlp z
    obtain ⟨L, _, hLA, hLp⟩ := singular_fibration_cube_lifting p (n+1) l A' B' hA₀ hAB hl₀
    let l' : TopCat.of (Fin (n+2) → unitInterval) ⟶ X :=
      TopCat.ofHom ⟨fun z => L (1, z), L.continuous.comp (by fun_prop)⟩
    refine ⟨⟨{ l := l', fac_left := ?_, fac_right := ?_ }⟩⟩
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      change L (1, z.val) = a.hom z
      rw [hLA]
      change F (unitInterval.symm 1, z) = a.hom z
      simpa using hF₀ z
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      change p.hom (L (1, z)) = b.hom z
      rw [hLp]
      change B (unitInterval.symm 1, z) = b.hom z
      simpa using hB₀ z

/-- The full cubical lifting conclusion under the original singular-realization
weak-equivalence hypothesis, with no constant-boundary restriction. -/
theorem singular_acyclic_boundary_lifting (n : ℕ) {X Y : TopCat.{0}}
    (p : X ⟶ Y) [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : realizationWeakEquivalences (TopCat.toSSet.map p)) :
    HasLiftingProperty (boundaryInclusion n) p :=
  singular_fibration_boundary_lifting n p (singular_realization_reflects_weak p hp)

end

end Thomason.Construction.RealizedCube

end

section

/-! # The finite convex bodies underlying simplex/cube boundary transport -/

namespace Thomason.Construction.SimplexPolytopes

open Set Topology Convexity

noncomputable section

def cube (n : ℕ) : Set (Fin (n+1) → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc 0 1)

def simplex (n : ℕ) : Set (Fin (n+1) → ℝ) :=
  Set.univ.pi (fun _ => Set.Ici 0) ∩ {x | ∑ i, x i ≤ 1}

def sumMap (n : ℕ) : (Fin (n+1) → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' a x := by simp [Finset.mul_sum]

theorem sumMap_surjective (n : ℕ) : Function.Surjective (sumMap n) := by
  intro a
  refine ⟨Pi.single 0 a, ?_⟩
  simp [sumMap, Pi.single_apply]

theorem cube_convex (n : ℕ) : Convex ℝ (cube n) :=
  convex_pi (fun _ _ => convex_Icc 0 1)

theorem simplex_convex (n : ℕ) : Convex ℝ (simplex n) := by
  apply Convex.inter (convex_pi (fun _ _ => convex_Ici 0))
  exact (convex_Iic (1 : ℝ)).linear_preimage (sumMap n)

theorem cube_closed (n : ℕ) : IsClosed (cube n) :=
  isClosed_set_pi (fun _ _ => isClosed_Icc)

theorem simplex_closed (n : ℕ) : IsClosed (simplex n) :=
  (isClosed_set_pi (fun _ _ => isClosed_Ici)).inter (isClosed_le (by fun_prop) continuous_const)

theorem cube_compact (n : ℕ) : IsCompact (cube n) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem simplex_subset_cube (n : ℕ) : simplex n ⊆ cube n := by
  intro x hx i _
  refine ⟨hx.1 i (Set.mem_univ i), le_trans ?_ hx.2⟩
  exact Finset.single_le_sum (fun j _ => hx.1 j (Set.mem_univ j)) (Finset.mem_univ i)

theorem simplex_compact (n : ℕ) : IsCompact (simplex n) :=
  (cube_compact n).of_isClosed_subset (simplex_closed n) (simplex_subset_cube n)

theorem cube_interior (n : ℕ) : interior (cube n) =
    Set.univ.pi (fun _ => Set.Ioo 0 1) := by
  rw [cube, interior_pi_set Set.finite_univ]
  simp only [interior_Icc]

theorem simplex_interior (n : ℕ) : interior (simplex n) =
    Set.univ.pi (fun _ => Set.Ioi 0) ∩ {x | ∑ i, x i < 1} := by
  rw [simplex, interior_inter, interior_pi_set Set.finite_univ]
  simp only [interior_Ici]
  have he := (sumMap n).isOpenMap_of_finiteDimensional (sumMap_surjective n)
  have hc : Continuous (sumMap n) := by fun_prop
  have h := he.preimage_interior_eq_interior_preimage hc (Set.Iic (1 : ℝ))
  rw [interior_Iic] at h
  change {x : Fin (n+1) → ℝ | ∑ i, x i < 1} =
    interior {x : Fin (n+1) → ℝ | ∑ i, x i ≤ 1} at h
  rw [← h]

theorem cube_interior_nonempty (n : ℕ) : (interior (cube n)).Nonempty := by
  rw [cube_interior]
  exact ⟨fun _ => 1/2, fun _ _ => by constructor <;> norm_num⟩

theorem simplex_interior_nonempty (n : ℕ) : (interior (simplex n)).Nonempty := by
  rw [simplex_interior]
  have hd : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  refine ⟨fun _ => 1 / ((n : ℝ)+2), ⟨fun _ _ => ?_, ?_⟩⟩
  · change 0 < 1 / ((n : ℝ)+2)
    positivity
  change (∑ _ : Fin (n+1), 1 / ((n : ℝ)+2)) < 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_one_div, div_lt_one hd]
  push_cast
  linarith

/-- The ambient radial comparison carries both bodies and their boundaries. -/
theorem exists_pair_homeomorph (n : ℕ) :
    ∃ e : (Fin (n+1) → ℝ) ≃ₜ (Fin (n+1) → ℝ),
      e '' simplex n = cube n ∧ e '' frontier (simplex n) = frontier (cube n) := by
  obtain ⟨e, _, he, hb⟩ := exists_homeomorph_image_eq
    (simplex_convex n) (simplex_interior_nonempty n) ((simplex_compact n).isVonNBounded (𝕜 := ℝ))
    (cube_convex n) (cube_interior_nonempty n) ((cube_compact n).isVonNBounded (𝕜 := ℝ))
  rw [(simplex_closed n).closure_eq, (cube_closed n).closure_eq] at he
  exact ⟨e, he, hb⟩

end

end Thomason.Construction.SimplexPolytopes

end

section

/-! # Coordinate homeomorphisms for finite simplex and cube polytopes -/

namespace Thomason.Construction.SimplexPolytopes

open Set Topology Convexity

noncomputable section

/-- Omit the first barycentric coordinate. Its value is recovered by the sum. -/
def simplexCoordinates (n : ℕ) : StdSimplex ℝ (Fin (n+2)) ≃ₜ simplex n where
  toFun s := ⟨fun i => s.weights i.succ, by
    refine ⟨fun i _ => s.weights_nonneg i.succ, ?_⟩
    have hs := s.total_of_fintype
    rw [Fin.sum_univ_succ] at hs
    have h0 := s.weights_nonneg 0
    change (∑ i : Fin (n+1), s.weights i.succ) ≤ 1
    linarith⟩
  invFun x := {
    weights := Finsupp.equivFunOnFinite.symm (Fin.cons (α := fun _ => ℝ) (1 - ∑ i, x.val i) x.val)
    nonneg := by
      intro i
      change 0 ≤ Fin.cons (α := fun _ => ℝ) (1 - ∑ i, x.val i) x.val i
      cases i using Fin.cases with
      | zero => exact sub_nonneg.mpr x.property.2
      | succ i => exact x.property.1 i (mem_univ i)
    total := by
      rw [Finsupp.sum_fintype _ _ (by intro; rfl)]
      change (∑ i, Fin.cons (α := fun _ => ℝ) (1 - ∑ j, x.val j) x.val i) = 1
      rw [Fin.sum_univ_succ]
      simp }
  left_inv s := by
    apply StdSimplex.ext
    apply Finsupp.ext
    intro i
    change Fin.cons (α := fun _ => ℝ) (1 - ∑ j : Fin (n+1), s.weights j.succ) (fun j => s.weights j.succ) i = s.weights i
    cases i using Fin.cases with
    | zero =>
      have hs := s.total_of_fintype
      rw [Fin.sum_univ_succ] at hs
      change 1 - ∑ j : Fin (n+1), s.weights j.succ = s.weights 0
      linarith
    | succ i => rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff.mpr
    change Continuous (fun x : simplex n => Fin.cons (α := fun _ => ℝ) (1 - ∑ i, x.val i) x.val)
    fun_prop

/-- The product of closed unit intervals is exactly the coordinate box. -/
def cubeCoordinates (n : ℕ) : (Fin (n+1) → unitInterval) ≃ₜ cube n where
  toFun u := ⟨fun i => (u i : ℝ), fun i _ => (u i).property⟩
  invFun u := fun i => ⟨u.val i, u.property i (mem_univ i)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

/-- Barycentric zeros are exactly the topological frontier of the solid simplex. -/
theorem simplexCoordinates_boundary (n : ℕ) (s : StdSimplex ℝ (Fin (n+2))) :
    s ∈ RealizationPrism.boundaryLocus (n+1) ↔
      (simplexCoordinates n s).val ∈ frontier (simplex n) := by
  rw [frontier, (simplex_closed n).closure_eq]
  change (∃ i, s.weights i = 0) ↔ _
  rw [Set.mem_sdiff, simplex_interior]
  simp only [(simplexCoordinates n s).property, true_and]
  have hs := s.total_of_fintype
  rw [Fin.sum_univ_succ] at hs
  constructor
  · rintro ⟨i, hi⟩ h
    cases i using Fin.cases with
    | zero =>
      have hsum : (∑ j : Fin (n+1), s.weights j.succ) < 1 := h.2
      change s.weights 0 = 0 at hi
      linarith
    | succ i =>
      have hp : 0 < s.weights i.succ := h.1 i (mem_univ i)
      linarith
  · intro h
    by_contra hz
    have hp (i) : 0 < s.weights i :=
      lt_of_le_of_ne (s.weights_nonneg i) (Ne.symm (fun he => hz ⟨i, he⟩))
    apply h
    refine ⟨fun i _ => hp i.succ, ?_⟩
    change (∑ j : Fin (n+1), s.weights j.succ) < 1
    linarith [hp 0]

/-- Endpoint coordinates are exactly the topological frontier of the box. -/
theorem cubeCoordinates_boundary (n : ℕ) (u : Fin (n+1) → unitInterval) :
    u ∈ Cube.boundary (Fin (n+1)) ↔
      (cubeCoordinates n u).val ∈ frontier (cube n) := by
  rw [frontier, (cube_closed n).closure_eq, Set.mem_sdiff, cube_interior]
  simp only [(cubeCoordinates n u).property, true_and]
  constructor
  · rintro ⟨i, hi | hi⟩ h
    · have hp : 0 < (u i : ℝ) := (h i (mem_univ i)).1
      rw [hi] at hp
      exact lt_irrefl 0 hp
    · have hp : (u i : ℝ) < 1 := (h i (mem_univ i)).2
      rw [hi] at hp
      exact lt_irrefl 1 hp
  · intro h
    by_contra hz
    apply h
    intro i _
    have h0 : u i ≠ 0 := fun he => hz ⟨i, Or.inl he⟩
    have h1 : u i ≠ 1 := fun he => hz ⟨i, Or.inr he⟩
    exact ⟨lt_of_le_of_ne (u i).property.1 (by
      intro he
      exact h0 (Subtype.ext he.symm)),
      lt_of_le_of_ne (u i).property.2 (by
        intro he
        exact h1 (Subtype.ext he))⟩

end

end Thomason.Construction.SimplexPolytopes

end

section

/-! # A homeomorphism of the entire simplex/cube boundary-inclusion pairs -/

namespace Thomason.Construction.SimplexPolytopes

open CategoryTheory Set Topology Convexity

noncomputable section

def ambientHomeomorph (n : ℕ) : (Fin (n+1) → ℝ) ≃ₜ (Fin (n+1) → ℝ) :=
  (exists_pair_homeomorph n).choose

theorem ambientHomeomorph_body (n : ℕ) :
    ambientHomeomorph n '' simplex n = cube n :=
  (exists_pair_homeomorph n).choose_spec.1

theorem ambientHomeomorph_boundary (n : ℕ) :
    ambientHomeomorph n '' frontier (simplex n) = frontier (cube n) :=
  (exists_pair_homeomorph n).choose_spec.2

def bodyHomeomorph (n : ℕ) : simplex n ≃ₜ cube n :=
  ((ambientHomeomorph n).image (simplex n)).trans
    (Homeomorph.setCongr (ambientHomeomorph_body n))

def simplexCubeHomeomorph (n : ℕ) :
    StdSimplex ℝ (Fin (n+2)) ≃ₜ (Fin (n+1) → unitInterval) :=
  (simplexCoordinates n).trans ((bodyHomeomorph n).trans (cubeCoordinates n).symm)

theorem simplexCubeHomeomorph_boundary (n : ℕ) (s : StdSimplex ℝ (Fin (n+2))) :
    s ∈ RealizationPrism.boundaryLocus (n+1) ↔
      simplexCubeHomeomorph n s ∈ Cube.boundary (Fin (n+1)) := by
  have ha (x : Fin (n+1) → ℝ) : x ∈ frontier (simplex n) ↔
      ambientHomeomorph n x ∈ frontier (cube n) := by
    rw [← ambientHomeomorph_boundary]
    exact ((ambientHomeomorph n).injective.mem_set_image).symm
  have hc := cubeCoordinates_boundary n (simplexCubeHomeomorph n s)
  have he : (cubeCoordinates n (simplexCubeHomeomorph n s)).val =
      ambientHomeomorph n (simplexCoordinates n s).val :=
    congrArg Subtype.val ((cubeCoordinates n).apply_symm_apply
      (bodyHomeomorph n (simplexCoordinates n s)))
  rw [he] at hc
  exact (simplexCoordinates_boundary n s).trans ((ha _).trans hc.symm)

/-- Transport of lifting problems retains the entire boundary on both sides. -/
def boundaryArrowIso (n : ℕ) :
    Arrow.mk (RealizationPrism.boundaryInclusion (n+1)) ≅
      Arrow.mk (RealizedCube.boundaryInclusion n) :=
  Arrow.isoMk' _ _
    (TopCat.isoOfHomeo ((simplexCubeHomeomorph n).subtype
      (simplexCubeHomeomorph_boundary n)))
    (TopCat.isoOfHomeo (simplexCubeHomeomorph n)) (by rfl)

end

end Thomason.Construction.SimplexPolytopes

end

section

/-! # All singular acyclic boundary lifts, with no published comparison input -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- The full boundary lift from the actual topological weak-equivalence test. -/
theorem singular_fibration_boundary_lifting {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) (n : ℕ) :
    HasLiftingProperty (SSet.boundary n).ι (TopCat.toSSet.map p) := by
  cases n with
  | zero =>
    exact singular_boundary_zero_lifting_of_surjective p
      (singular_fibration_surjective_of_weak p hp)
  | succ n =>
    apply (RealizationPrism.singular_boundary_lifting_iff p (n+1)).mpr
    exact (HasLiftingProperty.iff_of_arrow_iso_left
      (SimplexPolytopes.boundaryArrowIso n) p).mpr
        (RealizedCube.singular_fibration_boundary_lifting n p hp)

/-- Actual weak equivalences with singular Kan lifting have the boundary rlp. -/
theorem singular_fibration_boundary_rlp {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) :
    SSet.modelCategoryQuillen.I.rlp (TopCat.toSSet.map p) := by
  rintro A B i ⟨n⟩
  exact singular_fibration_boundary_lifting p hp n

/-- The actual singular Kan fibration associated to a realization-weak map
has the full boundary right lifting property in every simplicial degree. -/
theorem singular_acyclic_boundary_lifting {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : realizationWeakEquivalences (TopCat.toSSet.map p)) (n : ℕ) :
    HasLiftingProperty (SSet.boundary n).ι (TopCat.toSSet.map p) := by
  cases n with
  | zero => exact singular_acyclic_boundary_zero p hp
  | succ n =>
    apply (RealizationPrism.singular_boundary_lifting_iff p (n+1)).mpr
    exact (HasLiftingProperty.iff_of_arrow_iso_left
      (SimplexPolytopes.boundaryArrowIso n) p).mpr
        (RealizedCube.singular_acyclic_boundary_lifting n p hp)

/-- The singular specialization of the acyclic Kan implication, stated for
its actual generating boundary class. General simplicial maps remain separate. -/
theorem singular_acyclic_boundary_rlp {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : realizationWeakEquivalences (TopCat.toSSet.map p)) :
    SSet.modelCategoryQuillen.I.rlp (TopCat.toSSet.map p) := by
  rintro A B i ⟨n⟩
  exact singular_acyclic_boundary_lifting p hp n

/-- On actual singular Kan fibrations, singular realization preserves and
reflects the topological weak-equivalence test. No counit-W input is used. -/
theorem singular_fibration_weak_iff {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)] :
    realizationWeakEquivalences (TopCat.toSSet.map p) ↔
      IsWeakHomotopyEquivalence p.hom := by
  constructor
  · exact singular_realization_reflects_weak p
  · intro hp
    exact boundary_rlp_weak _ (singular_fibration_boundary_rlp p hp)

/-- Acyclic singular fibrations lift against every actual realized simplicial
monomorphism, keeping the whole prescribed subcomplex map exactly fixed. -/
theorem singular_fibration_realization_mono_lifting {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) {K L : SSet.{0}} (i : K ⟶ L) [Mono i] :
    HasLiftingProperty (SSet.toTop.map i) p := by
  apply RealizationPrism.realization_mono_lifting p _ i
  intro n
  exact (RealizationPrism.singular_boundary_lifting_iff p n).mp
    (singular_fibration_boundary_lifting p hp n)

end

end Thomason.Construction

end

section

/-! # Exact extension into actual fibres over realized simplicial subobjects -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- Any map from a realized simplicial subobject to a point fibre of an
acyclic singular fibration extends inside that same actual point fibre. -/
theorem singular_fibration_fiber_extension {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)]
    (hp : IsWeakHomotopyEquivalence p.hom) (y : Y)
    {K L : SSet.{0}} (i : K ⟶ L) [Mono i]
    (a : SSet.toTop.obj K ⟶ TopCat.of {x : X // p.hom x = y}) :
    ∃ g : SSet.toTop.obj L ⟶ TopCat.of {x : X // p.hom x = y},
      SSet.toTop.map i ≫ g = a := by
  let a' : SSet.toTop.obj K ⟶ X :=
    TopCat.ofHom ⟨fun z => (a.hom z).val, a.hom.continuous.subtype_val⟩
  let b : SSet.toTop.obj L ⟶ Y := TopCat.ofHom (ContinuousMap.const _ y)
  have sq : CommSq a' (SSet.toTop.map i) p b := by
    constructor
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    exact (a.hom z).property
  let : HasLiftingProperty (SSet.toTop.map i) p :=
    singular_fibration_realization_mono_lifting p hp i
  let g : SSet.toTop.obj L ⟶ TopCat.of {x : X // p.hom x = y} := TopCat.ofHom {
    toFun z := ⟨sq.lift.hom z, congrArg (fun f => f.hom z) sq.fac_right⟩
    continuous_toFun := sq.lift.hom.continuous.subtype_mk
      (fun z => congrArg (fun f => f.hom z) sq.fac_right) }
  refine ⟨g, ?_⟩
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact congrArg (fun f => f.hom z) sq.fac_left

end

end Thomason.Construction

end

section

/-! # Subdivision and unions inside a standard simplex -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

/-- The subdivision of a subcomplex, mapped to the standard finite-chain nerve. -/
def subdivisionInclusion {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    SSet.sd.obj (A : SSet) ⟶ SimplexCategory.sd.obj ⦋n⦌ :=
  SSet.sd.map A.ι ≫ SSet.stdSimplex.sdIso.hom.app ⦋n⦌

theorem subdivisionInclusion_fac {n : ℕ} {A B : (Δ[n] : SSet.{0}).Subcomplex}
    (h : A ≤ B) :
    SSet.sd.map (SSet.Subcomplex.homOfLE h) ≫ subdivisionInclusion B =
      subdivisionInclusion A := by
  rw [subdivisionInclusion, ← Category.assoc, ← SSet.sd.map_comp]
  rfl

/-- Subdivision assembles a union injectively when its two images meet in the
already constructed subdivision of their intersection. -/
theorem subdivision_union_mono_range {n : ℕ}
    (A B : (Δ[n] : SSet.{0}).Subcomplex)
    (ha : Mono (subdivisionInclusion A)) (hb : Mono (subdivisionInclusion B))
    (hi : Mono (subdivisionInclusion (A ⊓ B)))
    (he : SSet.Subcomplex.range (subdivisionInclusion (A ⊓ B)) =
      SSet.Subcomplex.range (subdivisionInclusion A) ⊓
        SSet.Subcomplex.range (subdivisionInclusion B)) :
    Mono (subdivisionInclusion (A ⊔ B)) ∧
      SSet.Subcomplex.range (subdivisionInclusion (A ⊔ B)) =
        SSet.Subcomplex.range (subdivisionInclusion A) ⊔
          SSet.Subcomplex.range (subdivisionInclusion B) := by
  have sq : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) := ⟨rfl, rfl⟩
  have hp := sq.isPushout.map SSet.sd
  have hf := subdivisionInclusion_fac (show A ⊓ B ≤ A from inf_le_left)
  have : Mono (SSet.sd.map (SSet.Subcomplex.homOfLE (show A ⊓ B ≤ A from inf_le_left)) ≫
      subdivisionInclusion A) := by rw [hf]; exact hi
  refine ⟨simplicial_pushout_comparison_mono hp (subdivisionInclusion (A ⊔ B))
    (subdivisionInclusion A) (subdivisionInclusion B)
    (subdivisionInclusion_fac le_sup_left) (subdivisionInclusion_fac le_sup_right) ?_, ?_⟩
  · rwa [hf]
  · exact simplicial_pushout_comparison_range hp (subdivisionInclusion (A ⊔ B))
      (subdivisionInclusion A) (subdivisionInclusion B)
      (subdivisionInclusion_fac le_sup_left) (subdivisionInclusion_fac le_sup_right)

def faceUnion {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    (Δ[n] : SSet.{0}).Subcomplex := F.sup SSet.stdSimplex.face

def subdividedFaceUnion {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    (SimplexCategory.sd.obj ⦋n⦌).Subcomplex := F.sup subdividedFace


private theorem subcomplex_finsetSup_inf {X : SSet.{0}} {ι : Type}
    (F : Finset ι) (f : ι → X.Subcomplex) (A : X.Subcomplex) :
    F.sup f ⊓ A = F.sup (fun i => f i ⊓ A) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    change (⊥ : X.Subcomplex) ⊓ A = ⊥
    exact bot_inf_eq A
  | @insert i F hi ih =>
    rw [Finset.sup_insert, Finset.sup_insert, ← ih]
    ext d x
    exact or_and_right

theorem faceUnion_inter_face {n : ℕ} (F : Finset (Finset (Fin (n+1))))
    (S : Finset (Fin (n+1))) :
    faceUnion F ⊓ SSet.stdSimplex.face S = faceUnion (F.image (fun T => T ∩ S)) := by
  classical
  calc
    _ = F.sup (fun T => SSet.stdSimplex.face T ⊓ SSet.stdSimplex.face S) :=
      subcomplex_finsetSup_inf F SSet.stdSimplex.face (SSet.stdSimplex.face S)
    _ = F.sup (fun T => SSet.stdSimplex.face (T ∩ S)) := by
      apply Finset.sup_congr rfl
      intro T _
      exact SSet.stdSimplex.face_inter_face T S
    _ = _ := (Finset.sup_image F (f := fun T => T ∩ S) (g := SSet.stdSimplex.face)).symm

theorem subdividedFaceUnion_inter_face {n : ℕ} (F : Finset (Finset (Fin (n+1))))
    (S : Finset (Fin (n+1))) :
    subdividedFaceUnion F ⊓ subdividedFace S =
      subdividedFaceUnion (F.image (fun T => T ∩ S)) := by
  classical
  calc
    _ = F.sup (fun T => subdividedFace T ⊓ subdividedFace S) :=
      subcomplex_finsetSup_inf F subdividedFace (subdividedFace S)
    _ = F.sup (fun T => subdividedFace (T ∩ S)) := by
      apply Finset.sup_congr rfl
      intro T _
      exact subdividedFace_inter T S
    _ = _ := (Finset.sup_image F (f := fun T => T ∩ S) (g := subdividedFace)).symm

private theorem finiteFaceUnion_mono_range_aux {n : ℕ} (k : ℕ) :
    ∀ F : Finset (Finset (Fin (n+1))), F.card = k →
      Mono (subdivisionInclusion (faceUnion F)) ∧
      SSet.Subcomplex.range (subdivisionInclusion (faceUnion F)) =
        subdividedFaceUnion F := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro F hF
    rcases F.eq_empty_or_nonempty with rfl | hne
    · have he : faceUnion (∅ : Finset (Finset (Fin (n+1)))) =
          SSet.stdSimplex.face (∅ : Finset (Fin (n+1))) := by
        change (⊥ : (Δ[n] : SSet.{0}).Subcomplex) = _
        exact (SSet.stdSimplex.face_empty n).symm
      rw [he]
      exact ⟨subdividedFaceMap_mono _, by
        change SSet.Subcomplex.range (subdividedFaceMap _) = ⊥
        rw [subdividedFaceMap_range, subdividedFace_empty]⟩
    · obtain ⟨S, hS⟩ := hne
      let G := F.erase S
      have hk : G.card < k := by
        rw [← hF]
        exact Finset.card_erase_lt_of_mem hS
      have hG := ih G.card hk G rfl
      let H := G.image (fun T => T ∩ S)
      have hH := ih H.card
        (lt_of_le_of_lt (Finset.card_image_le) hk) H rfl
      have hI : Mono (subdivisionInclusion (faceUnion G ⊓ SSet.stdSimplex.face S)) := by
        rw [faceUnion_inter_face]
        exact hH.1
      have hrS : SSet.Subcomplex.range (subdivisionInclusion (SSet.stdSimplex.face S)) =
          subdividedFace S := subdividedFaceMap_range S
      have he : SSet.Subcomplex.range
          (subdivisionInclusion (faceUnion G ⊓ SSet.stdSimplex.face S)) =
          SSet.Subcomplex.range (subdivisionInclusion (faceUnion G)) ⊓
            SSet.Subcomplex.range (subdivisionInclusion (SSet.stdSimplex.face S)) := by
        rw [faceUnion_inter_face, hH.2, hG.2, hrS]
        exact (subdividedFaceUnion_inter_face G S).symm
      have hc := subdivision_union_mono_range (faceUnion G) (SSet.stdSimplex.face S)
        hG.1 (subdividedFaceMap_mono S) hI he
      have hfg : F = insert S G := (Finset.insert_erase hS).symm
      have hf : faceUnion F = faceUnion G ⊔ SSet.stdSimplex.face S := by
        rw [hfg]
        simp only [faceUnion, Finset.sup_insert, sup_comm]
      have hsf : subdividedFaceUnion F = subdividedFaceUnion G ⊔ subdividedFace S := by
        rw [hfg]
        simp only [subdividedFaceUnion, Finset.sup_insert, sup_comm]
      rw [hf]
      exact ⟨hc.1, by rw [hc.2, hG.2, hrS, hsf]⟩

/-- Every finite union of original faces subdivides as the literal union of
its finite-chain faces, with an injective comparison to the ambient simplex. -/
theorem finiteFaceUnion_mono_range {n : ℕ} (F : Finset (Finset (Fin (n+1)))) :
    Mono (subdivisionInclusion (faceUnion F)) ∧
      SSet.Subcomplex.range (subdivisionInclusion (faceUnion F)) = subdividedFaceUnion F :=
  finiteFaceUnion_mono_range_aux F.card F rfl

end

end Thomason.Construction

end

end OAI
