import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift
import OAI.CategoryTheory.Thomason.Simplicial.RealizationSubcomplexSemantics
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Separation.Regular

namespace OAI

section

/-! # Nondegenerate barycentric coordinates of a realization point -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory CategoryTheory.Limits Convexity Opposite
open scoped Simplicial

noncomputable section

/-- A nondegenerate simplex with its barycentric coordinates. -/
abbrev NondegenerateCoordinates (K : SSet.{0}) :=
  Σ s : K.N, StdSimplex ℝ (Fin (s.dim+1))

/-- Remove degeneracies from a simplex and push forward its barycentric coordinates. -/
def normalizeSimplex (K : SSet.{0}) {n : ℕ} (s : K.obj (.op (.mk n)))
    (x : StdSimplex ℝ (Fin (n+1))) : NondegenerateCoordinates K :=
  ⟨(SSet.S.mk s).toN, StdSimplex.map (SSet.S.mk s).toNπ.toOrderHom x⟩

/-- Any nondegenerate epimorphic presentation computes the same normalization. -/
theorem normalizeSimplex_of_representation (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1)))
    (c : K.N) (f : SimplexCategory.mk n ⟶ .mk c.dim) [Epi f]
    (h : K.map f.op c.simplex = s) :
    normalizeSimplex K s x = ⟨c, StdSimplex.map f.toOrderHom x⟩ := by
  have hc : (SSet.S.mk s).toN = c := by
    apply SSet.S.toN_eq_iff.mpr
    change SSet.Subcomplex.ofSimplex c.simplex = SSet.Subcomplex.ofSimplex s
    rw [← h, SSet.Subcomplex.ofSimplex_map_of_epi]
  subst c
  have hf : (SSet.S.mk s).toNπ = f := by
    apply (SSet.S.existsUnique_toNπ (x := SSet.S.mk s) rfl).unique
    · exact ⟨inferInstance, (SSet.S.mk s).map_toNπ_op_apply⟩
    · exact ⟨inferInstance, h⟩
  unfold normalizeSimplex
  rw [hf]

/-- Removing degeneracies commutes with an epimorphic simplex operator. -/
theorem normalizeSimplex_epi (K : SSet.{0}) {m n : ℕ}
    (f : SimplexCategory.mk m ⟶ .mk n) [Epi f]
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (m+1))) :
    normalizeSimplex K (K.map f.op s) x =
      normalizeSimplex K s (StdSimplex.map f.toOrderHom x) := by
  let c := (SSet.S.mk s).toN
  let q : SimplexCategory.mk n ⟶ .mk c.dim := (SSet.S.mk s).toNπ
  have hq : K.map q.op c.simplex = s := (SSet.S.mk s).map_toNπ_op_apply
  have h : K.map (f ≫ q).op c.simplex = K.map f.op s := by
    rw [op_comp, K.map_comp]
    change K.map f.op (K.map q.op c.simplex) = _
    rw [hq]
  rw [normalizeSimplex_of_representation K _ x c (f ≫ q) h,
    normalizeSimplex_of_representation K s (StdSimplex.map f.toOrderHom x) c q hq]
  congr 1
  exact StdSimplex.map_comp x f.toOrderHom q.toOrderHom

/-- First discard zero coordinates, then remove degeneracies from the supported simplex. -/
def normalizeSupported (K : SSet.{0}) {n : ℕ} (s : K.obj (.op (.mk n)))
    (x : StdSimplex ℝ (Fin (n+1))) : NondegenerateCoordinates K :=
  normalizeSimplex K (K.map (show SimplexCategory.mk (HornBarycentric.supportLen x) ⟶ .mk n
    from SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom).op s)
    (HornBarycentric.supportCoordinates x)

/-- The supported nondegenerate coordinates are invariant under all simplex operators. -/
theorem normalizeSupported_naturality (K : SSet.{0}) {m n : ℕ}
    (f : SimplexCategory.mk m ⟶ .mk n) (s : K.obj (.op (.mk n)))
    (x : StdSimplex ℝ (Fin (m+1))) :
    normalizeSupported K (K.map f.op s) x =
      normalizeSupported K s (StdSimplex.map f.toOrderHom x) := by
  let a : SimplexCategory.mk (HornBarycentric.supportLen x) ⟶ .mk m :=
    SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom
  let b : SimplexCategory.mk (HornBarycentric.supportLen x) ⟶
      .mk (HornBarycentric.supportLen (StdSimplex.map f.toOrderHom x)) :=
    SimplexCategory.Hom.mk (HornBarycentric.supportOrdinal f.toOrderHom x)
  let c : SimplexCategory.mk (HornBarycentric.supportLen (StdSimplex.map f.toOrderHom x)) ⟶
      .mk n := SimplexCategory.Hom.mk
        (HornBarycentric.supportMap (StdSimplex.map f.toOrderHom x)).toOrderHom
  have hb : Epi b := SimplexCategory.epi_iff_surjective.mpr
    (HornBarycentric.supportOrdinal_surjective f.toOrderHom x)
  have he : a ≫ f = b ≫ c := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    exact (HornBarycentric.supportOrdinal_commutes f.toOrderHom x i).symm
  have hs : K.map a.op (K.map f.op s) = K.map b.op (K.map c.op s) := by
    change (K.map f.op ≫ K.map a.op) s = (K.map c.op ≫ K.map b.op) s
    rw [← K.map_comp, ← K.map_comp, ← op_comp, ← op_comp, he]
  change normalizeSimplex K (K.map a.op (K.map f.op s))
    (HornBarycentric.supportCoordinates x) = _
  rw [hs, normalizeSimplex_epi]
  exact congrArg (normalizeSimplex K (K.map c.op s))
    (HornBarycentric.supportCoordinates_naturality f.toOrderHom x)

/-- Nondegenerate coordinates form a cocone of sets over all realization simplices. -/
def normalizationCocone (K : SSet.{0}) : Cocone (diagram K ⋙ forget TopCat) where
  pt := NondegenerateCoordinates K
  ι := {
    app j := ↾fun p => normalizeSupported K (SSet.yonedaEquiv j.hom) p.down
    naturality j k f := by
      apply ConcreteCategory.hom_ext
      intro p
      have hs : K.map f.left.op (SSet.yonedaEquiv k.hom) = SSet.yonedaEquiv j.hom := by
        rw [SSet.yonedaEquiv_naturality, CostructuredArrow.w f]
      change normalizeSupported K (SSet.yonedaEquiv k.hom)
        (StdSimplex.map f.left.toOrderHom p.down) = _
      rw [← hs]
      exact (normalizeSupported_naturality K f.left (SSet.yonedaEquiv k.hom) p.down).symm }

/-- The nondegenerate coordinates of an actual realization point. -/
def normalization (K : SSet.{0}) : SSet.toTop.obj K → NondegenerateCoordinates K :=
  fun p => (isColimitOfPreserves (forget TopCat) (isColimit K)).desc (normalizationCocone K) p

theorem normalization_leg (K : SSet.{0}) (j : CostructuredArrow SSet.stdSimplex K)
    (p : (diagram K).obj j) :
    normalization K ((leg K j).hom p) = normalizeSupported K (SSet.yonedaEquiv j.hom) p.down :=
  congrArg (fun f => f p)
    ((isColimitOfPreserves (forget TopCat) (isColimit K)).fac (normalizationCocone K) j)

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Reconstruction from intrinsic nondegenerate coordinates -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

/-- Evaluate a nondegenerate simplex with specified barycentric coordinates. -/
def denormalize (K : SSet.{0}) (p : NondegenerateCoordinates K) : SSet.toTop.obj K :=
  simplexPoint K p.1.simplex p.2

theorem denormalize_normalizeSimplex (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1))) :
    denormalize K (normalizeSimplex K s x) = simplexPoint K s x := by
  have h := simplexPoint_map K (SSet.S.mk s).toNπ (SSet.S.mk s).toN.simplex x
  have hs : K.map (SSet.S.mk s).toNπ.op (SSet.S.mk s).toN.simplex = s :=
    (SSet.S.mk s).map_toNπ_op_apply
  rw [hs] at h
  exact h.symm

theorem denormalize_normalizeSupported (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1))) :
    denormalize K (normalizeSupported K s x) = simplexPoint K s x := by
  let a : SimplexCategory.mk (HornBarycentric.supportLen x) ⟶ .mk n :=
    SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom
  change denormalize K (normalizeSimplex K (K.map a.op s)
    (HornBarycentric.supportCoordinates x)) = _
  rw [denormalize_normalizeSimplex, simplexPoint_map]
  exact congrArg (simplexPoint K s) (HornBarycentric.support_recover x)

theorem normalization_simplexPoint (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1))) :
    normalization K (simplexPoint K s x) = normalizeSupported K s x := by
  have h := normalization_leg K (CostructuredArrow.mk (SSet.yonedaEquiv.symm s)) (ULift.up x)
  change normalization K (simplexPoint K s x) =
    normalizeSupported K (SSet.yonedaEquiv (SSet.yonedaEquiv.symm s)) x at h
  rw [SSet.yonedaEquiv.apply_symm_apply] at h
  exact h

/-- The intrinsic normal coordinates reconstruct every actual realization point. -/
theorem denormalize_normalization (K : SSet.{0}) (x : SSet.toTop.obj K) :
    denormalize K (normalization K x) = x := by
  obtain ⟨n, s, p, rfl⟩ := point_representation_simplex K x
  rw [normalization_simplexPoint, denormalize_normalizeSupported]

/-- Distinct realization points have distinct intrinsic nondegenerate coordinates. -/
theorem normalization_injective (K : SSet.{0}) : Function.Injective (normalization K) :=
  (show Function.LeftInverse (denormalize K) (normalization K) from
    denormalize_normalization K).injective

/-- With no zero coordinates the support normalization agrees with degeneracy normalization. -/
theorem normalizeSupported_of_full_support (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1)))
    (hx : ∀ i, x.weights i ≠ 0) :
    normalizeSupported K s x = normalizeSimplex K s x := by
  let a : SimplexCategory.mk (HornBarycentric.supportLen x) ⟶ .mk n :=
    SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom
  have ha : Epi a := SimplexCategory.epi_iff_surjective.mpr (by
    intro i
    have hi : i ∈ Set.range (HornBarycentric.supportMap x) := by
      rw [HornBarycentric.supportMap_range]
      exact Finsupp.mem_support_iff.mpr (hx i)
    exact hi)
  change normalizeSimplex K (K.map a.op s) (HornBarycentric.supportCoordinates x) = _
  rw [normalizeSimplex_epi]
  exact congrArg (normalizeSimplex K s) (HornBarycentric.support_recover x)

/-- Interior points of a nondegenerate simplex have precisely that simplex's coordinates. -/
theorem normalization_nondegenerate_interior (K : SSet.{0}) (s : K.N)
    (x : StdSimplex ℝ (Fin (s.dim+1))) (hx : ∀ i, x.weights i ≠ 0) :
    normalization K (simplexPoint K s.simplex x) = ⟨s, x⟩ := by
  rw [normalization_simplexPoint, normalizeSupported_of_full_support K _ x hx]
  have h := normalizeSimplex_of_representation K s.simplex x s (𝟙 _) (by simp)
  change normalizeSimplex K s.simplex x = ⟨s, StdSimplex.map id x⟩ at h
  simpa only [StdSimplex.map_id] using h

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Closed points in geometric realization -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite Topology
open scoped Simplicial

noncomputable section

/-- Degeneracy normalization on a fixed simplex is continuous into the disjoint union. -/
theorem normalizeSimplex_continuous (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) : Continuous (normalizeSimplex K s) :=
  continuous_sigmaMk.comp (StdSimplex.continuous_map ℝ (SSet.S.mk s).toNπ.toOrderHom)

theorem nondegenerateCoordinates_t2Space (K : SSet.{0}) :
    T2Space (NondegenerateCoordinates K) := by
  let (s : K.N) : T2Space (StdSimplex ℝ (Fin (s.dim+1))) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).t2Space
  infer_instance

/-- A point fibre on a parameter simplex is a finite union of compact affine images. -/
theorem simplexPoint_fiber_eq (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (z : SSet.toTop.obj K) :
    (simplexPoint K s) ⁻¹' {z} =
      ⋃ i : FaceIndex n, (StdSimplex.map i.2.toOrderHom) ''
        ((normalizeSimplex K (K.map i.2.op s)) ⁻¹' {normalization K z}) := by
  ext x
  constructor
  · intro hx
    have he : simplexPoint K s x = z := hx
    let k : Fin (n+1) := ⟨HornBarycentric.supportLen x, by
      have h := supportLen_le x
      omega⟩
    let f : SimplexCategory.mk k.val ⟶ .mk n :=
      SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom
    apply Set.mem_iUnion.mpr
    refine ⟨⟨k, f⟩, HornBarycentric.supportCoordinates x, ?_, HornBarycentric.support_recover x⟩
    change normalizeSupported K s x = normalization K z
    rw [← normalization_simplexPoint, he]
  · intro hx
    obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    change normalizeSimplex K (K.map i.2.op s) y = normalization K z at hy
    have he := congrArg (denormalize K) hy
    rw [denormalize_normalizeSimplex, denormalize_normalization, simplexPoint_map] at he
    exact he

/-- Individual point fibres are closed on every barycentric parameter simplex. -/
theorem simplexPoint_fiber_isClosed (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (z : SSet.toTop.obj K) :
    IsClosed ((simplexPoint K s) ⁻¹' {z}) := by
  let : T2Space (NondegenerateCoordinates K) := nondegenerateCoordinates_t2Space K
  let : T2Space (StdSimplex ℝ (Fin (n+1))) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).t2Space
  rw [simplexPoint_fiber_eq]
  apply isClosed_iUnion_of_finite
  intro i
  exact ((isClosed_singleton.preimage (normalizeSimplex_continuous K _)).isCompact.image
    (StdSimplex.continuous_map ℝ i.2.toOrderHom)).isClosed

/-- Every actual geometric realization is a T₁ space. -/
theorem realization_t1Space (K : SSet.{0}) : T1Space (SSet.toTop.obj K) where
  t1 z := by
    apply (isClosed_iff_simplex K _).mpr
    intro j
    rcases j with ⟨⟨n⟩, ⟨⟨⟩⟩, g⟩
    have hs := (simplexPoint_fiber_isClosed K (SSet.yonedaEquiv g) z).preimage
      continuous_uliftDown
    have he : (leg K (CostructuredArrow.mk g)).hom ⁻¹' {z} =
        ULift.down ⁻¹' ((simplexPoint K (SSet.yonedaEquiv g)) ⁻¹' {z}) := by
      ext p
      change (leg K (CostructuredArrow.mk g)).hom p = z ↔
        (leg K (CostructuredArrow.mk (SSet.yonedaEquiv.symm (SSet.yonedaEquiv g)))).hom
          (ULift.up p.down) = z
      rw [SSet.yonedaEquiv.symm_apply_apply]
      rfl
    exact he.symm ▸ hs

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Compact subsets meet only finitely many intrinsic simplex carriers -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite Topology Classical
open scoped Simplicial

noncomputable section

/-- Only finitely many supported simplex carriers occur in one parameter simplex. -/
theorem simplexCarrier_range_finite (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) : Set.Finite (Set.range (simplexCarrier K s)) := by
  apply (Set.finite_range (fun i : FaceIndex n => SSet.Subcomplex.ofSimplex (K.map i.2.op s))).subset
  rintro _ ⟨x, rfl⟩
  let k : Fin (n+1) := ⟨HornBarycentric.supportLen x, by
    have h := supportLen_le x
    omega⟩
  let f : SimplexCategory.mk k.val ⟶ .mk n :=
    SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom
  exact ⟨⟨k, f⟩, rfl⟩

/-- A set containing at most one point in each carrier is closed. -/
theorem isClosed_of_carrier_injOn (K : SSet.{0}) (S : Set (SSet.toTop.obj K))
    (hS : Set.InjOn (carrier K) S) : IsClosed S := by
  apply (isClosed_iff_simplex K S).mpr
  intro j
  let T := Set.range (leg K j).hom ∩ S
  have hi : (carrier K '' T).Finite :=
    (simplexCarrier_range_finite K (SSet.yonedaEquiv j.hom)).subset (by
      rintro _ ⟨x, ⟨⟨p, rfl⟩, _⟩, rfl⟩
      exact ⟨p.down, (carrier_leg K j p).symm⟩)
  have ht : T.Finite := hi.of_finite_image (hS.mono Set.inter_subset_right)
  have he : (leg K j).hom ⁻¹' S = (leg K j).hom ⁻¹' T := by
    ext p
    simp only [Set.mem_preimage, Set.mem_inter_iff, T]
    exact ⟨fun h => ⟨⟨p, rfl⟩, h⟩, fun h => h.2⟩
  rw [he]
  have htClosed : IsClosed (T : Set (SSet.toTop.obj K)) :=
    @Set.Finite.isClosed (SSet.toTop.obj K) inferInstance (realization_t1Space K) T ht
  exact htClosed.preimage (leg K j).hom.continuous

/-- Such a set is also discrete, since each of its subsets has the same carrier property. -/
theorem isDiscrete_of_carrier_injOn (K : SSet.{0}) (S : Set (SSet.toTop.obj K))
    (hS : Set.InjOn (carrier K) S) : IsDiscrete S := by
  apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
  intro T hT
  exact ⟨T, isClosed_of_carrier_injOn K T (hS.mono hT), Set.inter_eq_left.mpr hT⟩

/-- Every compact subset of realization meets only finitely many supported simplex carriers. -/
theorem compact_carriers_finite (K : SSet.{0}) (C : Set (SSet.toTop.obj K))
    (hC : IsCompact C) : Set.Finite (carrier K '' C) := by
  let I := carrier K '' C
  let pick (c : I) : SSet.toTop.obj K := Classical.choose c.property
  have hp (c : I) : pick c ∈ C ∧ carrier K (pick c) = c.val := Classical.choose_spec c.property
  let D := Set.range pick
  have hd : Set.InjOn (carrier K) D := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩ h
    have hc : c = d := Subtype.ext ((hp c).2.symm.trans (h.trans (hp d).2))
    subst d
    rfl
  have hDC : D ⊆ C := by rintro _ ⟨c, rfl⟩; exact (hp c).1
  have hD : D.Finite :=
    (hC.of_isClosed_subset (isClosed_of_carrier_injOn K D hd) hDC).finite
      (isDiscrete_of_carrier_injOn K D hd)
  apply (hD.image (carrier K)).subset
  intro c hc
  exact ⟨pick ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩, (hp ⟨c, hc⟩).2⟩

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Compact maps into realizations factor through finite subcomplexes -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite Topology Classical
open scoped Simplicial

noncomputable section

/-- Every intrinsic carrier is generated by one simplex, hence is a finite simplicial set. -/
theorem carrier_finite (K : SSet.{0}) (x : SSet.toTop.obj K) :
    SSet.Finite (carrier K x : SSet) := by
  obtain ⟨n, s, p, rfl⟩ := point_representation_simplex K x
  rw [carrier_simplexPoint]
  unfold simplexCarrier
  infer_instance

/-- The finite subcomplex generated by all carriers met by a compact subset. -/
def compactSubcomplex (K : SSet.{0}) (C : Set (SSet.toTop.obj K)) : K.Subcomplex :=
  ⨆ c : carrier K '' C, c.val

theorem compactSubcomplex_finite (K : SSet.{0}) (C : Set (SSet.toTop.obj K))
    (hC : IsCompact C) : SSet.Finite (compactSubcomplex K C : SSet) := by
  have : Finite (carrier K '' C) := (compact_carriers_finite K C hC).to_subtype
  apply (SSet.finite_iSup_iff _).mpr
  rintro ⟨c, x, hx, rfl⟩
  exact carrier_finite K x

/-- The compact subset lies in the realization of its finite carrier subcomplex. -/
theorem compactSubcomplex_contains (K : SSet.{0}) (C : Set (SSet.toTop.obj K)) :
    C ⊆ Set.range (SSet.toTop.map (compactSubcomplex K C).ι).hom := by
  intro x hx
  apply (mem_range_inclusion_iff K _ x).mpr
  exact le_iSup (fun c : carrier K '' C => c.val) ⟨carrier K x, x, hx, rfl⟩

/-- Every continuous map from a compact space into realization factors continuously
    through the realization of a finite simplicial subcomplex. -/
theorem compact_map_factors {X : Type} [TopologicalSpace X] [CompactSpace X]
    (K : SSet.{0}) (f : C(X, SSet.toTop.obj K)) :
    ∃ (A : K.Subcomplex), SSet.Finite (A : SSet) ∧
      ∃ g : C(X, SSet.toTop.obj (A : SSet)), (SSet.toTop.map A.ι).hom.comp g = f := by
  let C := Set.range f
  have hC : IsCompact C := isCompact_range f.continuous
  let A := compactSubcomplex K C
  have hf (x : X) : f x ∈ Set.range (SSet.toTop.map A.ι).hom :=
    compactSubcomplex_contains K C ⟨x, rfl⟩
  let g₀ : X → SSet.toTop.obj (A : SSet) := fun x => Classical.choose (hf x)
  have hg₀ (x : X) : (SSet.toTop.map A.ι).hom (g₀ x) = f x := Classical.choose_spec (hf x)
  have hg : Continuous g₀ := by
    apply (inclusion_isClosedEmbedding K A).isEmbedding.continuous_iff.mpr
    have he : (SSet.toTop.map A.ι).hom ∘ g₀ = f := funext hg₀
    rw [he]
    exact f.continuous
  exact ⟨A, compactSubcomplex_finite K C hC, ⟨g₀, hg⟩, ContinuousMap.ext hg₀⟩

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Finite-subcomplex factorization of the actual based cubes -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

/-- Every positive-dimensional based cube in realization factors through a finite
    subcomplex, with its entire boundary still constant at a lifted basepoint. -/
theorem based_cube_factors (K : SSet.{0}) {x : SSet.toTop.obj K} (n : ℕ)
    (p : GenLoop (Fin (n+1)) (SSet.toTop.obj K) x) :
    ∃ (A : K.Subcomplex), SSet.Finite (A : SSet) ∧
      ∃ (a : SSet.toTop.obj (A : SSet)), (SSet.toTop.map A.ι).hom a = x ∧
        ∃ q : GenLoop (Fin (n+1)) (SSet.toTop.obj (A : SSet)) a,
          ∀ t, (SSet.toTop.map A.ι).hom (q t) = p t := by
  obtain ⟨A, hA, g, hg⟩ := compact_map_factors K p.val
  have he (t : Fin (n+1) → unitInterval) : (SSet.toTop.map A.ι).hom (g t) = p t :=
    congrArg (fun f : C(_, _) => f t) hg
  let a := g (fun _ => 0)
  have ha : (SSet.toTop.map A.ι).hom a = x :=
    (he _).trans (p.property _ ⟨0, Or.inl rfl⟩)
  have hb : ∀ t ∈ Cube.boundary (Fin (n+1)), g t = a := by
    intro t ht
    apply inclusion_injective K A
    exact (he t).trans ((p.property t ht).trans ha.symm)
  exact ⟨A, hA, a, ha, ⟨g, hb⟩, he⟩

/-- A relative homotopy of based cubes has a single finite-subcomplex factorization,
    including both endpoint cubes and the fixed boundary. -/
theorem based_homotopy_factors (K : SSet.{0}) {x : SSet.toTop.obj K} (n : ℕ)
    {p q : GenLoop (Fin (n+1)) (SSet.toTop.obj K) x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin (n+1)))) :
    ∃ (A : K.Subcomplex), SSet.Finite (A : SSet) ∧
      ∃ (a : SSet.toTop.obj (A : SSet)), (SSet.toTop.map A.ι).hom a = x ∧
        ∃ (p' q' : GenLoop (Fin (n+1)) (SSet.toTop.obj (A : SSet)) a)
          (H' : p'.val.HomotopyRel q'.val (Cube.boundary (Fin (n+1)))),
          (∀ t, (SSet.toTop.map A.ι).hom (p' t) = p t) ∧
          (∀ t, (SSet.toTop.map A.ι).hom (q' t) = q t) ∧
          (∀ z, (SSet.toTop.map A.ι).hom (H' z) = H z) := by
  let F : C(unitInterval × (Fin (n+1) → unitInterval), SSet.toTop.obj K) :=
    ⟨H, H.continuous⟩
  obtain ⟨A, hA, g, hg⟩ := compact_map_factors K F
  have he (z) : (SSet.toTop.map A.ι).hom (g z) = H z :=
    congrArg (fun f : C(_, _) => f z) hg
  let a := g (0, fun _ => 0)
  have ha : (SSet.toTop.map A.ι).hom a = x :=
    (he _).trans ((H.apply_zero _).trans (p.property _ ⟨0, Or.inl rfl⟩))
  have hb (e : unitInterval) (t : Fin (n+1) → unitInterval)
      (ht : t ∈ Cube.boundary (Fin (n+1))) : g (e, t) = a := by
    apply inclusion_injective K A
    exact (he _).trans ((H.eq_fst e ht).trans ((p.property t ht).trans ha.symm))
  let p' : GenLoop (Fin (n+1)) (SSet.toTop.obj (A : SSet)) a :=
    ⟨⟨fun t => g (0, t), g.continuous.comp (continuous_const.prodMk continuous_id)⟩, hb 0⟩
  let q' : GenLoop (Fin (n+1)) (SSet.toTop.obj (A : SSet)) a :=
    ⟨⟨fun t => g (1, t), g.continuous.comp (continuous_const.prodMk continuous_id)⟩, hb 1⟩
  let H' : p'.val.HomotopyRel q'.val (Cube.boundary (Fin (n+1))) := {
    toFun := g
    continuous_toFun := g.continuous
    map_zero_left := fun _ => rfl
    map_one_left := fun _ => rfl
    prop' := fun e t ht => (hb e t ht).trans (hb 0 t ht).symm }
  refine ⟨A, hA, a, ha, p', q', H', ?_, ?_, he⟩
  · intro t
    exact (he _).trans (H.apply_zero t)
  · intro t
    exact (he _).trans (H.apply_one t)

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Finite approximation of actual commuting realization squares -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory

noncomputable section

/-- A continuous compact lifting problem over a realized simplicial map
factors through one map between finite simplicial subcomplexes. The lifted
square still commutes exactly, including any prescribed boundary values. -/
theorem compact_square_factors {P Q : Type}
    [TopologicalSpace P] [CompactSpace P] [TopologicalSpace Q] [CompactSpace Q]
    {K L : SSet.{0}} (f : K ⟶ L)
    (u : C(P, Q)) (a : C(P, SSet.toTop.obj K)) (b : C(Q, SSet.toTop.obj L))
    (h : (SSet.toTop.map f).hom.comp a = b.comp u) :
    ∃ (A : K.Subcomplex) (B : L.Subcomplex),
      SSet.Finite (A : SSet) ∧ SSet.Finite (B : SSet) ∧
      ∃ (g : (A : SSet) ⟶ (B : SSet))
        (a' : C(P, SSet.toTop.obj (A : SSet)))
        (b' : C(Q, SSet.toTop.obj (B : SSet))),
        g ≫ B.ι = A.ι ≫ f ∧
        (SSet.toTop.map A.ι).hom.comp a' = a ∧
        (SSet.toTop.map B.ι).hom.comp b' = b ∧
        (SSet.toTop.map g).hom.comp a' = b'.comp u := by
  obtain ⟨A, hA, a', ha⟩ := compact_map_factors K a
  obtain ⟨C, hC, bC, hb⟩ := compact_map_factors L b
  let : SSet.Finite (A : SSet) := hA
  let : SSet.Finite (C : SSet) := hC
  let T : Bool → L.Subcomplex := fun e => if e then SSet.Subcomplex.range (A.ι ≫ f) else C
  let B : L.Subcomplex := iSup T
  have hB : SSet.Finite (B : SSet) := by
    apply (SSet.finite_iSup_iff T).mpr
    intro e
    cases e <;> dsimp [T] <;> infer_instance
  have hf : SSet.Subcomplex.range (A.ι ≫ f) ≤ B := le_iSup T true
  have hc : C ≤ B := le_iSup T false
  let g : (A : SSet) ⟶ (B : SSet) := B.lift (A.ι ≫ f) hf
  let j := SSet.Subcomplex.homOfLE hc
  let b' := (SSet.toTop.map j).hom.comp bC
  have hg : g ≫ B.ι = A.ι ≫ f := rfl
  have hj : j ≫ B.ι = C.ι := rfl
  have hb' : (SSet.toTop.map B.ι).hom.comp b' = b := by
    apply ContinuousMap.ext
    intro x
    have he := SSet.toTop.congr_map hj
    rw [SSet.toTop.map_comp] at he
    exact (congrArg (fun t => t.hom (bC x)) he).trans
      (congrArg (fun t : C(_, _) => t x) hb)
  refine ⟨A, B, hA, hB, g, a', b', hg, ha, hb', ?_⟩
  apply ContinuousMap.ext
  intro x
  apply inclusion_injective L B
  have he := SSet.toTop.congr_map hg
  rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at he
  calc
    (SSet.toTop.map B.ι).hom ((SSet.toTop.map g).hom (a' x)) =
        (SSet.toTop.map f).hom ((SSet.toTop.map A.ι).hom (a' x)) :=
      congrArg (fun t => t.hom (a' x)) he
    _ = (SSet.toTop.map f).hom (a x) :=
      congrArg (SSet.toTop.map f).hom (congrArg (fun t : C(_, _) => t x) ha)
    _ = b (u x) := congrArg (fun t : C(_, _) => t x) h
    _ = (SSet.toTop.map B.ι).hom (b' (u x)) :=
      (congrArg (fun t : C(_, _) => t (u x)) hb').symm

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Simplex parameter maps are closed maps

The proof uses finite face pairs with equal nondegenerate coordinates. It
therefore needs no Hausdorff assumption on the realization itself.
-/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite Topology
open scoped Simplicial

noncomputable section

def supportFaceIndex {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) : FaceIndex n :=
  ⟨⟨HornBarycentric.supportLen x, by have h := supportLen_le x; omega⟩,
    SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom⟩

/-- Pairs of face points whose nondegenerate coordinate descriptions agree. -/
def matchingFacePairs (K : SSet.{0}) {n m : ℕ}
    (s : K.obj (.op (.mk n))) (t : K.obj (.op (.mk m)))
    (B : Set (StdSimplex ℝ (Fin (n+1)))) (i : FaceIndex n) (j : FaceIndex m) :
    Set (StdSimplex ℝ (Fin (i.1.val+1)) × StdSimplex ℝ (Fin (j.1.val+1))) :=
  Set.ofPred (fun p => StdSimplex.map i.2.toOrderHom p.1 ∈ B ∧
    normalizeSimplex K (K.map i.2.op s) p.1 = normalizeSimplex K (K.map j.2.op t) p.2)

theorem matchingFacePairs_isClosed (K : SSet.{0}) {n m : ℕ}
    (s : K.obj (.op (.mk n))) (t : K.obj (.op (.mk m)))
    (B : Set (StdSimplex ℝ (Fin (n+1)))) (hB : IsClosed B)
    (i : FaceIndex n) (j : FaceIndex m) : IsClosed (matchingFacePairs K s t B i j) := by
  let : T2Space (NondegenerateCoordinates K) := nondegenerateCoordinates_t2Space K
  exact (hB.preimage ((StdSimplex.continuous_map ℝ i.2.toOrderHom).comp continuous_fst)).inter
    (isClosed_eq ((normalizeSimplex_continuous K _).comp continuous_fst)
      ((normalizeSimplex_continuous K _).comp continuous_snd))

/-- Equality of points from two parameter simplices is detected by finitely many face pairs. -/
theorem simplexPoint_preimage_image (K : SSet.{0}) {n m : ℕ}
    (s : K.obj (.op (.mk n))) (t : K.obj (.op (.mk m)))
    (B : Set (StdSimplex ℝ (Fin (n+1)))) :
    (simplexPoint K t) ⁻¹' ((simplexPoint K s) '' B) =
      ⋃ ij : FaceIndex n × FaceIndex m,
        (fun p => StdSimplex.map ij.2.2.toOrderHom p.2) ''
          matchingFacePairs K s t B ij.1 ij.2 := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    apply Set.mem_iUnion.mpr
    refine ⟨(supportFaceIndex y, supportFaceIndex x),
      (HornBarycentric.supportCoordinates y, HornBarycentric.supportCoordinates x),
      ?_, HornBarycentric.support_recover x⟩
    constructor
    · change StdSimplex.map (HornBarycentric.supportMap y)
        (HornBarycentric.supportCoordinates y) ∈ B
      rwa [HornBarycentric.support_recover]
    · change normalizeSupported K s y = normalizeSupported K t x
      rw [← normalization_simplexPoint, ← normalization_simplexPoint, he]
  · intro hx
    obtain ⟨⟨i, j⟩, ⟨u, v⟩, hp, rfl⟩ := Set.mem_iUnion.mp hx
    have he := congrArg (denormalize K) hp.2
    rw [denormalize_normalizeSimplex, denormalize_normalizeSimplex,
      simplexPoint_map, simplexPoint_map] at he
    exact ⟨StdSimplex.map i.2.toOrderHom u, hp.1, he⟩

/-- Each continuous simplex parameter map into realization is closed. -/
theorem simplexPoint_isClosedMap (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) : IsClosedMap (simplexPoint K s) := by
  intro B hB
  have h (m : ℕ) (t : K.obj (.op (.mk m))) :
      IsClosed ((simplexPoint K t) ⁻¹' ((simplexPoint K s) '' B)) := by
    let : T2Space (StdSimplex ℝ (Fin (m+1))) :=
      (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).t2Space
    rw [simplexPoint_preimage_image]
    apply isClosed_iUnion_of_finite
    intro ij
    exact ((matchingFacePairs_isClosed K s t B hB ij.1 ij.2).isCompact.image
      ((StdSimplex.continuous_map ℝ ij.2.2.toOrderHom).comp continuous_snd)).isClosed
  apply (isClosed_iff_simplex K _).mpr
  intro j
  rcases j with ⟨⟨m⟩, ⟨⟨⟩⟩, g⟩
  have hs := (h m (SSet.yonedaEquiv g)).preimage continuous_uliftDown
  have he : (leg K (CostructuredArrow.mk g)).hom ⁻¹' ((simplexPoint K s) '' B) =
      ULift.down ⁻¹' ((simplexPoint K (SSet.yonedaEquiv g)) ⁻¹' ((simplexPoint K s) '' B)) := by
    ext p
    change (leg K (CostructuredArrow.mk g)).hom p ∈ ((simplexPoint K s) '' B) ↔
      (leg K (CostructuredArrow.mk (SSet.yonedaEquiv.symm (SSet.yonedaEquiv g)))).hom
        (ULift.up p.down) ∈ ((simplexPoint K s) '' B)
    rw [SSet.yonedaEquiv.symm_apply_apply]
    rfl
  exact he.symm ▸ hs

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Finite realizations are compact Hausdorff spaces

The finite union of simplex parameter spaces is a closed quotient. Separating
its closed fibers gives Hausdorff separation in the actual realization.
-/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite Topology
open scoped Simplicial

noncomputable section

theorem nondegenerateProjection_isClosedMap (K : SSet.{0}) [K.Finite] :
    IsClosedMap (nondegenerateProjection K) := by
  intro C hC
  have he : nondegenerateProjection K '' C =
      ⋃ s : K.N, simplexPoint K s.simplex ''
        ((fun x => (⟨s, x⟩ : NondegeneratePoints K)) ⁻¹' C) := by
    ext y
    constructor
    · rintro ⟨⟨s, x⟩, hx, rfl⟩
      exact Set.mem_iUnion.mpr ⟨s, x, hx, rfl⟩
    · intro hy
      obtain ⟨s, x, hx, rfl⟩ := Set.mem_iUnion.mp hy
      exact ⟨⟨s, x⟩, hx, rfl⟩
  rw [he]
  apply isClosed_iUnion_of_finite
  intro s
  exact simplexPoint_isClosedMap K s.simplex _ (hC.preimage continuous_sigmaMk)

/-- A finite realization has its actual quotient topology from its finitely
    many nondegenerate simplex parameter spaces. -/
theorem nondegenerateProjection_isQuotientMap (K : SSet.{0}) [K.Finite] :
    IsQuotientMap (nondegenerateProjection K) :=
  (nondegenerateProjection_isClosedMap K).isQuotientMap
    (nondegenerateProjection_continuous K) (nondegenerateProjection_surjective K)

/-- Finite simplicial realizations are Hausdorff; no ambient separation
    assumption on arbitrary realizations is used. -/
theorem finite_realization_t2Space (K : SSet.{0}) [K.Finite] :
    T2Space (SSet.toTop.obj K) := by
  let : T1Space (SSet.toTop.obj K) := realization_t1Space K
  let : T2Space (NondegeneratePoints K) := nondegenerateCoordinates_t2Space K
  let q := nondegenerateProjection K
  have hq := nondegenerateProjection_isClosedMap K
  refine ⟨?_⟩
  intro x y hxy
  have hx : IsClosed (q ⁻¹' {x}) := isClosed_singleton.preimage
    (nondegenerateProjection_continuous K)
  have hy : IsClosed (q ⁻¹' {y}) := isClosed_singleton.preimage
    (nondegenerateProjection_continuous K)
  have hd : Disjoint (q ⁻¹' {x}) (q ⁻¹' {y}) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hxy (hz.symm.trans hz')
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := normal_separation hx hy hd
  refine ⟨(q '' Uᶜ)ᶜ, (q '' Vᶜ)ᶜ, (hq _ hU.isClosed_compl).isOpen_compl,
    (hq _ hV.isClosed_compl).isOpen_compl, ?_, ?_, ?_⟩
  · rintro ⟨z, hz, he⟩
    exact hz (hxU he)
  · rintro ⟨z, hz, he⟩
    exact hz (hyV he)
  · apply Set.disjoint_left.mpr
    intro z hzU hzV
    obtain ⟨w, rfl⟩ := nondegenerateProjection_surjective K z
    have hwU : w ∈ U := by
      by_contra hw
      exact hzU ⟨w, hw, rfl⟩
    have hwV : w ∈ V := by
      by_contra hw
      exact hzV ⟨w, hw, rfl⟩
    exact Set.disjoint_left.mp hUV hwU hwV

end

end Thomason.Construction.RealizationPrism

end

section

/-! # One-simplex subcomplexes as actual closed quotients -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite Topology
open scoped Simplicial

noncomputable section

/-- The parameter map onto the entire subcomplex generated by one simplex. -/
def monogenousPoint (K : SSet.{0}) {n : ℕ} (s : K.obj (.op (.mk n))) :
    C(StdSimplex ℝ (Fin (n+1)), SSet.toTop.obj (SSet.Subcomplex.ofSimplex s : SSet)) :=
  simplexPoint _ ⟨s, SSet.Subcomplex.mem_ofSimplex_obj s⟩

/-- This map covers every point, including all degenerate representations. -/
theorem monogenousPoint_surjective (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) : Function.Surjective (monogenousPoint K s) := by
  intro y
  obtain ⟨m, t, p, rfl⟩ := point_representation_simplex (SSet.Subcomplex.ofSimplex s : SSet) y
  obtain ⟨f, hf⟩ := (SSet.Subcomplex.mem_ofSimplex_obj_iff s t.val).mp t.property
  let seed : (SSet.Subcomplex.ofSimplex s : SSet).obj (.op (.mk n)) :=
    ⟨s, SSet.Subcomplex.mem_ofSimplex_obj s⟩
  have he : (SSet.Subcomplex.ofSimplex s : SSet).map f.op seed = t := by
    apply Subtype.ext
    exact hf
  refine ⟨StdSimplex.map f.toOrderHom p, ?_⟩
  change simplexPoint _ seed (StdSimplex.map f.toOrderHom p) = _
  rw [← simplexPoint_map, he]

/-- The realization of a simplex-generated subcomplex is its closed topological quotient. -/
theorem monogenousPoint_isQuotientMap (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) : IsQuotientMap (monogenousPoint K s) :=
  (simplexPoint_isClosedMap _ _).isQuotientMap (monogenousPoint K s).continuous
    (monogenousPoint_surjective K s)

/-- The original simplex parameter map factors through that quotient and the closed inclusion. -/
theorem monogenousPoint_inclusion (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) :
    (SSet.toTop.map (SSet.Subcomplex.ofSimplex s).ι).hom.comp (monogenousPoint K s) =
      simplexPoint K s := by
  apply ContinuousMap.ext
  intro x
  exact simplexPoint_naturality _ _ x

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Nondegenerate simplex interiors in geometric realization -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite Topology
open scoped Simplicial

noncomputable section

/-- The barycentric interior, expressed by its nonzero coordinates. -/
def fullSupport (n : ℕ) : Set (StdSimplex ℝ (Fin (n+1))) :=
  Set.ofPred (fun x => ∀ i, x.weights i ≠ 0)

theorem fullSupport_isOpen (n : ℕ) : IsOpen (fullSupport n) := by
  have he : fullSupport n =
      ⋂ i : Fin (n+1), Set.ofPred (fun x : StdSimplex ℝ (Fin (n+1)) => x.weights i ≠ 0) := by
    ext x
    simp only [fullSupport, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact (isClosed_eq (StdSimplex.continuous_weights_apply ℝ i)
    (show Continuous (fun _ : StdSimplex ℝ (Fin (n+1)) => (0 : ℝ)) from continuous_const)).isOpen_compl

theorem normalization_dim_le_supportLen (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1))) :
    (normalization K (simplexPoint K s x)).1.dim ≤ HornBarycentric.supportLen x := by
  rw [normalization_simplexPoint]
  exact SSet.S.dim_toN_le _

theorem fullSupport_of_supportLen_ge {n : ℕ} (x : StdSimplex ℝ (Fin (n+1)))
    (hx : n ≤ HornBarycentric.supportLen x) : x ∈ fullSupport n := by
  have he : HornBarycentric.supportLen x = n := le_antisymm (supportLen_le x) hx
  have hc : x.weights.support.card = Fintype.card (Fin (n+1)) := by
    rw [HornBarycentric.support_card, he, Fintype.card_fin]
  have hu := Finset.eq_univ_of_card x.weights.support hc
  intro i
  apply Finsupp.mem_support_iff.mp
  rw [hu]
  exact Finset.mem_univ _

/-- A point of a nondegenerate simplex interior has no other representative
    in that simplex, including on its boundary. -/
theorem interior_simplexPoint_fiber (K : SSet.{0}) (s : K.N)
    (x y : StdSimplex ℝ (Fin (s.dim+1))) (hx : x ∈ fullSupport s.dim)
    (hxy : simplexPoint K s.simplex y = simplexPoint K s.simplex x) : y = x := by
  have hn : normalization K (simplexPoint K s.simplex y) = ⟨s, x⟩ := by
    rw [hxy, normalization_nondegenerate_interior K s x hx]
  have hy : y ∈ fullSupport s.dim := by
    apply fullSupport_of_supportLen_ge y
    have hd := normalization_dim_le_supportLen K s.simplex y
    rw [hn] at hd
    exact hd
  rw [normalization_nondegenerate_interior K s y hy] at hn
  exact eq_of_heq (Sigma.mk.inj_iff.mp hn).2

/-- The nondegenerate interior is saturated under the simplex quotient. -/
theorem interior_preimage_image (K : SSet.{0}) (s : K.N) :
    (simplexPoint K s.simplex) ⁻¹' ((simplexPoint K s.simplex) '' fullSupport s.dim) =
      fullSupport s.dim := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    rwa [interior_simplexPoint_fiber K s x y hx hxy.symm]
  · intro hy
    exact ⟨y, hy, rfl⟩

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Topological cells inside the actual realization -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite Topology
open scoped Simplicial

noncomputable section

/-- A closed map remains closed on the preimage of any target subspace. -/
theorem closedMap_restrictPreimage {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsClosedMap f) (S : Set Y) : IsClosedMap (S.restrictPreimage f) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := isClosed_induced_iff.mp hC
  have he : (S.restrictPreimage f) '' (Subtype.val ⁻¹' D) = Subtype.val ⁻¹' (f '' D) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨x, hx, he⟩
      exact ⟨⟨x, show f x ∈ S from he.symm ▸ y.property⟩, hx, Subtype.ext he⟩
  rw [he]
  exact (hf D hD).preimage continuous_subtype_val

/-- The open barycentric simplex is homeomorphic to the corresponding
    nondegenerate cell in the actual realization. -/
def cellInteriorHomeomorph (K : SSet.{0}) (s : K.N) :
    fullSupport s.dim ≃ₜ (simplexPoint K s.simplex '' fullSupport s.dim) := by
  let S := simplexPoint K s.simplex '' fullSupport s.dim
  let f := S.restrictPreimage (simplexPoint K s.simplex)
  have hi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hx : x.val ∈ fullSupport s.dim := by
      rw [← interior_preimage_image K s]
      exact x.property
    have he : simplexPoint K s.simplex y.val = simplexPoint K s.simplex x.val :=
      (congrArg Subtype.val hxy).symm
    exact (interior_simplexPoint_fiber K s x.val y.val hx he).symm
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, he⟩ := y.property
    exact ⟨⟨x, show simplexPoint K s.simplex x ∈ S from he.symm ▸ y.property⟩, Subtype.ext he⟩
  have hc : IsClosedEmbedding f := .of_continuous_injective_isClosedMap
    (simplexPoint K s.simplex).continuous.restrictPreimage hi
    (closedMap_restrictPreimage (simplexPoint_isClosedMap K s.simplex) S)
  exact (Homeomorph.setCongr (interior_preimage_image K s).symm).trans
    (hc.isEmbedding.toHomeomorphOfSurjective hs)

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Characteristic simplex closures in actual geometric realization -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite Topology
open scoped Simplicial

noncomputable section

/-- Every barycentric point is approached by points with all coordinates
    nonzero, by moving it towards the barycenter. -/
theorem fullSupport_dense (n : ℕ) : Dense (fullSupport n) := by
  intro x
  let f : unitInterval → StdSimplex ℝ (Fin (n+1)) := fun t =>
    convexCombPair (R := ℝ) (unitInterval.symm t) t
      (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) x StdSimplex.barycenter
  have hf : Continuous f := StdSimplex.continuous_convexCombPair _ _
  have hz : f 0 = x := by simp [f]
  have hpos : Set.MapsTo f (Set.Ioi 0) (fullSupport n) := by
    intro t ht i
    have ht' : (0 : ℝ) < t := ht
    have hb : (0 : ℝ) < (StdSimplex.barycenter : StdSimplex ℝ (Fin (n+1))).weights i := by
      rw [StdSimplex.weights_barycenter_apply, Fintype.card_fin]
      positivity
    change (f t).weights i ≠ 0
    simp only [f, StdSimplex.weights_convexCombPair, Finsupp.add_apply,
      Finsupp.smul_apply, smul_eq_mul]
    exact ne_of_gt (add_pos_of_nonneg_of_pos
      (mul_nonneg (unitInterval.nonneg _) (x.nonneg i)) (mul_pos ht' hb))
  have hzero : (0 : unitInterval) ∈ closure (Set.Ioi (0 : unitInterval)) := by
    rw [closure_Ioi' (show (Set.Ioi (0 : unitInterval)).Nonempty from ⟨1, by norm_num⟩)]
    change (0 : unitInterval) ≤ 0
    exact le_rfl
  rw [← hz]
  exact (closure_mono (Set.image_subset_iff.mpr hpos))
    (image_closure_subset_closure_image hf ⟨0, hzero, rfl⟩)

/-- The closed characteristic simplex is the closure of its open cell.
    The statement is valid even when some boundary faces are identified. -/
theorem closure_cellInterior (K : SSet.{0}) (s : K.N) :
    closure (simplexPoint K s.simplex '' fullSupport s.dim) =
      Set.range (simplexPoint K s.simplex) := by
  have hd : closure (fullSupport s.dim) = Set.univ := (fullSupport_dense s.dim).closure_eq
  calc
    closure (simplexPoint K s.simplex '' fullSupport s.dim) =
        simplexPoint K s.simplex '' closure (fullSupport s.dim) :=
      (simplexPoint_isClosedMap K s.simplex).closure_image_eq_of_continuous
        (simplexPoint K s.simplex).continuous _
    _ = Set.range (simplexPoint K s.simplex) := by rw [hd, Set.image_univ]

end

end Thomason.Construction.RealizationPrism

end

end OAI
