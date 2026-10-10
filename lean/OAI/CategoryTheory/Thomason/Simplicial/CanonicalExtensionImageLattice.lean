import OAI.CategoryTheory.Thomason.Chains.HornChainRetraction
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionAnodyneHorn
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionCartesian
import OAI.CategoryTheory.Thomason.Simplicial.ConstructedExtensionLocalizer
import OAI.CategoryTheory.Thomason.Simplicial.ExhaustionWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.FiniteSingularRelativeLifting
import OAI.CategoryTheory.Thomason.Simplicial.FixedInternalPathMaps
import OAI.CategoryTheory.Thomason.Simplicial.InfiniteExtensionKan
import OAI.CategoryTheory.Thomason.Simplicial.KanBaseChangeExhaustion
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

namespace OAI

section

/-! # Boundary lifting through the actual extension colimit

This concerns the independently constructed right class of boundary
inclusions. It does not identify that class with weak Kan fibrations.
-/

namespace Thomason.Construction.InfiniteExtension

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Extension preserves the already defined boundary right lifting class. -/
theorem extension_boundary_rlp {X Y : SSet.{0}} (p : X ⟶ Y) (hp : I.rlp p) :
    I.rlp (SSet.ex.map p) := by
  rw [← SSet.rlp_monomorphisms] at hp ⊢
  intro A B i hi
  apply (SSet.sdExAdjunction.hasLiftingProperty_iff _ _).mp
  have : Mono i := hi
  exact hp _ (subdivision_map_mono i)

theorem stageMap_boundary_rlp {X Y : SSet.{0}} (p : X ⟶ Y) (hp : I.rlp p) (n : ℕ) :
    I.rlp (stageMap p n) := by
  induction n with
  | zero => exact hp
  | succ n ih => exact extension_boundary_rlp (stageMap p n) ih

/-- Every lifting square with finite source and target occurs in one
common stage of the two extension towers. -/
theorem map_finite_lifting {A B X Y : SSet.{0}} [A.Finite] [B.Finite]
    (i : A ⟶ B) (p : X ⟶ Y)
    (hp : ∀ m, HasLiftingProperty i (stageMap p m)) :
    HasLiftingProperty i (map p) := by
  refine ⟨fun {a b} sq => ?_⟩
  obtain ⟨r, a₀, ha₀⟩ := finite_map_factors X a
  obtain ⟨s, b₀, hb₀⟩ := finite_map_factors Y b
  let m := max r s
  let a₁ := a₀ ≫ (diagram X).map (homOfLE (Nat.le_max_left r s))
  let b₁ := b₀ ≫ (diagram Y).map (homOfLE (Nat.le_max_right r s))
  have ha₁ : a₁ ≫ inclusion X m = a := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => a₀ ≫ f)
        (colimit.w (diagram X) (homOfLE (Nat.le_max_left r s)))).trans ha₀)
  have hb₁ : b₁ ≫ inclusion Y m = b := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => b₀ ≫ f)
        (colimit.w (diagram Y) (homOfLE (Nat.le_max_right r s)))).trans hb₀)
  have hh : a₁ ≫ stageMap p m = i ≫ b₁ := by
    apply (cancel_mono (inclusion Y m)).mp
    calc
      (a₁ ≫ stageMap p m) ≫ inclusion Y m =
          (a₁ ≫ inclusion X m) ≫ map p := by
        rw [Category.assoc, ← inclusion_map, ← Category.assoc]
      _ = a ≫ map p := by rw [ha₁]
      _ = i ≫ b := sq.w
      _ = (i ≫ b₁) ≫ inclusion Y m := by rw [Category.assoc, hb₁]
  have := hp m
  let t : CommSq a₁ i (stageMap p m) b₁ := ⟨hh⟩
  refine ⟨⟨{ l := t.lift ≫ inclusion X m, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, t.fac_left, ha₁]
  · rw [Category.assoc, inclusion_map, ← Category.assoc, t.fac_right, hb₁]

/-- The extension colimit preserves the boundary right lifting class. -/
theorem map_boundary_rlp {X Y : SSet.{0}} (p : X ⟶ Y) (hp : I.rlp p) :
    I.rlp (map p) := by
  intro A B i hi
  obtain ⟨n⟩ := hi
  apply map_finite_lifting
  intro m
  exact stageMap_boundary_rlp _ hp m _ (boundary_ι_mem_I n)

end

end Thomason.Construction.InfiniteExtension

end

section

/-! # Exact relative weak comparison for the constructed Kan replacement

The union of the original target and the Kan replacement of its prescribed
subcomplex is a weak subcomplex of the Kan replacement of the target.
-/

namespace Thomason.Construction.InfiniteExtension

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- This relative comparison retains both the original target and the
entire replacement of its prescribed subcomplex. -/
def relativeUnit {A B : SSet.{0}} (i : A ⟶ B) :
    pushout i (unit A) ⟶ obj B :=
  pushout.desc (unit B) (map i) (coaugmentation.naturality i)

@[reassoc] theorem relativeUnit_inl {A B : SSet.{0}} (i : A ⟶ B) :
    pushout.inl i (unit A) ≫ relativeUnit i = unit B :=
  pushout.inl_desc _ _ _

@[reassoc] theorem relativeUnit_inr {A B : SSet.{0}} (i : A ⟶ B) :
    pushout.inr i (unit A) ≫ relativeUnit i = map i :=
  pushout.inr_desc _ _ _

instance relativeUnit_mono {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
    Mono (relativeUnit i) := by
  have : Mono (map i) := by
    change Mono (functor.map i)
    infer_instance
  have : Mono (unit B) := inferInstanceAs (Mono (inclusion B 0))
  let sq := IsPushout.of_hasPushout i (unit A)
  have he : relativeUnit i = sq.desc (unit B) (map i) (unit_isPullback i).w := by
    apply pushout.hom_ext
    · exact (relativeUnit_inl i).trans (sq.inl_desc _ _ _).symm
    · exact (relativeUnit_inr i).trans (sq.inr_desc _ _ _).symm
  rw [he]
  exact sq.desc_mono_of_isPullback (unit_isPullback i)

/-- The exact relative comparison is an actual realization weak equivalence.
No recognition of acyclic monomorphisms as anodyne maps is used. -/
theorem relativeUnit_weak {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
    realizationWeakEquivalences (relativeUnit i) := by
  have hleft : realizationWeakEquivalences (pushout.inl i (unit A)) := by
    let W := MorphismProperty.monomorphisms SSet.{0} ⊓ realizationWeakEquivalences
    have hA : W (unit A) := ⟨inferInstanceAs (Mono (inclusion A 0)), unit_weak A⟩
    exact (W.of_isPushout (IsPushout.of_hasPushout i (unit A)) hA).2
  apply realizationWeakEquivalences.of_precomp (pushout.inl i (unit A)) (relativeUnit i) hleft
  rw [relativeUnit_inl]
  exact unit_weak B

end

end Thomason.Construction.InfiniteExtension

end

section

/-! # Finite original carriers in the extension colimit

A finite family in the constructed Kan replacement is supported over one
finite subcomplex of the original simplicial set, as well as one stage.
-/

namespace Thomason.Construction.InfiniteExtension

open CategoryTheory

noncomputable section

/-- The finite carrier can be chosen in the original source, through any
specified finite number of extensions. -/
theorem finite_stage_map_factors {T X : SSet.{0}} [T.Finite]
    (n : ℕ) (f : T ⟶ stage X n) :
    ∃ A : X.Subcomplex, SSet.Finite A.toSSet ∧
      ∃ g : T ⟶ stage A.toSSet n, g ≫ stageMap A.ι n = f := by
  induction n generalizing T with
  | zero =>
    let A := SSet.Subcomplex.range f
    exact ⟨A, inferInstance, SSet.Subcomplex.toRange f, rfl⟩
  | succ n ih =>
    obtain ⟨B, hB, b, hb⟩ := finite_map_extension_factors f
    have := hB
    obtain ⟨A, hA, a, ha⟩ := ih B.ι
    refine ⟨A, hA, b ≫ SSet.ex.map a, ?_⟩
    change (b ≫ SSet.ex.map a) ≫ SSet.ex.map (stageMap A.ι n) = f
    rw [Category.assoc, ← SSet.ex.map_comp, ha]
    exact hb

/-- Every finite family in the colimit is induced from the colimit over
one finite subcomplex of the original object. -/
theorem finite_original_map_factors {T X : SSet.{0}} [T.Finite]
    (f : T ⟶ obj X) :
    ∃ A : X.Subcomplex, SSet.Finite A.toSSet ∧
      ∃ g : T ⟶ obj A.toSSet, g ≫ map A.ι = f := by
  obtain ⟨n, b, hb⟩ := finite_map_factors X f
  obtain ⟨A, hA, a, ha⟩ := finite_stage_map_factors n b
  refine ⟨A, hA, a ≫ inclusion A.toSSet n, ?_⟩
  rw [Category.assoc, inclusion_map, ← Category.assoc, ha, hb]

/-- Compact continuous families also have a finite original carrier.
The factorization is an exact equality of continuous maps. -/
theorem compact_original_map_factors {Z : Type} [TopologicalSpace Z] [CompactSpace Z]
    (X : SSet.{0}) (f : C(Z, SSet.toTop.obj (obj X))) :
    ∃ A : X.Subcomplex, SSet.Finite A.toSSet ∧
      ∃ g : C(Z, SSet.toTop.obj (obj A.toSSet)),
        (SSet.toTop.map (map A.ι)).hom.comp g = f := by
  obtain ⟨T, hT, u, hu⟩ := RealizationPrism.compact_map_factors (obj X) f
  have := hT
  obtain ⟨A, hA, a, ha⟩ := finite_original_map_factors T.ι
  refine ⟨A, hA, (SSet.toTop.map a).hom.comp u, ?_⟩
  calc
    _ = (SSet.toTop.map (a ≫ map A.ι)).hom.comp u := by
      rw [SSet.toTop.map_comp]
      rfl
    _ = f := by rw [ha]; exact hu

end

end Thomason.Construction.InfiniteExtension

end

section

/-! # Relative finite original carriers for the extension colimit -/

namespace Thomason.Construction.InfiniteExtension

open CategoryTheory

noncomputable section

/-- A finite family with boundary in the original object factors over one
finite original subcomplex, retaining that complete boundary exactly. -/
theorem finite_relative_original_map_factors {A K X : SSet.{0}} [K.Finite]
    (i : A ⟶ K) [Mono i] (a : A ⟶ X) (f : K ⟶ obj X)
    (hf : i ≫ f = a ≫ unit X) :
    ∃ S : X.Subcomplex, SSet.Finite S.toSSet ∧
      ∃ (aS : A ⟶ S.toSSet) (g : K ⟶ obj S.toSSet),
        aS ≫ S.ι = a ∧ g ≫ map S.ι = f ∧ i ≫ g = aS ≫ unit S.toSSet := by
  have : A.Finite := SSet.finite_of_mono i
  obtain ⟨T, hT, g₀, hg₀⟩ := finite_original_map_factors f
  have := hT
  let S : X.Subcomplex := T ⊔ SSet.Subcomplex.range a
  have hS : SSet.Finite S.toSSet := by
    let U : Bool → X.Subcomplex := fun b => if b then T else SSet.Subcomplex.range a
    have he : S = iSup U := by
      apply le_antisymm
      · apply sup_le
        · exact le_iSup U true
        · exact le_iSup U false
      · apply iSup_le
        intro b
        cases b
        · exact le_sup_right
        · exact le_sup_left
    rw [he]
    apply (SSet.finite_iSup_iff U).mpr
    intro b
    cases b <;> dsimp [U] <;> infer_instance
  let j : T.toSSet ⟶ S.toSSet := SSet.Subcomplex.homOfLE le_sup_left
  let aS : A ⟶ S.toSSet := S.lift a le_sup_right
  let g : K ⟶ obj S.toSSet := g₀ ≫ map j
  have ha : aS ≫ S.ι = a := rfl
  have hj : j ≫ S.ι = T.ι := rfl
  have hg : g ≫ map S.ι = f := by
    dsimp only [g]
    rw [Category.assoc, ← map_comp, hj, hg₀]
  have : Mono (map S.ι) := inferInstanceAs (Mono (functor.map S.ι))
  refine ⟨S, hS, aS, g, ha, hg, ?_⟩
  apply (cancel_mono (map S.ι)).mp
  rw [Category.assoc, hg, hf, Category.assoc]
  have hn : unit S.toSSet ≫ map S.ι = S.ι ≫ unit X :=
    (coaugmentation.naturality S.ι).symm
  rw [hn, ← Category.assoc, ha]

end

end Thomason.Construction.InfiniteExtension

end

section

/-! # Relative canonical extension preserves the prescribed subcomplex

The actual union of B and Ex A in Ex B is a weak subcomplex. This concerns
geometric realization and does not use recognition of weak monomorphisms
as anodyne maps.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- The original target and the extension of its entire prescribed
subcomplex together include weakly into the extended target. -/
theorem relativeCanonicalExtension_weak {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
    realizationWeakEquivalences (relativeCanonicalExtension i) := by
  have hleft : realizationWeakEquivalences
      (pushout.inl i (canonicalExtension.app A)) := by
    let W := MorphismProperty.monomorphisms SSet.{0} ⊓ realizationWeakEquivalences
    have hA : W (canonicalExtension.app A) :=
      ⟨canonicalExtension_mono A, canonicalExtension_weak A⟩
    exact (W.of_isPushout (IsPushout.of_hasPushout i (canonicalExtension.app A)) hA).2
  apply realizationWeakEquivalences.of_precomp
    (pushout.inl i (canonicalExtension.app A)) (relativeCanonicalExtension i) hleft
  rw [relativeCanonicalExtension_inl]
  exact canonicalExtension_weak B

/-- The relative comparison is both an actual subcomplex inclusion and
an actual realization weak equivalence. -/
theorem relativeCanonicalExtension_weak_mono {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
    (MorphismProperty.monomorphisms SSet.{0} ⊓ realizationWeakEquivalences)
      (relativeCanonicalExtension i) :=
  ⟨inferInstance, relativeCanonicalExtension_weak i⟩

end

end Thomason.Construction

end

section

/-! # Exact coordinate loci of faces and finite face unions

The coordinate description is proved for the actual realization arrows,
so it can restrict the barycentric homeomorphism to arbitrary subcomplexes.
-/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

theorem standard_face_carrier_iff (n : ℕ) (S : Finset (Fin (n+1)))
    (p : StdSimplex ℝ (Fin (n+1))) :
    simplexCarrier (Δ[n] : SSet.{0}) (SSet.yonedaEquiv (𝟙 _)) p ≤
      SSet.stdSimplex.face.{0} S ↔ ∀ i ∉ S, p.weights i = 0 := by
  let a : SimplexCategory.mk (HornBarycentric.supportLen p) ⟶ .mk n :=
    SimplexCategory.Hom.mk (HornBarycentric.supportMap p).toOrderHom
  change SSet.Subcomplex.ofSimplex ((Δ[n] : SSet.{0}).map a.op
    (SSet.yonedaEquiv (𝟙 _))) ≤ SSet.stdSimplex.face.{0} S ↔ _
  rw [SSet.Subcomplex.ofSimplex_le_iff, SSet.yonedaEquiv_naturality,
    Category.comp_id, SSet.yonedaEquiv_map, SSet.stdSimplex.mem_face_iff]
  change (∀ j, HornBarycentric.supportMap p j ∈ S) ↔ _
  constructor
  · intro h i hi
    apply Finsupp.notMem_support_iff.mp
    intro hp
    have hr : i ∈ Set.range (HornBarycentric.supportMap p) := by
      rw [HornBarycentric.supportMap_range]
      exact hp
    obtain ⟨j, rfl⟩ := hr
    exact hi (h j)
  · intro h j
    by_contra hj
    exact (Finsupp.mem_support_iff.mp (HornBarycentric.supportMap_mem p j))
      (h _ hj)

theorem standard_face_point_iff (n : ℕ) (S : Finset (Fin (n+1)))
    (p : StdSimplex ℝ (Fin (n+1))) :
    (SimplexCategory.mk n).toTopHomeo.symm p ∈
      Set.range (SSet.toTop.map (SSet.stdSimplex.face.{0} S).ι).hom ↔
        ∀ i ∉ S, p.weights i = 0 := by
  have h : simplexPoint (Δ[n] : SSet.{0}) (SSet.yonedaEquiv (𝟙 _)) p ∈
      Set.range (SSet.toTop.map (SSet.stdSimplex.face.{0} S).ι).hom ↔
        ∀ i ∉ S, p.weights i = 0 := by
    rw [mem_range_inclusion_iff, carrier_simplexPoint, standard_face_carrier_iff]
  exact (Iff.of_eq (congrArg
    (fun z => z ∈ Set.range (SSet.toTop.map (SSet.stdSimplex.face.{0} S).ι).hom)
    (simplexPoint_standard_id n p)).symm).trans h

theorem standard_faceUnion_point_iff {n : ℕ} (F : Finset (Finset (Fin (n+1))))
    (p : StdSimplex ℝ (Fin (n+1))) :
    (SimplexCategory.mk n).toTopHomeo.symm p ∈
      Set.range (SSet.toTop.map (faceUnion F).ι).hom ↔
        ∃ S ∈ F, ∀ i ∉ S, p.weights i = 0 := by
  rw [faceUnion, Finset.sup_eq_iSup, range_iSup_inclusion, Set.mem_iUnion]
  apply exists_congr
  intro S
  classical
  let R (A : (Δ[n] : SSet.{0}).Subcomplex) :=
    (SimplexCategory.mk n).toTopHomeo.symm p ∈ Set.range (SSet.toTop.map A.ι).hom
  change R (⨆ (_ : S ∈ F), SSet.stdSimplex.face.{0} S) ↔
    S ∈ F ∧ ∀ i ∉ S, p.weights i = 0
  by_cases hS : S ∈ F
  · have he : (⨆ (_ : S ∈ F), SSet.stdSimplex.face.{0} S) =
        SSet.stdSimplex.face.{0} S := iSup_pos hS
    rw [he]
    simp only [hS, true_and]
    exact standard_face_point_iff n S p
  · have he : (⨆ (_ : S ∈ F), SSet.stdSimplex.face.{0} S) =
        (⊥ : (Δ[n] : SSet.{0}).Subcomplex) := iSup_neg hS
    rw [he]
    simp only [hS, false_and, iff_false]
    dsimp only [R]
    rw [mem_range_iff_normalization]
    exact Set.notMem_empty _

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Common face support of barycentric and last-vertex maps

Every original face containing the barycentric image also contains the
last-vertex image. This makes their straight interpolation remain in
the same finite face union.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity RealizationPrism
open scoped Simplicial

noncomputable section

def lastVertexCoordinates (n : ℕ) :
    C(SSet.toTop.obj (nerve (Faces n)), StdSimplex ℝ (Fin (n+1))) :=
  ((SimplexCategory.mk n).toTopHomeo : C(_, _)).comp
    (SSet.toTop.map (simplexLastVertex.app (.mk n))).hom

theorem subdividedFace_lastVertex {n : ℕ} (S : Finset (Fin (n+1))) :
    subdividedFaceMap S ≫ simplexLastVertex.app (.mk n) =
      lastVertex.app (SSet.stdSimplex.face.{0} S).toSSet ≫ (SSet.stdSimplex.face.{0} S).ι := by
  have he : SSet.stdSimplex.sdIso.hom.app (.mk n) ≫ simplexLastVertex.app (.mk n) =
      lastVertex.app (Δ[n] : SSet.{0}) := by
    rw [← lastVertex_on_standard_simplex, ← Category.assoc]
    simp
  rw [subdividedFaceMap, Category.assoc, he]
  exact lastVertex.naturality (SSet.stdSimplex.face.{0} S).ι

theorem lastVertexCoordinates_face {n : ℕ} (S : Finset (Fin (n+1)))
    (z : SSet.toTop.obj (nerve (Faces n)))
    (hz : ∀ i ∉ S, (point n z).weights i = 0) :
    ∀ i ∉ S, (lastVertexCoordinates n z).weights i = 0 := by
  have hc : carrier (nerve (Faces n)) z ≤ subdividedFace S := by
    rw [subdividedFace_eq_permitted]
    exact (point_face_preimage n (S : Set (Fin (n+1))) z).mp hz
  have hr : z ∈ Set.range (SSet.toTop.map (subdividedFaceMap S)).hom := by
    have hz' : z ∈ Set.range (SSet.toTop.map (subdividedFace S).ι).hom :=
      (mem_range_inclusion_iff (nerve (Faces n)) (subdividedFace S) z).mpr hc
    have he := congrArg (fun A => Set.range (SSet.toTop.map A.ι).hom)
      (subdividedFaceMap_range S)
    have hm := range_realized_map (subdividedFaceMap S)
    exact (hm.trans he) ▸ hz'
  obtain ⟨y, rfl⟩ := hr
  apply (standard_face_point_iff n S _).mp
  refine ⟨(SSet.toTop.map (lastVertex.app (SSet.stdSimplex.face.{0} S).toSSet)).hom y, ?_⟩
  change _ = (SimplexCategory.mk n).toTopHomeo.symm
    ((SimplexCategory.mk n).toTopHomeo _)
  rw [Homeomorph.symm_apply_apply]
  have he := congrArg (fun f => SSet.toTop.map f) (subdividedFace_lastVertex S)
  simp only [Functor.map_comp] at he
  exact (ConcreteCategory.congr_hom he y).symm

/-- A zero barycentric coordinate stays zero under the last-vertex map. -/
theorem lastVertexCoordinates_zero {n : ℕ} (z : SSet.toTop.obj (nerve (Faces n)))
    (i : Fin (n+1)) (hi : (point n z).weights i = 0) :
    (lastVertexCoordinates n z).weights i = 0 := by
  classical
  have h := lastVertexCoordinates_face ({i}ᶜ : Finset (Fin (n+1))) z (by
    intro j hj
    have hji : j = i := by simpa using hj
    simpa only [hji] using hi)
  exact h i (by simp)

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # A face-preserving homotopy to the actual last-vertex map

The barycentric homeomorphism and the Kan descent map use the same
parameter up to a homotopy which stays inside every prescribed face.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity RealizationPrism

noncomputable section

def lastVertexHomotopy (n : ℕ) : (map n).Homotopy (lastVertexCoordinates n) where
  toFun p := PosetGeometry.blend (point n p.2) (lastVertexCoordinates n p.2) p.1
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff]
    apply continuous_pi
    intro i
    simp only [Function.comp_def, PosetGeometry.blend, StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      unitInterval.coe_symm_eq]
    have hp : Continuous (fun p : unitInterval × SSet.toTop.obj (nerve (Faces n)) =>
        (point n p.2).weights i) :=
      (StdSimplex.continuous_weights_apply ℝ i).comp ((map n).continuous.comp continuous_snd)
    have hl : Continuous (fun p : unitInterval × SSet.toTop.obj (nerve (Faces n)) =>
        (lastVertexCoordinates n p.2).weights i) :=
      (StdSimplex.continuous_weights_apply ℝ i).comp
        ((lastVertexCoordinates n).continuous.comp continuous_snd)
    exact ((continuous_const.sub continuous_fst.subtype_val).mul hp).add
      (continuous_fst.subtype_val.mul hl)
  map_zero_left z := PosetGeometry.blend_zero _ _
  map_one_left z := PosetGeometry.blend_one _ _

/-- The homotopy never introduces a new positive coordinate. -/
theorem lastVertexHomotopy_zero {n : ℕ} (z : SSet.toTop.obj (nerve (Faces n)))
    (t : unitInterval) (i : Fin (n+1)) (hi : (point n z).weights i = 0) :
    (lastVertexHomotopy n (t, z)).weights i = 0 := by
  have hl := lastVertexCoordinates_zero z i hi
  change (PosetGeometry.blend (point n z) (lastVertexCoordinates n z) t).weights i = 0
  simp [PosetGeometry.blend, hi, hl]

/-- In particular the same complete face is retained at every time. -/
theorem lastVertexHomotopy_face {n : ℕ} (S : Finset (Fin (n+1)))
    (z : SSet.toTop.obj (nerve (Faces n))) (t : unitInterval)
    (hz : ∀ i ∉ S, (point n z).weights i = 0) :
    ∀ i ∉ S, (lastVertexHomotopy n (t, z)).weights i = 0 :=
  fun i hi => lastVertexHomotopy_zero z t i (hz i hi)

theorem lastVertexHomotopy_faceUnion {n : ℕ} (F : Finset (Finset (Fin (n+1))))
    (z : SSet.toTop.obj (nerve (Faces n))) (t : unitInterval)
    (hz : ∃ S ∈ F, ∀ i ∉ S, (point n z).weights i = 0) :
    ∃ S ∈ F, ∀ i ∉ S, (lastVertexHomotopy n (t, z)).weights i = 0 := by
  obtain ⟨S, hS, hz⟩ := hz
  exact ⟨S, hS, lastVertexHomotopy_face S z t hz⟩

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # An exact finite-stage horn retraction for the extension tower -/

namespace Thomason.Construction

open CategoryTheory PartialOrder
open scoped Simplicial

noncomputable section

private def equalRangeIso {A B C : SSet.{0}} (f : A ⟶ C) (g : B ⟶ C)
    [Mono f] [Mono g] (h : SSet.Subcomplex.range f = SSet.Subcomplex.range g) : A ≅ B :=
  asIso (SSet.Subcomplex.toRange f) ≪≫
    { hom := SSet.Subcomplex.homOfLE h.le
      inv := SSet.Subcomplex.homOfLE h.ge
      hom_inv_id := by ext d x; rfl
      inv_hom_id := by ext d x; rfl } ≪≫
    (asIso (SSet.Subcomplex.toRange g)).symm

private theorem equalRangeIso_fac {A B C : SSet.{0}} (f : A ⟶ C) (g : B ⟶ C)
    [Mono f] [Mono g] (h : SSet.Subcomplex.range f = SSet.Subcomplex.range g) :
    (equalRangeIso f g h).hom ≫ g = f := by
  have hg : inv (SSet.Subcomplex.toRange g) ≫ g = (SSet.Subcomplex.range g).ι := by
    calc
      _ = inv (SSet.Subcomplex.toRange g) ≫
          (SSet.Subcomplex.toRange g ≫ (SSet.Subcomplex.range g).ι) :=
        congrArg (fun q => inv (SSet.Subcomplex.toRange g) ≫ q)
          (SSet.Subcomplex.toRange_ι g).symm
      _ = _ := IsIso.inv_hom_id_assoc _ _
  change ((SSet.Subcomplex.toRange f ≫ SSet.Subcomplex.homOfLE h.le) ≫
    inv (SSet.Subcomplex.toRange g)) ≫ g = f
  rw [Category.assoc, hg, Category.assoc, SSet.Subcomplex.homOfLE_ι]
  rfl

def subdivisionFaceIso (n : SimplexCategory) :
    SSet.sd.obj (SSet.stdSimplex.obj n) ≅
      nerve (NonemptyFiniteChains (ULift.{0} (Fin (n.len+1)))) :=
  SSet.stdSimplex.sdIso.app n

def originalMaximum (n : SimplexCategory) :
    NonemptyFiniteChains (ULift.{0} (Fin (n.len+1))) →o ULift.{0} (Fin (n.len+1)) :=
  chainMaximumHom

def originalMaximumNerve (n : SimplexCategory) :
    nerve (NonemptyFiniteChains (ULift.{0} (Fin (n.len+1)))) ⟶
      nerve (ULift.{0} (Fin (n.len+1))) :=
  nerveMap (originalMaximum n).monotone.functor

def originalSimplexIso (n : SimplexCategory) :
    SSet.stdSimplex.obj n ≅ nerve (ULift.{0} (Fin (n.len+1))) :=
  simplexNerveIso.app n

def originalLastVertex (n : SimplexCategory) :
    nerve (NonemptyFiniteChains (ULift.{0} (Fin (n.len+1)))) ⟶ SSet.stdSimplex.obj n :=
  simplexLastVertex.app n

def hornIntoFaces (n : ℕ) (k : Fin (n+2)) :
    SSet.sd.obj (SSet.horn.{0} (n+1) k) ⟶ nerve (SubdivisionHornFaces.Faces n) :=
  SSet.sd.map (SSet.horn.{0} (n+1) k).ι ≫ (subdivisionFaceIso ⦋n+1⦌).hom

instance hornIntoFaces_mono (n : ℕ) (k : Fin (n+2)) : Mono (hornIntoFaces n k) := by
  have : Mono (SSet.sd.map (SSet.horn.{0} (n+1) k).ι) := subdivision_map_mono _
  change Mono (SSet.sd.map (SSet.horn.{0} (n+1) k).ι ≫ (subdivisionFaceIso ⦋n+1⦌).hom)
  infer_instance

def hornFaceInclusion (n : ℕ) (k : Fin (n+2)) :
    nerve (SubdivisionHornFaces.HornFaces n k) ⟶ nerve (SubdivisionHornFaces.Faces n) :=
  nerveMap ((SubdivisionHornFaces.remainderInclusion n k).comp
    (SubdivisionHornFaces.inclusion n k)).monotone.functor

instance hornFaceInclusion_mono (n : ℕ) (k : Fin (n+2)) : Mono (hornFaceInclusion n k) :=
  SubdivisionHornFaces.nerveMap_mono _ (fun _ _ h => Subtype.ext (Subtype.ext h))

def hornSubdivisionIso (n : ℕ) (k : Fin (n+2)) :
    SSet.sd.obj (SSet.horn.{0} (n+1) k) ≅ nerve (SubdivisionHornFaces.HornFaces n k) := by
  exact equalRangeIso (hornIntoFaces n k) (hornFaceInclusion n k)
    ((subdivision_horn_range n k).trans (hornFaceNerve_range n k).symm)

theorem hornSubdivisionIso_fac (n : ℕ) (k : Fin (n+2)) :
    (hornSubdivisionIso n k).hom ≫ hornFaceInclusion n k =
      hornIntoFaces n k :=
  equalRangeIso_fac (hornIntoFaces n k) (hornFaceInclusion n k) _

theorem subdivision_lastVertex_standard_chain (n : SimplexCategory) :
    SSet.sd.map (lastVertex.app (SSet.stdSimplex.obj n)) ≫ (subdivisionFaceIso n).hom =
      SSet.sd.map (subdivisionFaceIso n).hom ≫
        NerveSubdivisionMap.map (NonemptyFiniteChains (ULift.{0} (Fin (n.len+1)))) ≫
        NerveSubdivisionMap.chainNerveMap (originalMaximum n) := by
  let v := (originalSimplexIso n).hom
  have hLV : originalLastVertex n ≫ v = originalMaximumNerve n := by
    change (originalMaximumNerve n ≫ (originalSimplexIso n).inv) ≫
      (originalSimplexIso n).hom = originalMaximumNerve n
    rw [Category.assoc, Iso.inv_hom_id]
    exact Category.comp_id _
  have hformula : (subdivisionFaceIso n).hom ≫ originalLastVertex n =
      lastVertex.app (SSet.stdSimplex.obj n) := lastVertex_standard_formula n
  have he : lastVertex.app (SSet.stdSimplex.obj n) ≫ v =
      (subdivisionFaceIso n).hom ≫ originalMaximumNerve n := by
    calc
      _ = ((subdivisionFaceIso n).hom ≫ originalLastVertex n) ≫ v :=
        congrArg (fun q => q ≫ v) hformula.symm
      _ = _ := by rw [Category.assoc, hLV]
  have hStd : SSet.sd.map v ≫ NerveSubdivisionMap.map (ULift.{0} (Fin (n.len+1))) =
      (subdivisionFaceIso n).hom := NerveSubdivisionMap.map_standard n
  calc
    _ = SSet.sd.map (lastVertex.app (SSet.stdSimplex.obj n)) ≫
        (SSet.sd.map v ≫ NerveSubdivisionMap.map (ULift.{0} (Fin (n.len+1)))) :=
      congrArg (fun q => SSet.sd.map (lastVertex.app (SSet.stdSimplex.obj n)) ≫ q) hStd.symm
    _ = SSet.sd.map (lastVertex.app (SSet.stdSimplex.obj n) ≫ v) ≫
        NerveSubdivisionMap.map (ULift.{0} (Fin (n.len+1))) := by
      rw [SSet.sd.map_comp, Category.assoc]
    _ = SSet.sd.map ((subdivisionFaceIso n).hom ≫ originalMaximumNerve n) ≫
        NerveSubdivisionMap.map (ULift.{0} (Fin (n.len+1))) :=
      congrArg (fun q => SSet.sd.map q ≫ NerveSubdivisionMap.map (ULift.{0} (Fin (n.len+1)))) he
    _ = SSet.sd.map (subdivisionFaceIso n).hom ≫
        (SSet.sd.map (originalMaximumNerve n) ≫
          NerveSubdivisionMap.map (ULift.{0} (Fin (n.len+1)))) := by
      rw [SSet.sd.map_comp, Category.assoc]
    _ = _ := congrArg (fun q => SSet.sd.map (subdivisionFaceIso n).hom ≫ q)
      (NerveSubdivisionMap.map_naturality (originalMaximum n))

def rawHornRetraction (n : ℕ) (k : Fin (n+2)) :
    SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.obj ⦋n+1⦌)) ⟶
      nerve (SubdivisionHornFaces.HornFaces n k) :=
  SSet.sd.map (subdivisionFaceIso ⦋n+1⦌).hom ≫
    NerveSubdivisionMap.map (SubdivisionHornFaces.Faces n) ≫
      nerveMap (HornChainRetraction.retraction n k).monotone.functor

private theorem old_chain_retraction (n : ℕ) (k : Fin (n+2)) :
    NerveSubdivisionMap.chainNerveMap
      ((SubdivisionHornFaces.remainderInclusion n k).comp (SubdivisionHornFaces.inclusion n k)) ≫
      nerveMap (HornChainRetraction.retraction n k).monotone.functor ≫ hornFaceInclusion n k =
    NerveSubdivisionMap.chainNerveMap
      ((SubdivisionHornFaces.remainderInclusion n k).comp (SubdivisionHornFaces.inclusion n k)) ≫
      NerveSubdivisionMap.chainNerveMap (originalMaximum ⦋n+1⦌) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext t
  apply HornChainRetraction.retraction_old
  intro A hA
  obtain ⟨B, _, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp hA
  exact ⟨B.val.property, B.property⟩

theorem rawHornRetraction_fac (n : ℕ) (k : Fin (n+2)) :
    SSet.sd.map (SSet.sd.map (SSet.horn.{0} (n+1) k).ι) ≫ rawHornRetraction n k ≫
      hornFaceInclusion n k =
    SSet.sd.map (lastVertex.app (SSet.horn.{0} (n+1) k : SSet)) ≫
      hornIntoFaces n k := by
  let i := (SSet.horn.{0} (n+1) k).ι
  let e := hornSubdivisionIso n k
  let g := hornFaceInclusion n k
  let G := ((SubdivisionHornFaces.remainderInclusion n k).comp
    (SubdivisionHornFaces.inclusion n k))
  have hf : SSet.sd.map (SSet.sd.map i) ≫
      SSet.sd.map (subdivisionFaceIso ⦋n+1⦌).hom ≫
      NerveSubdivisionMap.map (SubdivisionHornFaces.Faces n) =
      SSet.sd.map e.hom ≫ NerveSubdivisionMap.map (SubdivisionHornFaces.HornFaces n k) ≫
        NerveSubdivisionMap.chainNerveMap G := by
    calc
      _ = SSet.sd.map (hornIntoFaces n k) ≫
          NerveSubdivisionMap.map (SubdivisionHornFaces.Faces n) := by
        change _ = SSet.sd.map (SSet.sd.map i ≫ (subdivisionFaceIso ⦋n+1⦌).hom) ≫ _
        rw [SSet.sd.map_comp, Category.assoc]
      _ = SSet.sd.map (e.hom ≫ g) ≫ NerveSubdivisionMap.map (SubdivisionHornFaces.Faces n) :=
        congrArg (fun q => SSet.sd.map q ≫ NerveSubdivisionMap.map (SubdivisionHornFaces.Faces n))
          (hornSubdivisionIso_fac n k).symm
      _ = SSet.sd.map e.hom ≫
          (SSet.sd.map g ≫ NerveSubdivisionMap.map (SubdivisionHornFaces.Faces n)) := by
        rw [SSet.sd.map_comp, Category.assoc]
      _ = _ := congrArg (fun q => SSet.sd.map e.hom ≫ q) (NerveSubdivisionMap.map_naturality G)
  have hn := congrArg (fun q => SSet.sd.map q) (lastVertex.naturality i)
  simp only [SSet.sd.map_comp] at hn
  calc
    _ = (SSet.sd.map e.hom ≫ NerveSubdivisionMap.map (SubdivisionHornFaces.HornFaces n k)) ≫
          (NerveSubdivisionMap.chainNerveMap G ≫
            nerveMap (HornChainRetraction.retraction n k).monotone.functor ≫ g) := by
      have h := congrArg (fun q => q ≫
        (nerveMap (HornChainRetraction.retraction n k).monotone.functor ≫ g)) hf
      simpa only [rawHornRetraction, Category.assoc] using h
    _ = (SSet.sd.map e.hom ≫ NerveSubdivisionMap.map (SubdivisionHornFaces.HornFaces n k)) ≫
          (NerveSubdivisionMap.chainNerveMap G ≫
            NerveSubdivisionMap.chainNerveMap (originalMaximum ⦋n+1⦌)) := by
      rw [old_chain_retraction]
    _ = SSet.sd.map (SSet.sd.map i) ≫
          (SSet.sd.map (subdivisionFaceIso ⦋n+1⦌).hom ≫
            NerveSubdivisionMap.map (SubdivisionHornFaces.Faces n) ≫
            NerveSubdivisionMap.chainNerveMap (originalMaximum ⦋n+1⦌)) := by
      have h := congrArg (fun q => q ≫ NerveSubdivisionMap.chainNerveMap
        (originalMaximum ⦋n+1⦌)) hf.symm
      simpa only [Category.assoc] using h
    _ = SSet.sd.map (SSet.sd.map i) ≫
          (SSet.sd.map (lastVertex.app (SSet.stdSimplex.obj ⦋n+1⦌)) ≫
            (subdivisionFaceIso ⦋n+1⦌).hom) := by
      rw [subdivision_lastVertex_standard_chain]
    _ = _ := by
      rw [← Category.assoc, hn, Category.assoc]
      rfl

/-- After two subdivisions, a simplex retracts into the once-subdivided
horn with restriction exactly `Sd(lastVertex_horn)`. This is the finite-stage
extension identity used to fill horns in the extension tower. -/
def subdivisionHornRetraction (n : ℕ) (k : Fin (n+2)) :
    SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.obj ⦋n+1⦌)) ⟶
      SSet.sd.obj (SSet.horn.{0} (n+1) k) :=
  rawHornRetraction n k ≫ (hornSubdivisionIso n k).inv

theorem subdivisionHornRetraction_fac (n : ℕ) (k : Fin (n+2)) :
    SSet.sd.map (SSet.sd.map (SSet.horn.{0} (n+1) k).ι) ≫ subdivisionHornRetraction n k =
      SSet.sd.map (lastVertex.app (SSet.horn.{0} (n+1) k : SSet)) := by
  apply (cancel_mono ((hornSubdivisionIso n k).hom ≫ hornFaceInclusion n k)).mp
  simp only [subdivisionHornRetraction, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hornSubdivisionIso_fac]
  exact rawHornRetraction_fac n k

end

end Thomason.Construction

end

section

/-! # Exact canonical-extension lifting on subdivided simplices -/

namespace Thomason.Construction

open CategoryTheory PartialOrder
open scoped Simplicial

noncomputable section

/-- Transport the canonical-extension anodyne property through an actual
simplicial isomorphism. -/
theorem canonicalExtension_anodyne_of_iso {X Y : SSet.{0}} (e : X ≅ Y)
    (hY : SSet.anodyneExtensions (canonicalExtension.app Y)) :
    SSet.anodyneExtensions (canonicalExtension.app X) := by
  have hn : e.hom ≫ canonicalExtension.app Y =
      canonicalExtension.app X ≫ SSet.ex.map e.hom := canonicalExtension.naturality e.hom
  have he : (e.hom ≫ canonicalExtension.app Y) ≫ SSet.ex.map e.inv =
      canonicalExtension.app X := by
    rw [hn, Category.assoc, ← SSet.ex.map_comp, e.hom_inv_id, SSet.ex.map_id,
      Category.comp_id]
  rw [← he]
  exact SSet.anodyneExtensions.comp_mem _ _
    (SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _) hY)
    (SSet.anodyneExtensions.of_isIso _)

/-- A greatest vertex supplies the concrete simplicial contraction used
for the face-poset nerve. -/
theorem canonicalExtension_anodyne_nerve_greatest {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ x, x ≤ v) :
    SSet.anodyneExtensions (canonicalExtension.app (nerve P)) := by
  let z := NormalizedSimplexIdentities.orderSimplex (OrderHom.const (Fin 1) v)
  let f : nerve P ⟶ (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from _
  let g : (Δ[0] : SSet.{0}) ⟶ nerve P := SSet.const z
  have hc : nerveMap (OrderHom.const P v).monotone.functor =
      SSet.const (X := nerve P) z := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    rfl
  apply canonicalExtension_anodyne_of_contraction (nerve P) f g
  simpa only [orderNerveMap_id, hc, g, SSet.comp_const] using
    orderNerveHomotopy (OrderHom.id : P →o P) (OrderHom.const P v) hv

def simplexTopFace (n : ℕ) : NonemptyFiniteChains (ULift.{0} (Fin (n+1))) where
  finset := Finset.univ
  nonempty := ⟨ULift.up 0, Finset.mem_univ _⟩
  comparable _ _ := le_total _ _

/-- The once-subdivided simplex also admits exact Kan lifting across its
canonical extension; its full face is the contracting greatest vertex. -/
theorem canonicalExtension_subdivision_standard_anodyne (n : ℕ) :
    SSet.anodyneExtensions (canonicalExtension.app (SSet.sd.obj (Δ[n] : SSet.{0}))) := by
  apply canonicalExtension_anodyne_of_iso (subdivisionFaceIso ⦋n⦌)
  exact canonicalExtension_anodyne_nerve_greatest (simplexTopFace n)
    (fun _ => Finset.subset_univ _)

/-- The second orientation of a two-step contraction, used for the
face-poset model of a subdivided horn. -/
theorem canonicalExtension_anodyne_of_homotopy_span (X : SSet.{0})
    (f : X ⟶ (Δ[0] : SSet.{0})) (g : (Δ[0] : SSet.{0}) ⟶ X) (u : X ⟶ X)
    (H : SSet.Homotopy (f ≫ g) u) (G : SSet.Homotopy (𝟙 X) u) :
    SSet.anodyneExtensions (canonicalExtension.app X) := by
  have := canonicalExtension_mono X
  have := canonicalExtension_isIso_of_terminal SSet.stdSimplex.isTerminalObj₀
  let HX : SSet.Homotopy (SSet.ex.map f ≫ SSet.ex.map g) (SSet.ex.map u) :=
    { h := (extensionHomotopy H).h
      h₀ := by
        change SSet.ι₀ ≫ (extensionHomotopy H).h = SSet.ex.map f ≫ SSet.ex.map g
        simpa only [Functor.map_comp] using (extensionHomotopy H).h₀
      h₁ := (extensionHomotopy H).h₁
      rel := (extensionHomotopy H).rel }
  let GX : SSet.Homotopy (𝟙 (SSet.ex.obj X)) (SSet.ex.map u) :=
    { h := (extensionHomotopy G).h
      h₀ := by
        change SSet.ι₀ ≫ (extensionHomotopy G).h = 𝟙 (SSet.ex.obj X)
        exact (extensionHomotopy G).h₀.trans (SSet.ex.map_id X)
      h₁ := (extensionHomotopy G).h₁
      rel := (extensionHomotopy G).rel }
  exact anodyne_of_arrow_homotopy_zigzag (canonicalExtension.app X)
    (canonicalExtension.app (Δ[0] : SSet.{0})) (SSet.anodyneExtensions.of_isIso _)
    f (SSet.ex.map f) g (SSet.ex.map g)
    (canonicalExtension.naturality f).symm (canonicalExtension.naturality g).symm
    u (SSet.ex.map u) H HX (extensionHomotopy_canonical H)
    G GX (extensionHomotopy_canonical G)

/-- On the horn face poset the maps `id ≤ addVertex ≥ constant` give the
needed two-step contraction. -/
theorem canonicalExtension_hornFaceNerve_anodyne (n : ℕ) (k : Fin (n+2)) :
    SSet.anodyneExtensions
      (canonicalExtension.app (nerve (SubdivisionHornFaces.HornFaces n k))) := by
  let P := SubdivisionHornFaces.HornFaces n k
  let v : P := SubdivisionHornFaces.vertex n k
  let z := NormalizedSimplexIdentities.orderSimplex (OrderHom.const (Fin 1) v)
  let f : nerve P ⟶ (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from _
  let g : (Δ[0] : SSet.{0}) ⟶ nerve P := SSet.const z
  let u := nerveMap (SubdivisionHornFaces.addVertexHorn n k).monotone.functor
  have hc : nerveMap (OrderHom.const P v).monotone.functor =
      SSet.const (X := nerve P) z := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext t
    rfl
  apply canonicalExtension_anodyne_of_homotopy_span (nerve P) f g u
  · simpa only [hc, g, SSet.comp_const] using orderNerveHomotopy
      (OrderHom.const P v) (SubdivisionHornFaces.addVertexHorn n k)
      (SubdivisionHornFaces.point_le_addVertexHorn n k)
  · simpa only [orderNerveMap_id] using orderNerveHomotopy
      (OrderHom.id : P →o P) (SubdivisionHornFaces.addVertexHorn n k)
      (SubdivisionHornFaces.identity_le_addVertexHorn n k)

/-- The actual subdivided horn inherits its anodyne canonical extension
through the constructed face-poset isomorphism. -/
theorem canonicalExtension_subdivision_horn_anodyne (n : ℕ) (k : Fin (n+2)) :
    SSet.anodyneExtensions
      (canonicalExtension.app (SSet.sd.obj (Λ[n+1, k] : SSet.{0}))) :=
  canonicalExtension_anodyne_of_iso (hornSubdivisionIso n k)
    (canonicalExtension_hornFaceNerve_anodyne n k)

/-- The original subdivided simplex and the extended subdivided face can
both remain fixed in the relative lifting problem. -/
theorem relativeCanonicalExtension_subdivision_standard_anodyne {m n : ℕ}
    (i : (Δ[m] : SSet.{0}) ⟶ (Δ[n] : SSet.{0})) [Mono i] :
    SSet.anodyneExtensions (relativeCanonicalExtension (SSet.sd.map i)) := by
  have := subdivision_map_mono i
  exact relativeCanonicalExtension_anodyne _
    (canonicalExtension_subdivision_standard_anodyne m)
    (canonicalExtension_subdivision_standard_anodyne n)

/-- Exact relative Kan lifting for a subdivided generating horn, with
both the original subdivided simplex and the whole extended horn fixed. -/
theorem relativeCanonicalExtension_subdivision_horn_anodyne (n : ℕ) (k : Fin (n+2)) :
    SSet.anodyneExtensions (relativeCanonicalExtension (SSet.sd.map
      (Λ[n+1, k].ι : (Λ[n+1, k] : SSet.{0}) ⟶ (Δ[n+1] : SSet.{0})))) := by
  have := subdivision_map_mono (Λ[n+1, k].ι :
    (Λ[n+1, k] : SSet.{0}) ⟶ (Δ[n+1] : SSet.{0}))
  exact relativeCanonicalExtension_anodyne _
    (canonicalExtension_subdivision_horn_anodyne n k)
    (canonicalExtension_subdivision_standard_anodyne (n+1))

end

end Thomason.Construction

end

section

/-! # Intersections of extended subcomplexes

The extension functor preserves pullbacks. Its subcomplex images therefore
preserve intersections, and the original-object intersection is identified
by the cartesian canonical-extension square.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

noncomputable section

theorem subcomplex_inf_isPullback {X : SSet.{0}} (A B : X.Subcomplex) :
    IsPullback (SSet.Subcomplex.homOfLE (show A ⊓ B ≤ A from inf_le_left))
      (SSet.Subcomplex.homOfLE (show A ⊓ B ≤ B from inf_le_right)) A.ι B.ι := by
  apply IsPullback.of_forall_isPullback_app
  intro n
  rw [Types.isPullback_iff]
  refine ⟨rfl, ?_, ?_⟩
  · intro x y h
    have he : (⟨x.val, x.property.1⟩ : A.obj n) = ⟨y.val, y.property.1⟩ := h.1
    exact Subtype.ext (congrArg (fun z : (A.toSSet).obj n => z.val) he)
  · intro x y h
    change x.val = y.val at h
    refine ⟨⟨x.val, x.property, h.symm ▸ y.property⟩, ?_, ?_⟩
    · exact Subtype.ext rfl
    · exact Subtype.ext h

theorem range_comp_eq_inf_of_isPullback {W X Y Z : SSet.{0}}
    {t : W ⟶ X} {l : W ⟶ Y} {r : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback t l r b) :
    SSet.Subcomplex.range (t ≫ r) = SSet.Subcomplex.range r ⊓ SSet.Subcomplex.range b := by
  apply Subfunctor.ext
  funext n
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨⟨t.app n w, rfl⟩, ⟨l.app n w, ?_⟩⟩
    exact (ConcreteCategory.congr_hom (h.app n).w w).symm
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    obtain ⟨w, hw, _⟩ := Types.exists_of_isPullback (h.app n) x y (hx.trans hy.symm)
    refine ⟨w, ?_⟩
    change r.app n (t.app n w) = z
    rw [hw, hx]

theorem anodyne_range_inclusion {A B X : SSet.{0}} (f : A ⟶ B) (g : B ⟶ X)
    [Mono f] [Mono g] (hf : SSet.anodyneExtensions f) :
    SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
      (Subfunctor.range_comp_le f g)) := by
  let e := asIso (SSet.Subcomplex.toRange (f ≫ g))
  let d := asIso (SSet.Subcomplex.toRange g)
  have he : f ≫ d.hom = e.hom ≫
      SSet.Subcomplex.homOfLE (Subfunctor.range_comp_le f g) := by
    apply (cancel_mono (SSet.Subcomplex.range g).ι).mp
    simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι]
    rfl
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff (Arrow.isoMk e d he.symm)).mp hf

def extensionImage {X : SSet.{0}} (A : X.Subcomplex) : (SSet.ex.obj X).Subcomplex :=
  SSet.Subcomplex.range (SSet.ex.map A.ι)

def originalImage (X : SSet.{0}) : (SSet.ex.obj X).Subcomplex :=
  SSet.Subcomplex.range (canonicalExtension.app X)

theorem extensionImage_inf {X : SSet.{0}} (A B : X.Subcomplex) :
    extensionImage (A ⊓ B) = extensionImage A ⊓ extensionImage B := by
  have h := range_comp_eq_inf_of_isPullback ((subcomplex_inf_isPullback A B).map SSet.ex)
  have he : SSet.ex.map (SSet.Subcomplex.homOfLE (show A ⊓ B ≤ A from inf_le_left)) ≫
      SSet.ex.map A.ι = SSet.ex.map (A ⊓ B).ι := by
    rw [← SSet.ex.map_comp]
    rfl
  exact (congrArg SSet.Subcomplex.range he).symm.trans h

theorem originalImage_inter_extensionImage {X : SSet.{0}} (A : X.Subcomplex) :
    SSet.Subcomplex.range (canonicalExtension.app A.toSSet ≫ SSet.ex.map A.ι) =
      originalImage X ⊓ extensionImage A := by
  have h := range_comp_eq_inf_of_isPullback (canonicalExtension_isPullback A.ι)
  rw [(canonicalExtension_isPullback A.ι).w] at h
  exact h

theorem originalImage_inter_extensionImage_anodyne {X : SSet.{0}} (A : X.Subcomplex)
    (hA : SSet.anodyneExtensions (canonicalExtension.app A.toSSet)) :
    SSet.anodyneExtensions (SSet.Subcomplex.homOfLE
      (show originalImage X ⊓ extensionImage A ≤ extensionImage A from inf_le_right)) := by
  have := canonicalExtension_mono A.toSSet
  have h := anodyne_range_inclusion (canonicalExtension.app A.toSSet) (SSet.ex.map A.ι) hA
  exact (anodyne_subcomplex_congr (originalImage_inter_extensionImage A) rfl _ _).mp h

end

end Thomason.Construction

end

end OAI
