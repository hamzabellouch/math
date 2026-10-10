import OAI.AlgebraicTopology.IntegralHomology.Sections
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Topology.Category.TopCat.EpiMono

namespace OAI

noncomputable section

namespace Kaplansky

/-! Integral relative singular chains, homology, and relative section maps. -/

section
open CategoryTheory Limits AlgebraicTopology

/-- The same integral singular chains underlying `integralSingularHomology`. -/
def integralSingularChains : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- Relative chains are the actual cokernel of the subspace chain map. -/
def relativeSingularChains {A X : TopCat.{0}} (i : A ⟶ X) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ := cokernel (integralSingularChains.map i)

def relativeChainProjection {A X : TopCat.{0}} (i : A ⟶ X) :
    integralSingularChains.obj X ⟶ relativeSingularChains i :=
  cokernel.π (integralSingularChains.map i)

instance {A X : TopCat.{0}} (i : A ⟶ X) : Epi (relativeChainProjection i) := by
  exact coequalizer.π_epi (f := integralSingularChains.map i) (g := 0)

def relativeChainMap {A X B Y : TopCat.{0}} (i : A ⟶ X) (j : B ⟶ Y)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j) :
    relativeSingularChains i ⟶ relativeSingularChains j :=
  cokernel.map _ _ (integralSingularChains.map a) (integralSingularChains.map f)
    (by rw [← Functor.map_comp, h, Functor.map_comp])

@[reassoc (attr := simp)]
theorem relativeChainProjection_map {A X B Y : TopCat.{0}} (i : A ⟶ X) (j : B ⟶ Y)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j) :
    relativeChainProjection i ≫ relativeChainMap i j a f h =
      integralSingularChains.map f ≫ relativeChainProjection j := by
  exact cokernel.π_desc _ _ _

theorem relativeChainMap_id {A X : TopCat.{0}} (i : A ⟶ X) :
    relativeChainMap i i (𝟙 A) (𝟙 X) (by simp) = 𝟙 _ := by
  apply (cancel_epi (relativeChainProjection i)).mp
  simp

theorem relativeChainMap_comp {A X B Y C Z : TopCat.{0}}
    (i : A ⟶ X) (j : B ⟶ Y) (k : C ⟶ Z)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j)
    (b : B ⟶ C) (g : Y ⟶ Z) (h' : j ≫ g = b ≫ k) :
    relativeChainMap i j a f h ≫ relativeChainMap j k b g h' =
      relativeChainMap i k (a ≫ b) (f ≫ g) (by rw [← Category.assoc, h,
        Category.assoc, h', Category.assoc]) := by
  apply (cancel_epi (relativeChainProjection i)).mp
  simp [Functor.map_comp, Category.assoc]

def relativeChainSequence {A X : TopCat.{0}} (i : A ⟶ X) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (integralSingularChains.map i) (relativeChainProjection i)
    (cokernel.condition _)

/-- Injectivity of the actual inclusion supplies short exactness; it is
not an assumed homological property of the pair. -/
theorem relativeChainSequence_shortExact {A X : TopCat.{0}} (i : A ⟶ X)
    [Mono i] : (relativeChainSequence i).ShortExact := by
  have : Mono (integralSingularChains.map i) := by
    unfold integralSingularChains
    infer_instance
  change (ShortComplex.mk (integralSingularChains.map i)
    (cokernel.π _) (cokernel.condition _)).ShortExact
  exact { exact := ShortComplex.exact_cokernel _ }

/-- Inclusion of an arbitrary subspace with its inherited topology. -/
def subspaceInclusion {X : Type} [TopologicalSpace X] (U : Set X) :
    TopCat.of U ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

instance {X : Type} [TopologicalSpace X] (U : Set X) : Mono (subspaceInclusion U) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

end

section
open CategoryTheory Limits

def relativeSingularHomology {A X : TopCat.{0}} (i : A ⟶ X) (n : ℕ) : ModuleCat.{0} ℤ :=
  (relativeSingularChains i).homology n

def absoluteToRelative {A X : TopCat.{0}} (i : A ⟶ X) (n : ℕ) :
    (integralSingularHomology n).obj X ⟶ relativeSingularHomology i n :=
  HomologicalComplex.homologyMap (relativeChainProjection i) n

def relativeHomologyMap {A X B Y : TopCat.{0}} (i : A ⟶ X) (j : B ⟶ Y)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j) (n : ℕ) :
    relativeSingularHomology i n ⟶ relativeSingularHomology j n :=
  HomologicalComplex.homologyMap (relativeChainMap i j a f h) n

@[reassoc]
theorem absoluteToRelative_naturality {A X B Y : TopCat.{0}} (i : A ⟶ X) (j : B ⟶ Y)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j) (n : ℕ) :
    absoluteToRelative i n ≫ relativeHomologyMap i j a f h n =
      (integralSingularHomology n).map f ≫ absoluteToRelative j n := by
  change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ =
    HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
  rw [← HomologicalComplex.homologyMap_comp, relativeChainProjection_map,
    HomologicalComplex.homologyMap_comp]
  rfl

theorem relativeHomologyMap_id {A X : TopCat.{0}} (i : A ⟶ X) (n : ℕ) :
    relativeHomologyMap i i (𝟙 _) (𝟙 _) (by simp) n = 𝟙 _ := by
  simp [relativeHomologyMap, relativeChainMap_id, relativeSingularHomology]

theorem relativeHomologyMap_comp {A X B Y C Z : TopCat.{0}}
    (i : A ⟶ X) (j : B ⟶ Y) (k : C ⟶ Z)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j)
    (b : B ⟶ C) (g : Y ⟶ Z) (h' : j ≫ g = b ≫ k) (n : ℕ) :
    relativeHomologyMap i j a f h n ≫ relativeHomologyMap j k b g h' n =
      relativeHomologyMap i k (a ≫ b) (f ≫ g) (by rw [← Category.assoc, h,
        Category.assoc, h', Category.assoc]) n := by
  exact (HomologicalComplex.homologyMap_comp (relativeChainMap i j a f h)
    (relativeChainMap j k b g h') n).symm.trans
      (congrArg (fun φ => HomologicalComplex.homologyMap φ n)
        (relativeChainMap_comp i j k a f h b g h'))

/-- The boundary homomorphism of an actual injective topological map. -/
def relativeHomologyBoundary {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] (n : ℕ) :
    relativeSingularHomology i (n+1) ⟶ (integralSingularHomology n).obj A :=
  (relativeChainSequence_shortExact i).δ (n+1) n rfl

theorem absoluteToRelative_boundary {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] (n : ℕ) :
    absoluteToRelative i (n+1) ≫ relativeHomologyBoundary i n = 0 :=
  (relativeChainSequence_shortExact i).comp_δ (n+1) n rfl

theorem relativeHomologyBoundary_inclusion {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    (n : ℕ) : relativeHomologyBoundary i n ≫ (integralSingularHomology n).map i = 0 :=
  (relativeChainSequence_shortExact i).δ_comp (n+1) n rfl

theorem inclusion_absoluteToRelative {A X : TopCat.{0}} (i : A ⟶ X) (n : ℕ) :
    (integralSingularHomology n).map i ≫ absoluteToRelative i n = 0 := by
  have hp : integralSingularChains.map i ≫ relativeChainProjection i = 0 :=
    cokernel.condition (integralSingularChains.map i)
  calc
    _ = HomologicalComplex.homologyMap
        (integralSingularChains.map i ≫ relativeChainProjection i) n :=
      (HomologicalComplex.homologyMap_comp (integralSingularChains.map i)
        (relativeChainProjection i) n).symm
    _ = 0 := by rw [hp]; exact HomologicalComplex.homologyMap_zero _ _ _

/-- All three positions in the relative singular homology long exact sequence. -/
theorem relativeHomology_exact_at_absolute {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    (n : ℕ) : (ShortComplex.mk _ _ (inclusion_absoluteToRelative i n)).Exact :=
  (relativeChainSequence_shortExact i).homology_exact₂ n

theorem relativeHomology_exact_at_relative {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    (n : ℕ) : (ShortComplex.mk _ _ (absoluteToRelative_boundary i n)).Exact :=
  (relativeChainSequence_shortExact i).homology_exact₃ (n+1) n rfl

theorem relativeHomology_exact_at_subspace {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    (n : ℕ) : (ShortComplex.mk _ _ (relativeHomologyBoundary_inclusion i n)).Exact :=
  (relativeChainSequence_shortExact i).homology_exact₁ (n+1) n rfl

def relativeChainSequenceMap {A X B Y : TopCat.{0}} (i : A ⟶ X) (j : B ⟶ Y)
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j) :
    relativeChainSequence i ⟶ relativeChainSequence j where
  τ₁ := integralSingularChains.map a
  τ₂ := integralSingularChains.map f
  τ₃ := relativeChainMap i j a f h
  comm₁₂ := by
    change integralSingularChains.map a ≫ integralSingularChains.map j =
      integralSingularChains.map i ≫ integralSingularChains.map f
    rw [← Functor.map_comp, ← h, Functor.map_comp]
  comm₂₃ := (relativeChainProjection_map i j a f h).symm

theorem relativeHomologyBoundary_naturality {A X B Y : TopCat.{0}}
    (i : A ⟶ X) (j : B ⟶ Y) [Mono i] [Mono j]
    (a : A ⟶ B) (f : X ⟶ Y) (h : i ≫ f = a ≫ j) (n : ℕ) :
    relativeHomologyBoundary i n ≫ (integralSingularHomology n).map a =
      relativeHomologyMap i j a f h (n+1) ≫ relativeHomologyBoundary j n :=
  HomologicalComplex.HomologySequence.δ_naturality (relativeChainSequenceMap i j a f h)
    (relativeChainSequence_shortExact i) (relativeChainSequence_shortExact j) (n+1) n rfl

end

open Bundle Topology CategoryTheory OnePoint
section

/-- Restriction of a continuous map that really carries one subspace into another. -/
def subspaceMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U : Set X) (V : Set Y) (f : C(X,Y)) (h : Set.MapsTo f U V) :
    TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x => ⟨f x, h x.2⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem subspaceMap_square {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U : Set X) (V : Set Y) (f : C(X,Y)) (h : Set.MapsTo f U V) :
    subspaceInclusion U ≫ TopCat.ofHom f = subspaceMap U V f h ≫ subspaceInclusion V := rfl

variable {B V : Type} {E : B → Type} [∀ b, NormedAddCommGroup (E b)]

/-- Complement of the actual zero section in the one-point total space.
It includes infinity; it is not just the punctured total space. -/
def compactifiedNonzeroBundle : Set (OnePoint (TotalSpace V E)) :=
  (Set.range (fun b => (TotalSpace.mk' V b (0 : E b) : OnePoint (TotalSpace V E))))ᶜ

theorem coe_mem_compactifiedNonzeroBundle (b : B) (v : E b) :
    (TotalSpace.mk' V b v : OnePoint (TotalSpace V E)) ∈ compactifiedNonzeroBundle ↔ v ≠ 0 := by
  change (¬ ∃ c, (TotalSpace.mk' V c (0 : E c) : OnePoint (TotalSpace V E)) =
    (TotalSpace.mk' V b v : OnePoint (TotalSpace V E))) ↔ v ≠ 0
  constructor
  · intro h hv
    exact h ⟨b, by rw [hv]⟩
  · intro hv ⟨c, hc⟩
    have hz := OnePoint.coe_injective hc
    have hb := congrArg (fun z : TotalSpace V E => z.proj) hz
    change c = b at hb
    subst c
    exact hv ((TotalSpace.mk_injective b) hz).symm

theorem infty_mem_compactifiedNonzeroBundle :
    (∞ : OnePoint (TotalSpace V E)) ∈ compactifiedNonzeroBundle := by
  rintro ⟨b, hb⟩
  exact OnePoint.coe_ne_infty _ hb

/-- Nonvanishing locus of this section, with the actual base topology. -/
def sectionNonzeroLocus (s : ∀ b, E b) : Set B := {b | s b ≠ 0}

variable [TopologicalSpace B] [TopologicalSpace (TotalSpace V E)]

theorem compactifiedSection_mapsTo_nonzero (s : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b))) :
    Set.MapsTo (compactifiedSection s hs) (sectionNonzeroLocus s)
      (compactifiedNonzeroBundle (V := V) (E := E)) := by
  intro b hb
  exact (coe_mem_compactifiedNonzeroBundle b (s b)).mpr hb

/-- The actual map of pairs (B, B minus zeros) to (Thom, Thom minus zero section). -/
def sectionRelativeHomologyMap (s : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b))) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion (sectionNonzeroLocus s)) n ⟶
      relativeSingularHomology
        (subspaceInclusion (compactifiedNonzeroBundle (V := V) (E := E))) n :=
  relativeHomologyMap _ _
    (subspaceMap _ _ (compactifiedSection s hs) (compactifiedSection_mapsTo_nonzero s hs))
    (TopCat.ofHom (compactifiedSection s hs)) (subspaceMap_square _ _ _ _) n

/-- Exact comparison with the preserved absolute section map. No local
degree, excision, or fundamental-class premise is used in this square. -/
theorem sectionRelativeHomology_comparison (s : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b))) (n : ℕ) :
    absoluteToRelative (subspaceInclusion (sectionNonzeroLocus s)) n ≫
        sectionRelativeHomologyMap s hs n =
      sectionHomologyMap s hs n ≫
        absoluteToRelative (subspaceInclusion (compactifiedNonzeroBundle (V := V) (E := E))) n :=
  absoluteToRelative_naturality _ _ _ _ _ n

/-- A class annihilated by the relative boundary lifts to absolute homology.
This is a consequence of the proved long exact sequence, not a lifting axiom. -/
theorem relativeClass_lifts_iff {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] (n : ℕ)
    (c : relativeSingularHomology i (n+1)) :
    relativeHomologyBoundary i n c = 0 ↔
      ∃ b : (integralSingularHomology (n+1)).obj X, absoluteToRelative i (n+1) b = c := by
  have h := (relativeHomology_exact_at_relative i n).moduleCat_range_eq_ker
  change c ∈ LinearMap.ker (relativeHomologyBoundary i n).hom ↔
    c ∈ LinearMap.range (absoluteToRelative i (n+1)).hom
  rw [h]

/-- A precise witness criterion for a nonzero global section map. This
does not construct the required local class or compute its image. -/
theorem sectionHomologyMap_ne_zero_of_relativeClass (s : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b))) (n : ℕ)
    (c : relativeSingularHomology (subspaceInclusion (sectionNonzeroLocus s)) (n+1))
    (hc : relativeHomologyBoundary (subspaceInclusion (sectionNonzeroLocus s)) n c = 0)
    (hne : sectionRelativeHomologyMap s hs (n+1) c ≠ 0) :
    sectionHomologyMap s hs (n+1) ≠ 0 := by
  obtain ⟨b, hb⟩ := (relativeClass_lifts_iff _ n c).mp hc
  intro hz
  have h := sectionRelativeHomology_comparison s hs (n+1)
  rw [hz, Limits.zero_comp] at h
  have he := congrArg (fun f => f b) h
  exact hne (by simpa [← hb] using he)

end

end Kaplansky

end

end OAI
