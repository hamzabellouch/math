import OAI.AlgebraicTopology.IntegralHomology.Relative
import Mathlib.Analysis.Convex.Contractible

namespace OAI

noncomputable section

namespace Kaplansky

/-! Contractible-pair homology, equivalences, and relative map extensionality. -/

section
open CategoryTheory Limits ContinuousMap

/-- An actual homotopy equivalence induces an integral homology isomorphism. -/
def integralHomologyHomotopyIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (n : ℕ) :
    (integralSingularHomology n).obj (TopCat.of X) ≅
      (integralSingularHomology n).obj (TopCat.of Y) where
  hom := (integralSingularHomology n).map (TopCat.ofHom e.toFun)
  inv := (integralSingularHomology n).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← Functor.map_comp]
    obtain ⟨H⟩ := e.left_inv
    exact (integralSingularHomology_homotopy H n).trans (CategoryTheory.Functor.map_id _ _)
  inv_hom_id := by
    rw [← Functor.map_comp]
    obtain ⟨H⟩ := e.right_inv
    exact (integralSingularHomology_homotopy H n).trans (CategoryTheory.Functor.map_id _ _)

theorem integralSingularHomology_isZero_contractible (X : Type)
    [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero ((integralSingularHomology n).obj (TopCat.of X)) := by
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic X
  rw [IsZero.iff_id_eq_zero]
  have h := integralSingularHomology_homotopy
    (f := TopCat.ofHom (ContinuousMap.id X))
    (g := TopCat.ofHom (ContinuousMap.const X x)) H n
  change (integralSingularHomology n).map (𝟙 (TopCat.of X)) = _ at h
  rw [CategoryTheory.Functor.map_id, integralSingularHomology_const x hn] at h
  exact h

/-- In degrees at least two, relative homology in a contractible ambient
space is the preceding homology of the subspace, via the actual boundary. -/
def contractibleRelativeBoundaryIso {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    relativeSingularHomology i (n+1) ≅ (integralSingularHomology n).obj A :=
  (relativeChainSequence_shortExact i).δIso (n+1) n rfl
    (integralSingularHomology_isZero_contractible X (n+1) (Nat.succ_ne_zero n))
    (integralSingularHomology_isZero_contractible X n hn)

theorem contractibleRelativeBoundaryIso_hom {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    (contractibleRelativeBoundaryIso i n hn).hom = relativeHomologyBoundary i n := rfl

def puncturedVectorBoundaryIso (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (hn : n ≠ 0) :
    relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set V)) (n+1) ≅
      (integralSingularHomology n).obj (TopCat.of ({0}ᶜ : Set V)) :=
  contractibleRelativeBoundaryIso _ n hn

end

section
open CategoryTheory Limits
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A genuine homeomorphism of pairs acts invertibly on relative singular chains. -/
def relativeChainsHomeomorphIso (e : X ≃ₜ Y) (U : Set X) (V : Set Y)
    (h : ∀ x, x ∈ U ↔ e x ∈ V) :
    relativeSingularChains (subspaceInclusion U) ≅
      relativeSingularChains (subspaceInclusion V) :=
  cokernel.mapIso _ _
    (integralSingularChains.mapIso (TopCat.isoOfHomeo (e.subtype h)))
    (integralSingularChains.mapIso (TopCat.isoOfHomeo e)) (by
      change integralSingularChains.map _ ≫ integralSingularChains.map _ =
        integralSingularChains.map _ ≫ integralSingularChains.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      apply congrArg integralSingularChains.map
      rfl)

def relativeHomologyHomeomorphIso (e : X ≃ₜ Y) (U : Set X) (V : Set Y)
    (h : ∀ x, x ∈ U ↔ e x ∈ V) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion U) n ≅
      relativeSingularHomology (subspaceInclusion V) n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (relativeChainsHomeomorphIso e U V h)

/-- The isomorphism is the same map as that induced by the actual map of pairs. -/
theorem relativeHomologyHomeomorphIso_hom (e : X ≃ₜ Y) (U : Set X) (V : Set Y)
    (h : ∀ x, x ∈ U ↔ e x ∈ V) (n : ℕ) :
    (relativeHomologyHomeomorphIso e U V h n).hom =
      relativeHomologyMap (subspaceInclusion U) (subspaceInclusion V)
        (subspaceMap U V ⟨e, e.continuous⟩ (fun x hx => (h x).mp hx))
        (TopCat.ofHom ⟨e, e.continuous⟩) (subspaceMap_square _ _ _ _) n := rfl

def localHomologyHomeomorphIso (e : X ≃ₜ Y) (x : X) (n : ℕ) :
    relativeSingularHomology (subspaceInclusion ({x}ᶜ : Set X)) n ≅
      relativeSingularHomology (subspaceInclusion ({e x}ᶜ : Set Y)) n :=
  relativeHomologyHomeomorphIso e _ _ (fun y => by simp only [Set.mem_compl_iff,
    Set.mem_singleton_iff, e.injective.eq_iff]) n

end

section
open CategoryTheory

/-- Into an embedded subspace, the ambient map uniquely determines the
map of relative chains and hence of relative homology. -/
theorem relativeHomologyMap_congr_ambient {A X B Y : TopCat.{0}}
    (i : A ⟶ X) (j : B ⟶ Y) [Mono j]
    (a b : A ⟶ B) (f g : X ⟶ Y)
    (h : i ≫ f = a ≫ j) (h' : i ≫ g = b ≫ j) (he : f = g) (n : ℕ) :
    relativeHomologyMap i j a f h n = relativeHomologyMap i j b g h' n := by
  subst g
  have ha : a = b := (cancel_mono j).mp (h.symm.trans h')
  subst b
  rfl

end

open CategoryTheory Limits HomologicalComplex ContinuousMap
section

/-- Singular chains of an actual homotopy equivalence form a quasi-isomorphism. -/
theorem integralChains_homotopyEquiv_quasiIso {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) :
    QuasiIso (integralSingularChains.map (TopCat.ofHom e.toFun)) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso (integralHomologyHomotopyIso e n).hom
  infer_instance

/-- A map of genuine pairs whose ambient and subspace maps are homotopy
equivalences induces an isomorphism on relative homology in every degree. -/
theorem relativeHomologyMap_isIso_of_equivalences
    {A X B Y : Type} [TopologicalSpace A] [TopologicalSpace X]
    [TopologicalSpace B] [TopologicalSpace Y]
    (i : TopCat.of A ⟶ TopCat.of X) (j : TopCat.of B ⟶ TopCat.of Y)
    [Mono i] [Mono j] (a : A ≃ₕ B) (f : X ≃ₕ Y)
    (h : i ≫ TopCat.ofHom f.toFun = TopCat.ofHom a.toFun ≫ j) (n : ℕ) :
    IsIso (relativeHomologyMap i j (TopCat.ofHom a.toFun) (TopCat.ofHom f.toFun) h n) := by
  have hq : QuasiIso (relativeChainMap i j (TopCat.ofHom a.toFun)
      (TopCat.ofHom f.toFun) h) :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃
      (relativeChainSequenceMap i j _ _ h)
      (relativeChainSequence_shortExact i) (relativeChainSequence_shortExact j)
      (integralChains_homotopyEquiv_quasiIso a) (integralChains_homotopyEquiv_quasiIso f)
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp ((quasiIso_iff _).mp hq n)

end

end Kaplansky

end

end OAI
