import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionCartesian
import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.FixedInternalPathMaps
import OAI.CategoryTheory.Thomason.Simplicial.HomotopyFiberPathEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.KanContractedFamilyLifting
import OAI.CategoryTheory.Thomason.Simplicial.KanFiberComponentTransport
import OAI.CategoryTheory.Thomason.Simplicial.KanSimplexContinuousFibers
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.SingularKanComplex
import OAI.CategoryTheory.Thomason.Simplicial.SkeletalWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homotopy.Contractible

namespace OAI

section

/-! # Actual homotopy-fibre compatibility of standard-simplex restrictions -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Restriction to a base simplex induces the literal continuous map of
homotopy fibres, by projecting the point and applying the simplex map to its path. -/
def realizedSimplexHomotopyFiberMap {E : SSet.{0}} (n m : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) (g : (Δ[m] : SSet.{0}) ⟶ Δ[n])
    (b : SSet.toTop.obj (Δ[m] : SSet.{0})) :
    continuousHomotopyFiber (SSet.toTop.map (pullback.snd p g)) b ⟶
      continuousHomotopyFiber (SSet.toTop.map p) ((SSet.toTop.map g).hom b) :=
  continuousHomotopyFiberMap _ _ (SSet.toTop.map (pullback.fst p g)) (SSet.toTop.map g)
    (by rw [← SSet.toTop.map_comp, pullback.condition, SSet.toTop.map_comp]) b

/-- Every standard-simplex restriction is compatible with the genuine
continuous homotopy fibre by an actual weak equivalence. No general
realization/pullback theorem or acyclic Kan lifting input is used. -/
theorem realizedSimplexHomotopyFiberMap_weak {E : SSet.{0}} (n m : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (g : (Δ[m] : SSet.{0}) ⟶ Δ[n]) (b : SSet.toTop.obj (Δ[m] : SSet.{0})) :
    topologicalWeakEquivalences (realizedSimplexHomotopyFiberMap n m p g b) := by
  apply continuousHomotopyFiberMap_weak
  · exact homotopyEquiv_isWeakHomotopyEquivalence (simplexHomotopyFiberEquiv m _ _)
  · exact homotopyEquiv_isWeakHomotopyEquivalence (simplexHomotopyFiberEquiv n _ _)
  · exact kan_simplex_baseChange_weak n m p g

end

end Thomason.Construction

end

section

/-! # Pointwise quasifibration compatibility on every simplex restriction -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Restriction along any map of standard simplices induces a weak
equivalence of the literal continuous fibres at every real point. This
includes all faces, degeneracies, and their composites. -/
theorem kan_simplex_continuousFiberBaseChange_weak {E : SSet.{0}} (n m : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (g : (Δ[m] : SSet.{0}) ⟶ Δ[n]) (b : SSet.toTop.obj (Δ[m] : SSet.{0})) :
    topologicalWeakEquivalences (continuousFiberBaseChangeMap
      (SSet.toTop.map (pullback.snd p g)) (SSet.toTop.map p)
      (SSet.toTop.map (pullback.fst p g)) (SSet.toTop.map g)
      (by rw [← SSet.toTop.map_comp, pullback.condition, SSet.toTop.map_comp]) b) := by
  have : HomotopicalAlgebra.Fibration (pullback.snd p g) := kan_pullback_snd_fibration p g
  exact continuousFiberBaseChangeMap_weak _ _ _ _ _ b
    (kan_simplex_baseChange_weak n m p g)
    (kan_simplex_continuousFiberInclusion_weak m (pullback.snd p g) b)
    (kan_simplex_continuousFiberInclusion_weak n p _)

end

end Thomason.Construction

end

section

/-! # The total space as the colimit of its simplex pullbacks -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- The standard-simplex density presentation, with the harmless universe
lift already included in `SSet.stdSimplex`. -/
abbrev simplexDensityCocone (E : SSet.{0}) :
    Cocone (CostructuredArrow.proj SSet.stdSimplex E ⋙ SSet.stdSimplex) :=
  Presheaf.tautologicalCocone' E

def simplexDensityIsColimit (E : SSet.{0}) : IsColimit (simplexDensityCocone E) :=
  Presheaf.isColimitTautologicalCocone' E

/-- A simplex in the total space lifts its own base simplex canonically. -/
def simplexPullbackSection {E B : SSet.{0}} (p : E ⟶ B) {n : SimplexCategory}
    (e : SSet.stdSimplex.obj n ⟶ E) :
    SSet.stdSimplex.obj n ⟶ pullback p (e ≫ p) :=
  pullback.lift e (𝟙 _) (by rw [Category.id_comp])

@[reassoc]
theorem simplexPullbackSection_fst {E B : SSet.{0}} (p : E ⟶ B) {n : SimplexCategory}
    (e : SSet.stdSimplex.obj n ⟶ E) :
    simplexPullbackSection p e ≫ pullback.fst p (e ≫ p) = e :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem simplexPullbackSection_snd {E B : SSet.{0}} (p : E ⟶ B) {n : SimplexCategory}
    (e : SSet.stdSimplex.obj n ⟶ E) :
    simplexPullbackSection p e ≫ pullback.snd p (e ≫ p) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- Restricting a total-space simplex commutes with its canonical lift to
its base-simplex pullback. -/
theorem simplexPullbackSection_naturality {E B : SSet.{0}} (p : E ⟶ B)
    {s t : CostructuredArrow SSet.stdSimplex E} (f : s ⟶ t) :
    SSet.stdSimplex.map f.left ≫ simplexPullbackSection p t.hom =
      simplexPullbackSection p s.hom ≫ (simplexPullbackDiagram p).map
        ((CostructuredArrow.map p).map f) := by
  apply pullback.hom_ext
  · rw [Category.assoc, simplexPullbackSection_fst]
    change _ = simplexPullbackSection p s.hom ≫
      simplexPullbackMap p (s.hom ≫ p) (t.hom ≫ p) f.left (by simp) ≫ pullback.fst p (t.hom ≫ p)
    rw [simplexPullbackMap_fst, simplexPullbackSection_fst]
    exact f.w
  · rw [Category.assoc, simplexPullbackSection_snd, Category.comp_id]
    change _ = simplexPullbackSection p s.hom ≫
      simplexPullbackMap p (s.hom ≫ p) (t.hom ≫ p) f.left (by simp) ≫ pullback.snd p (t.hom ≫ p)
    rw [simplexPullbackMap_snd, ← Category.assoc, simplexPullbackSection_snd, Category.id_comp]

/-- Every cocone on base-simplex pullbacks induces a compatible cocone on
the standard simplices of the original total space. -/
def simplexPullbackDescCocone {E B : SSet.{0}} (p : E ⟶ B)
    (s : Cocone (simplexPullbackDiagram p)) :
    Cocone (CostructuredArrow.proj SSet.stdSimplex E ⋙ SSet.stdSimplex) where
  pt := s.pt
  ι := {
    app j := simplexPullbackSection p j.hom ≫ s.ι.app ((CostructuredArrow.map p).obj j)
    naturality j k f := by
      dsimp only [CostructuredArrow.map]
      change SSet.stdSimplex.map f.left ≫ (simplexPullbackSection p k.hom ≫
        s.ι.app ((CostructuredArrow.map p).obj k)) =
        (simplexPullbackSection p j.hom ≫ s.ι.app ((CostructuredArrow.map p).obj j)) ≫ 𝟙 s.pt
      rw [← Category.assoc, simplexPullbackSection_naturality, Category.assoc,
        s.w]
      rfl }

/-- The induced map is defined through the actual density colimit. -/
def simplexPullbackDesc {E B : SSet.{0}} (p : E ⟶ B)
    (s : Cocone (simplexPullbackDiagram p)) : E ⟶ s.pt :=
  (simplexDensityIsColimit E).desc (simplexPullbackDescCocone p s)

@[reassoc]
theorem simplexPullbackDesc_simplex {E B : SSet.{0}} (p : E ⟶ B)
    (s : Cocone (simplexPullbackDiagram p)) (j : CostructuredArrow SSet.stdSimplex E) :
    j.hom ≫ simplexPullbackDesc p s =
      simplexPullbackSection p j.hom ≫ s.ι.app ((CostructuredArrow.map p).obj j) :=
  (simplexDensityIsColimit E).fac (simplexPullbackDescCocone p s) j

/-- The induced map agrees with the given cocone on every full simplex
pullback, not just on individual chosen lifts. -/
theorem simplexPullbackDesc_fac {E B : SSet.{0}} (p : E ⟶ B)
    (s : Cocone (simplexPullbackDiagram p))
    (b : CostructuredArrow SSet.stdSimplex B) :
    pullback.fst p b.hom ≫ simplexPullbackDesc p s = s.ι.app b := by
  apply (simplexDensityIsColimit (pullback p b.hom)).hom_ext
  intro j
  let e := j.hom ≫ pullback.fst p b.hom
  let k : CostructuredArrow SSet.stdSimplex E := CostructuredArrow.mk e
  let φ := SSet.stdSimplex.preimage (j.hom ≫ pullback.snd p b.hom)
  have hφ : SSet.stdSimplex.map φ = j.hom ≫ pullback.snd p b.hom :=
    CategoryTheory.Functor.map_preimage _ _
  have ha : SSet.stdSimplex.map φ ≫ b.hom = e ≫ p := by
    rw [hφ, Category.assoc, ← pullback.condition]
    rfl
  let a : ((CostructuredArrow.map p).obj k) ⟶ b :=
    CostructuredArrow.homMk φ ha
  have hl : simplexPullbackSection p e ≫ (simplexPullbackDiagram p).map a = j.hom := by
    apply pullback.hom_ext
    · change (simplexPullbackSection p e ≫ simplexPullbackMap p (e ≫ p) b.hom φ ha) ≫
        pullback.fst p b.hom = _
      rw [Category.assoc, simplexPullbackMap_fst, simplexPullbackSection_fst]
    · change (simplexPullbackSection p e ≫ simplexPullbackMap p (e ≫ p) b.hom φ ha) ≫
        pullback.snd p b.hom = _
      rw [Category.assoc, simplexPullbackMap_snd, ← Category.assoc,
        simplexPullbackSection_snd, Category.id_comp, hφ]
  change j.hom ≫ (pullback.fst p b.hom ≫ simplexPullbackDesc p s) = j.hom ≫ s.ι.app b
  rw [← Category.assoc]
  change k.hom ≫ simplexPullbackDesc p s = _
  rw [simplexPullbackDesc_simplex]
  calc
    simplexPullbackSection p k.hom ≫ s.ι.app ((CostructuredArrow.map p).obj k) =
        simplexPullbackSection p k.hom ≫ (simplexPullbackDiagram p).map a ≫ s.ι.app b := by
      have hw := s.w a
      simpa only [Category.comp_id] using (congrArg (fun q => simplexPullbackSection p k.hom ≫ q) hw).symm
    _ = j.hom ≫ s.ι.app b := by
      rw [← Category.assoc]
      exact congrArg (fun q => q ≫ s.ι.app b) hl

/-- The canonical pullback cocone really reconstructs the original total
simplicial set. No Kan or weak-equivalence assumption is needed here. -/
def simplexPullbackIsColimit {E B : SSet.{0}} (p : E ⟶ B) :
    IsColimit (simplexPullbackCocone p) where
  desc := simplexPullbackDesc p
  fac := simplexPullbackDesc_fac p
  uniq s m hm := by
    change E ⟶ s.pt at m
    apply (simplexDensityIsColimit E).hom_ext
    intro j
    change j.hom ≫ m = j.hom ≫ simplexPullbackDesc p s
    rw [simplexPullbackDesc_simplex]
    have hj := hm ((CostructuredArrow.map p).obj j)
    change pullback.fst p (j.hom ≫ p) ≫ m = s.ι.app ((CostructuredArrow.map p).obj j) at hj
    rw [← hj, ← Category.assoc, simplexPullbackSection_fst]

end

end Thomason.Construction

end

section

/-! # Positive vertex support along the actual realization prism -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial

noncomputable section

/-- The only vertices of a simplicial cylinder over a fixed vertex are
    its two endpoints. -/
theorem cylinder_vertex_cases {K : SSet.{0}}
    (z : (K ⊗ Δ[1]).obj (.op (.mk 0))) :
    z = SSet.ι₀.app _ z.1 ∨ z = SSet.ι₁.app _ z.1 := by
  let a : Fin 2 := SSet.stdSimplex.obj₀Equiv z.2
  have ha : a.val = 0 ∨ a.val = 1 := by omega
  have hi : SSet.stdSimplex.obj₀Equiv z.2 = (0 : Fin 2) ∨
      SSet.stdSimplex.obj₀Equiv z.2 = (1 : Fin 2) :=
    ha.imp Fin.ext Fin.ext
  rcases hi with hi | hi
  · left
    refine Prod.ext rfl ?_
    change z.2 = SSet.stdSimplex.obj₀Equiv.symm 0
    exact SSet.stdSimplex.obj₀Equiv.injective (hi.trans rfl)
  · right
    refine Prod.ext rfl ?_
    change z.2 = SSet.stdSimplex.obj₀Equiv.symm 1
    exact SSet.stdSimplex.obj₀Equiv.injective (hi.trans rfl)

/-- If the endpoints send a vertex to the same target vertex, the whole
    realized homotopy sends its open star into the target open star. -/
theorem homotopy_mem_vertexStar {K L : SSet.{0}} {f g : K ⟶ L}
    (H : SSet.Homotopy f g) (v : K.obj (.op (.mk 0)))
    (w : L.obj (.op (.mk 0)))
    (hf : f.app (.op (.mk 0)) v = w) (hg : g.app (.op (.mk 0)) v = w)
    (t : unitInterval) (x : SSet.toTop.obj K) (hx : x ∈ vertexStar K v) :
    RealizedCylinder.homotopy H (t, x) ∈ vertexStar L w := by
  rw [realizedHomotopy_apply]
  apply vertexStar_transfer (fst K Δ[1]) H.h v w
  · intro z hz
    change z.1 = v at hz
    rcases cylinder_vertex_cases z with h₀ | h₁
    · rw [h₀]
      exact (congrArg (fun u : K ⟶ L => u.app (.op (.mk 0)) z.1) H.h₀).trans
        (hz ▸ hf)
    · rw [h₁]
      exact (congrArg (fun u : K ⟶ L => u.app (.op (.mk 0)) z.1) H.h₁).trans
        (hz ▸ hg)
  · rwa [RealizedCylinder.comparison_first]

/-- Restriction of an actual realized simplicial map to an open vertex star. -/
def vertexStarMap {K L : SSet.{0}} (f : K ⟶ L)
    (v : K.obj (.op (.mk 0))) (w : L.obj (.op (.mk 0)))
    (h : f.app (.op (.mk 0)) v = w) : C(vertexStar K v, vertexStar L w) where
  toFun x := ⟨(SSet.toTop.map f).hom x.val,
    (map_mem_vertexStar_iff f x.val w).mpr ⟨v, h, x.property⟩⟩
  continuous_toFun := ((SSet.toTop.map f).hom.continuous.comp
    continuous_subtype_val).subtype_mk _

/-- Restrict a simplicial homotopy fixing a vertex to its actual open star.
    This does not assert that the star is contractible for a general simplicial set. -/
def vertexStarHomotopy {K : SSet.{0}} {f g : K ⟶ K}
    (H : SSet.Homotopy f g) (v : K.obj (.op (.mk 0)))
    (hf : f.app (.op (.mk 0)) v = v) (hg : g.app (.op (.mk 0)) v = v) :
    (vertexStarMap f v v hf).Homotopy (vertexStarMap g v v hg) where
  toFun p := ⟨RealizedCylinder.homotopy H (p.1, p.2.val),
    homotopy_mem_vertexStar H v v hf hg p.1 p.2.val p.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (RealizedCylinder.homotopy H).continuous.comp (by fun_prop)
  map_zero_left x := Subtype.ext ((RealizedCylinder.homotopy H).map_zero_left x.val)
  map_one_left x := Subtype.ext ((RealizedCylinder.homotopy H).map_one_left x.val)

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Ordered vertex homotopies with arbitrary simplicial source -/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory MonoidalCategory Opposite RealizationPrism NormalizedSimplexIdentities
open scoped Simplicial

noncomputable section

variable {K : SSet.{0}} {P : Type} [PartialOrder P]
variable (f g : K ⟶ nerve P)
variable (hfg : ∀ v : K.obj (.op (.mk 0)),
  (f.app (.op (.mk 0)) v).obj 0 ≤ (g.app (.op (.mk 0)) v).obj 0)

include hfg

theorem simplex_vertex_le {n : ℕ} (s : K.obj (.op (.mk n))) (i : Fin (n+1)) :
    (f.app _ s).obj i ≤ (g.app _ s).obj i := by
  have h := hfg (simplexVertex K s i)
  rw [← simplexVertex_naturality f, ← simplexVertex_naturality g] at h
  exact h

/-- A pointwise inequality on vertices gives a simplicial homotopy into
    a poset nerve, even when the source is not itself an ordinary nerve. -/
def orderedVertexHomotopy : SSet.Homotopy f g where
  h := {
    app n := ↾fun x => orderSimplex
      (orderInterpolate (simplexOrder (f.app n x.1)) (simplexOrder (g.app n x.1))
        (simplex_vertex_le f g hfg x.1) (OrderHom.id : Fin (n.unop.len+1) →o Fin (n.unop.len+1))
        (SSet.stdSimplex.objEquiv x.2).toOrderHom)
    naturality n m a := by
      apply ConcreteCategory.hom_ext
      intro x
      apply nerve.ext_of_isThin
      funext i
      have hf := ConcreteCategory.congr_hom (f.naturality a) x.1
      have hg := ConcreteCategory.congr_hom (g.naturality a) x.1
      change f.app m (K.map a x.1) = (nerve P).map a (f.app n x.1) at hf
      change g.app m (K.map a x.1) = (nerve P).map a (g.app n x.1) at hg
      change (if (SSet.stdSimplex.objEquiv ((Δ[1] : SSet).map a x.2)).toOrderHom i = 0 then
          (f.app m (K.map a x.1)).obj i else (g.app m (K.map a x.1)).obj i) = _
      rw [hf, hg]
      rfl }
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    rfl
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    rfl
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- This ordered-vertex criterion preserves the actual realization weak test. -/
theorem orderedVertex_weak_iff : realizationWeakEquivalences f ↔ realizationWeakEquivalences g :=
  RealizedCylinder.weakEquivalence_iff (orderedVertexHomotopy f g hfg)

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Stationarity of constructed ordered-vertex homotopies -/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

variable {A K : SSet.{0}} {P : Type} [PartialOrder P]
variable (f g : K ⟶ nerve P)
variable (hfg : ∀ v : K.obj (.op (.mk 0)),
  (f.app (.op (.mk 0)) v).obj 0 ≤ (g.app (.op (.mk 0)) v).obj 0)

/-- The constructed homotopy is stationary along any map on which its
    endpoints agree, with equality of actual cylinder maps. -/
theorem orderedVertexHomotopy_stationary (i : A ⟶ K) (hi : i ≫ f = i ≫ g) :
    i ▷ Δ[1] ≫ (orderedVertexHomotopy f g hfg).h =
      fst A Δ[1] ≫ i ≫ f := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext k
  have he := congrArg (fun u : A ⟶ nerve P => u.app n s.1) hi
  change f.app n (i.app n s.1) = g.app n (i.app n s.1) at he
  change (if (SSet.stdSimplex.objEquiv s.2).toOrderHom k = 0 then
    (f.app n (i.app n s.1)).obj k else (g.app n (i.app n s.1)).obj k) =
      (f.app n (i.app n s.1)).obj k
  rw [← he]
  split_ifs <;> rfl

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Contractible open vertex stars of actual poset realizations -/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory Opposite RealizationPrism NormalizedSimplexIdentities
open scoped Simplicial

noncomputable section

variable {P : Type} [PartialOrder P]

theorem nerve_const (v : P) :
    nerveMap (OrderHom.const P v).monotone.functor = SSet.const (vertex v) := by
  ext n s
  rfl

/-- A monotone clamp gives a contraction on the open star: both order
    homotopies stay inside the star because they fix its chosen vertex. -/
theorem vertexStar_contractible_of_clamp (v : P) (a : P →o P)
    (ha : ∀ x, x ≤ a x) (hv : ∀ x, v ≤ a x) (hav : a v = v) :
    ContractibleSpace (vertexStar (nerve P) (vertex v)) := by
  let p : vertexStar (nerve P) (vertex v) :=
    ⟨vertexPoint (nerve P) (vertex v), vertexPoint_mem_vertexStar _ _⟩
  have hfix : (nerveMap a.monotone.functor).app (.op (.mk 0)) (vertex v) = vertex v := by
    apply (eq_vertex_iff _ _).mpr
    exact hav
  have hconst : (nerveMap (OrderHom.const P v).monotone.functor).app
      (.op (.mk 0)) (vertex v) = vertex v := by
    apply (eq_vertex_iff _ _).mpr
    rfl
  let H₀ := vertexStarHomotopy (orderNerveHomotopy OrderHom.id a ha) (vertex v) rfl hfix
  let H₁ := vertexStarHomotopy
    (orderNerveHomotopy (OrderHom.const P v) a hv) (vertex v) hconst hfix
  have hleft : vertexStarMap (nerveMap (OrderHom.id : P →o P).monotone.functor)
      (vertex v) (vertex v) rfl = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    change (SSet.toTop.map (nerveMap (OrderHom.id : P →o P).monotone.functor)).hom x.val = x.val
    rw [orderNerveMap_id, SSet.toTop.map_id]
    rfl
  have hright : vertexStarMap (nerveMap (OrderHom.const P v).monotone.functor)
      (vertex v) (vertex v) hconst = ContinuousMap.const _ p := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    change (SSet.toTop.map (nerveMap (OrderHom.const P v).monotone.functor)).hom x.val = _
    rw [nerve_const]
    exact realization_const (vertex v) x.val
  apply (contractible_iff_id_nullhomotopic _).mpr
  exact ⟨p, ⟨(H₀.trans H₁.symm).cast hleft hright⟩⟩

/-- Open vertex stars of arbitrary small poset nerves are contractible.
    The statement concerns the actual realization subspace topology. -/
theorem vertexStar_contractible (v : P) :
    ContractibleSpace (vertexStar (nerve P) (vertex v)) := by
  let : ContractibleSpace
      (vertexStar (nerve (comparable v)) (vertex (comparableVertex v))) :=
    vertexStar_contractible_of_clamp (comparableVertex v) (upperClamp v)
      (le_upperClamp v) (comparableVertex_le_upperClamp v) (upperClamp_vertex v)
  exact (comparableStarHomeomorph v).symm.contractibleSpace

end

end Thomason.Construction.PosetGeometry

end

section

/-! # A proved local singular/realization weak-equivalence bridge for posets -/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory RealizationPrism
open scoped Simplicial

noncomputable section

variable {P : Type} [PartialOrder P]

/-- Evaluation on an actual open vertex star of a poset realization is a
    weak equivalence on components and every positive homotopy group. -/
theorem vertexStar_singular_counit_weak (v : P) :
    topologicalWeakEquivalences
      (sSetTopAdj.counit.app (TopCat.of (vertexStar (nerve P) (vertex v)))) := by
  let : ContractibleSpace (vertexStar (nerve P) (vertex v)) := vertexStar_contractible v
  exact singular_counit_weak_contractible _

/-- Cubes in poset realizations have a uniform finite grid subordinate to
    actual contractible stars, on which the singular comparison is proved.
    This is local control, not an assumed global approximation theorem. -/
theorem cube_grid_singular_comparison (n : ℕ)
    (f : C((Fin n → unitInterval), SSet.toTop.obj (nerve P))) :
    ∃ m : ℕ, ∀ k : Fin n → Fin (m+1), ∃ v : P,
      (∀ x ∈ CubeGrid.cell n m k, f x ∈ vertexStar (nerve P) (vertex v)) ∧
      ContractibleSpace (vertexStar (nerve P) (vertex v)) ∧
      topologicalWeakEquivalences
        (sSetTopAdj.counit.app (TopCat.of (vertexStar (nerve P) (vertex v)))) := by
  obtain ⟨m, hm⟩ := cube_grid_vertexStar_refinement (nerve P) n f
  refine ⟨m, fun k => ?_⟩
  obtain ⟨u, hu⟩ := hm k
  have he : u = vertex (u.obj 0) := (eq_vertex_iff _ _).mpr rfl
  refine ⟨u.obj 0, ?_, vertexStar_contractible _, vertexStar_singular_counit_weak _⟩
  simpa only [← he] using hu

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Simplicial isomorphisms preserve actual open vertex stars -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

theorem iso_mem_vertexStar_iff {K L : SSet.{0}} (e : K ≅ L)
    (v : K.obj (.op (.mk 0))) (x : SSet.toTop.obj K) :
    (SSet.toTop.map e.hom).hom x ∈ vertexStar L (e.hom.app _ v) ↔
      x ∈ vertexStar K v := by
  rw [map_mem_vertexStar_iff]
  constructor
  · rintro ⟨u, hu, hx⟩
    have huv : u = v := by
      have h := congrArg (fun z => e.inv.app (.op (.mk 0)) z) hu
      simpa only [← ConcreteCategory.comp_apply, ← SSet.comp_app, e.hom_inv_id,
        SSet.id_app, ConcreteCategory.id_apply] using h
    rwa [huv] at hx
  · intro hx
    exact ⟨v, rfl, hx⟩

/-- The star correspondence uses the actual geometric-realization homeomorphism. -/
def isoVertexStarHomeomorph {K L : SSet.{0}} (e : K ≅ L)
    (v : K.obj (.op (.mk 0))) :
    vertexStar K v ≃ₜ vertexStar L (e.hom.app _ v) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso e)).subtype
    (fun x => (iso_mem_vertexStar_iff e v x).symm)

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Extension preserves actual simplicial homotopies

The right adjoint `Ex` preserves finite products. The canonical map from
the simplicial interval into its extension therefore gives an explicit
cylinder comparison. This proves homotopy invariance independently of the
general weak-equivalence theorem for the canonical map.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe u

noncomputable section

local instance : SSet.ex.{u}.Monoidal := Functor.Monoidal.ofChosenFiniteProducts _

/-- Naturality on constant maps also holds with an extended source, since
extension preserves the terminal simplex. -/
theorem extension_map_const (X Y : SSet.{u}) (y : Y _⦋0⦌) :
    SSet.ex.map (SSet.const (X := X) y) =
      SSet.const (X := SSet.ex.obj X) y ≫ canonicalExtension.app Y := by
  let T := SSet.stdSimplex.isTerminalObj₀.{u}
  have ht : T.from (SSet.ex.obj X) ≫ canonicalExtension.app (Δ[0]) =
      SSet.ex.map (T.from X) :=
    (T.isTerminalObj SSet.ex).hom_ext _ _
  calc
    _ = SSet.ex.map (T.from X ≫ SSet.const (X := Δ[0]) y) := by
      rw [SSet.comp_const]
    _ = (T.from (SSet.ex.obj X) ≫ canonicalExtension.app (Δ[0])) ≫
        SSet.ex.map (SSet.const (X := Δ[0]) y) := by rw [Functor.map_comp, ht]
    _ = T.from (SSet.ex.obj X) ≫ (SSet.const (X := Δ[0]) y ≫
        canonicalExtension.app Y) := by
      have h := canonicalExtension.naturality (SSet.const (X := Δ[0]) y)
      exact congrArg (fun k => T.from (SSet.ex.obj X) ≫ k) h.symm
    _ = _ := by rw [← Category.assoc, SSet.comp_const]

/-- The natural comparison from the cylinder on `Ex X` into `Ex` of the
cylinder on `X`. -/
def extensionCylinder (X : SSet.{u}) :
    SSet.ex.obj X ⊗ Δ[1] ⟶ SSet.ex.obj (X ⊗ Δ[1]) :=
  (𝟙 (SSet.ex.obj X) ⊗ₘ canonicalExtension.app (Δ[1])) ≫
    Functor.LaxMonoidal.μ SSet.ex X (Δ[1])

theorem extensionCylinder_zero (X : SSet.{u}) :
    SSet.ι₀ ≫ extensionCylinder X = SSet.ex.map (SSet.ι₀ (X := X)) := by
  apply (cancel_mono (Functor.OplaxMonoidal.δ SSet.ex X (Δ[1]))).mp
  apply CartesianMonoidalCategory.hom_ext
  · simp [extensionCylinder, ← Functor.map_comp]
  · simp [extensionCylinder, ← Functor.map_comp, extension_map_const]

theorem extensionCylinder_one (X : SSet.{u}) :
    SSet.ι₁ ≫ extensionCylinder X = SSet.ex.map (SSet.ι₁ (X := X)) := by
  apply (cancel_mono (Functor.OplaxMonoidal.δ SSet.ex X (Δ[1]))).mp
  apply CartesianMonoidalCategory.hom_ext
  · simp [extensionCylinder, ← Functor.map_comp]
  · simp [extensionCylinder, ← Functor.map_comp, extension_map_const]

/-- Applying actual extension to both endpoints of a simplicial homotopy
produces a simplicial homotopy. -/
def extensionHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy (SSet.ex.map f) (SSet.ex.map g) where
  h := extensionCylinder X ≫ SSet.ex.map H.h
  h₀ := by
    change SSet.ι₀ ≫ (extensionCylinder X ≫ SSet.ex.map H.h) = SSet.ex.map f
    rw [← Category.assoc, extensionCylinder_zero, ← Functor.map_comp, H.h₀]
  h₁ := by
    change SSet.ι₁ ≫ (extensionCylinder X ≫ SSet.ex.map H.h) = SSet.ex.map g
    rw [← Category.assoc, extensionCylinder_one, ← Functor.map_comp, H.h₁]
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- Extension preserves simplicial homotopy equivalences with explicit
chosen inverses; this needs no Kan--Quillen model structure. -/
theorem extension_homotopy_inverse_weak {X Y : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : SSet.Homotopy (𝟙 X) (f ≫ g)) (hY : SSet.Homotopy (𝟙 Y) (g ≫ f)) :
    realizationWeakEquivalences (SSet.ex.map f) := by
  apply (simplicial_homotopy_inverse_weak_pair _ (SSet.ex.map g) ?_ ?_).1
  · simpa only [Functor.map_comp, CategoryTheory.Functor.map_id] using extensionHomotopy hX
  · simpa only [Functor.map_comp, CategoryTheory.Functor.map_id] using extensionHomotopy hY

/-- The canonical extension of a terminal simplicial set is an isomorphism. -/
theorem canonicalExtension_isIso_of_terminal {X : SSet.{u}} (hX : IsTerminal X) :
    IsIso (canonicalExtension.app X) := by
  exact ⟨⟨hX.from _, hX.hom_ext _ _,
    (hX.isTerminalObj SSet.ex).hom_ext _ _⟩⟩

/-- The canonical extension map is weak on every simplicial set with a
specified simplicial homotopy equivalence to the point. -/
theorem canonicalExtension_weak_of_contractible (X : SSet.{0})
    (f : X ⟶ Δ[0]) (g : Δ[0] ⟶ X)
    (hX : SSet.Homotopy (𝟙 X) (f ≫ g))
    (hT : SSet.Homotopy (𝟙 (Δ[0] : SSet.{0})) (g ≫ f)) :
    realizationWeakEquivalences (canonicalExtension.app X) := by
  have hf := (simplicial_homotopy_inverse_weak_pair f g hX hT).1
  have hef := extension_homotopy_inverse_weak f g hX hT
  have := canonicalExtension_isIso_of_terminal SSet.stdSimplex.isTerminalObj₀
  apply realizationWeakEquivalences.of_postcomp _ (SSet.ex.map f) hef
  rw [← canonicalExtension.naturality f]
  exact realizationWeakEquivalences.comp_mem _ _ hf
    (realizationWeakEquivalences.of_isIso _)

end

end Thomason.Construction

end

section

/-! # Canonical extension has Kan lifting on contracted finite parameters

The pair contraction proves an actual anodyne property, not merely a
realization weak equivalence. The general canonical inclusion remains a
separate filtration problem.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

local instance : SSet.ex.{0}.Monoidal := Functor.Monoidal.ofChosenFiniteProducts _

/-- The extension cylinder restricts to the original cylinder along the
canonical map, with equality of maps rather than a further homotopy. -/
theorem extensionCylinder_canonical (X : SSet.{0}) :
    (canonicalExtension.app X) ▷ (Δ[1] : SSet.{0}) ≫ extensionCylinder X =
      canonicalExtension.app (X ⊗ (Δ[1] : SSet.{0})) := by
  apply (cancel_mono (Functor.OplaxMonoidal.δ SSet.ex X (Δ[1]))).mp
  apply CartesianMonoidalCategory.hom_ext
  · simp [extensionCylinder, ← canonicalExtension.naturality]
  · simp [extensionCylinder, ← canonicalExtension.naturality]

/-- A homotopy and its extension form an exact homotopy of arrows. -/
theorem extensionHomotopy_canonical {X Y : SSet.{0}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) :
    (canonicalExtension.app X) ▷ (Δ[1] : SSet.{0}) ≫ (extensionHomotopy H).h =
      H.h ≫ canonicalExtension.app Y := by
  change (canonicalExtension.app X) ▷ (Δ[1] : SSet.{0}) ≫
    (extensionCylinder X ≫ SSet.ex.map H.h) = _
  rw [← Category.assoc, extensionCylinder_canonical]
  exact (canonicalExtension.naturality H.h).symm

/-- A specified simplicial contraction makes the actual canonical
extension inclusion anodyne. This supplies exact relative Kan lifts over
that parameter, with no weak-equivalence recognition theorem. -/
theorem canonicalExtension_anodyne_of_contraction (X : SSet.{0})
    (f : X ⟶ (Δ[0] : SSet.{0})) (g : (Δ[0] : SSet.{0}) ⟶ X)
    (H : SSet.Homotopy (𝟙 X) (f ≫ g)) :
    SSet.anodyneExtensions (canonicalExtension.app X) := by
  have := canonicalExtension_mono X
  have := canonicalExtension_isIso_of_terminal SSet.stdSimplex.isTerminalObj₀
  let HX : SSet.Homotopy (𝟙 (SSet.ex.obj X)) (SSet.ex.map f ≫ SSet.ex.map g) :=
    { h := (extensionHomotopy H).h
      h₀ := by
        change SSet.ι₀ ≫ (extensionHomotopy H).h = 𝟙 (SSet.ex.obj X)
        exact (extensionHomotopy H).h₀.trans (SSet.ex.map_id X)
      h₁ := by
        change SSet.ι₁ ≫ (extensionHomotopy H).h = SSet.ex.map f ≫ SSet.ex.map g
        simpa only [Functor.map_comp] using (extensionHomotopy H).h₁
      rel := (extensionHomotopy H).rel }
  exact anodyne_of_arrow_homotopies_reverse (canonicalExtension.app X)
    (canonicalExtension.app (Δ[0] : SSet.{0})) (SSet.anodyneExtensions.of_isIso _)
    f (SSet.ex.map f) g (SSet.ex.map g)
    (canonicalExtension.naturality f).symm (canonicalExtension.naturality g).symm
    H HX (extensionHomotopy_canonical H)

/-- In particular every standard simplex has the exact Kan lifting
property against its canonical inclusion into its extension. -/
theorem canonicalExtension_standard_anodyne (n : ℕ) :
    SSet.anodyneExtensions (canonicalExtension.app (Δ[n] : SSet.{0})) := by
  let f := SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{0})
  let g : (Δ[0] : SSet.{0}) ⟶ (Δ[n] : SSet.{0}) := SSet.const (finalSimplexVertex n)
  apply canonicalExtension_anodyne_of_contraction _ f g
  simpa only [g, SSet.comp_const] using simplexFinalContraction n

end

end Thomason.Construction

end

section

/-! # Canonical extension on the actual contractible test simplices

The homotopy-preservation construction proves the canonical extension map
weak on every poset nerve with a greatest element, hence on every standard
simplex. The comparison on these simplicial sets needs no general
canonical-extension hypothesis.
-/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- A greatest element contracts the actual nerve, and this contraction
persists through the actual extension functor. -/
theorem canonicalExtension_weak_nerve_greatest {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ x, x ≤ v) :
    realizationWeakEquivalences (canonicalExtension.app (nerve P)) := by
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
  have hX : SSet.Homotopy (𝟙 (nerve P)) (f ≫ g) := by
    have H := orderNerveHomotopy (OrderHom.id : P →o P) (OrderHom.const P v) hv
    simpa only [orderNerveMap_id, hc, g, SSet.comp_const] using H
  have hT : SSet.Homotopy (𝟙 (Δ[0] : SSet.{0})) (g ≫ f) := by
    have ht : g ≫ f = 𝟙 _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [ht]
    exact SSet.RelativeMorphism.Homotopy.refl _
  exact canonicalExtension_weak_of_contractible (nerve P) f g hX hT

/-- Every standard simplex satisfies the actual canonical-extension weak
equivalence theorem. -/
theorem canonicalExtension_weak_standard_simplex (n : ℕ) :
    realizationWeakEquivalences (canonicalExtension.app (Δ[n] : SSet.{0})) := by
  let e := SSet.stdSimplex.isoNerve.{0} n
  have hv : ∀ x : ULift.{0} (Fin (n + 1)), x ≤ ULift.up (Fin.last n) := by
    intro x
    exact Fin.le_last x.down
  have h := canonicalExtension_weak_nerve_greatest (ULift.up (Fin.last n)) hv
  apply realizationWeakEquivalences.of_postcomp _ (SSet.ex.map e.hom)
    (realizationWeakEquivalences.of_isIso _)
  rw [← canonicalExtension.naturality e.hom]
  exact realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso _) h

end

end Thomason.Construction

end

section

/-! # Relative canonical extensions of finite simplices

Cartesianness makes the union of the original target with the extension
of its prescribed subobject a subcomplex of the extended target.
Anodyne cancellation then gives exact relative Kan lifting for simplices.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

def relativeCanonicalExtension {A B : SSet.{0}} (i : A ⟶ B) :
    pushout i (canonicalExtension.app A) ⟶ SSet.ex.obj B :=
  pushout.desc (canonicalExtension.app B) (SSet.ex.map i)
    (canonicalExtension.naturality i)

@[reassoc]
theorem relativeCanonicalExtension_inl {A B : SSet.{0}} (i : A ⟶ B) :
    pushout.inl i (canonicalExtension.app A) ≫ relativeCanonicalExtension i =
      canonicalExtension.app B := pushout.inl_desc _ _ _

@[reassoc]
theorem relativeCanonicalExtension_inr {A B : SSet.{0}} (i : A ⟶ B) :
    pushout.inr i (canonicalExtension.app A) ≫ relativeCanonicalExtension i =
      SSet.ex.map i := pushout.inr_desc _ _ _

instance relativeCanonicalExtension_mono {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
    Mono (relativeCanonicalExtension i) := by
  have := canonicalExtension_mono B
  let sq := IsPushout.of_hasPushout i (canonicalExtension.app A)
  have he : relativeCanonicalExtension i = sq.desc (canonicalExtension.app B)
      (SSet.ex.map i) (canonicalExtension_isPullback i).w := by
    apply pushout.hom_ext
    · exact (relativeCanonicalExtension_inl i).trans (sq.inl_desc _ _ _).symm
    · exact (relativeCanonicalExtension_inr i).trans (sq.inr_desc _ _ _).symm
  rw [he]
  exact sq.desc_mono_of_isPullback (canonicalExtension_isPullback i)

/-- Absolute anodyne canonical extensions on a pair imply the relative
anodyne extension, using the actual union map. -/
theorem relativeCanonicalExtension_anodyne {A B : SSet.{0}} (i : A ⟶ B) [Mono i]
    (hA : SSet.anodyneExtensions (canonicalExtension.app A))
    (hB : SSet.anodyneExtensions (canonicalExtension.app B)) :
    SSet.anodyneExtensions (relativeCanonicalExtension i) := by
  apply anodyne_right_cancellation (pushout.inl i (canonicalExtension.app A))
    (relativeCanonicalExtension i)
  · exact SSet.anodyneExtensions.of_isPushout
      (IsPushout.of_hasPushout i (canonicalExtension.app A)) hA
  · rwa [relativeCanonicalExtension_inl]

/-- In particular any monomorphic map of standard simplices has exact
relative lifting after canonical extension. Both the original target and
the entire extended face are prescribed. -/
theorem relativeCanonicalExtension_standard_anodyne {m n : ℕ}
    (i : (Δ[m] : SSet.{0}) ⟶ (Δ[n] : SSet.{0})) [Mono i] :
    SSet.anodyneExtensions (relativeCanonicalExtension i) :=
  relativeCanonicalExtension_anodyne i (canonicalExtension_standard_anodyne m)
    (canonicalExtension_standard_anodyne n)

end

end Thomason.Construction

end

section

/-! # Exact relative canonical-extension lifting over a horn

The explicit two-step horn contraction supplies the finite local anodyne
comparison. No general canonical-extension filtration is assumed.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

noncomputable section

/-- Two compatible homotopies from a common map to the identity and a
constant also suffice for an anodyne canonical extension. -/
theorem canonicalExtension_anodyne_of_homotopy_cospan (X : SSet.{0})
    (f : X ⟶ (Δ[0] : SSet.{0})) (g : (Δ[0] : SSet.{0}) ⟶ X) (u : X ⟶ X)
    (H : SSet.Homotopy u (f ≫ g)) (G : SSet.Homotopy u (𝟙 X)) :
    SSet.anodyneExtensions (canonicalExtension.app X) := by
  have := canonicalExtension_mono X
  have := canonicalExtension_isIso_of_terminal SSet.stdSimplex.isTerminalObj₀
  let HX : SSet.Homotopy (SSet.ex.map u) (SSet.ex.map f ≫ SSet.ex.map g) :=
    { h := (extensionHomotopy H).h
      h₀ := (extensionHomotopy H).h₀
      h₁ := by
        change SSet.ι₁ ≫ (extensionHomotopy H).h = SSet.ex.map f ≫ SSet.ex.map g
        simpa only [Functor.map_comp] using (extensionHomotopy H).h₁
      rel := (extensionHomotopy H).rel }
  let GX : SSet.Homotopy (SSet.ex.map u) (𝟙 (SSet.ex.obj X)) :=
    { h := (extensionHomotopy G).h
      h₀ := (extensionHomotopy G).h₀
      h₁ := by
        change SSet.ι₁ ≫ (extensionHomotopy G).h = 𝟙 (SSet.ex.obj X)
        exact (extensionHomotopy G).h₁.trans (SSet.ex.map_id X)
      rel := (extensionHomotopy G).rel }
  exact anodyne_of_arrow_homotopy_cospan (canonicalExtension.app X)
    (canonicalExtension.app (Δ[0] : SSet.{0})) (SSet.anodyneExtensions.of_isIso _)
    f (SSet.ex.map f) g (SSet.ex.map g)
    (canonicalExtension.naturality f).symm (canonicalExtension.naturality g).symm
    u (SSet.ex.map u) H HX (extensionHomotopy_canonical H)
    G GX (extensionHomotopy_canonical G)

/-- Every positive-dimensional horn has an anodyne canonical extension,
by its explicit simplicial contraction through `lowerMap`. -/
theorem canonicalExtension_horn_anodyne (n : ℕ) (k : Fin (n+2)) :
    SSet.anodyneExtensions (canonicalExtension.app (Λ[n+1, k] : SSet.{0})) := by
  let X := (Λ[n+1, k] : SSet.{0})
  let f := SSet.stdSimplex.isTerminalObj₀.from X
  let g : (Δ[0] : SSet.{0}) ⟶ X := SSet.const (HornContraction.vertex k)
  apply canonicalExtension_anodyne_of_homotopy_cospan X f g (HornContraction.lowerMap k)
  · simpa only [g, SSet.comp_const, Bool.true_eq_false, ↓reduceIte] using
      HornContraction.homotopy k true
  · simpa only [Bool.false_eq_true, ↓reduceIte] using HornContraction.homotopy k false

/-- The whole extended horn and the original simplex can both be fixed
when lifting through a Kan fibration into the extended simplex. -/
theorem relativeCanonicalExtension_horn_anodyne (n : ℕ) (k : Fin (n+2)) :
    SSet.anodyneExtensions (relativeCanonicalExtension (Λ[n+1, k].ι :
      (Λ[n+1, k] : SSet.{0}) ⟶ (Δ[n+1] : SSet.{0}))) :=
  relativeCanonicalExtension_anodyne _ (canonicalExtension_horn_anodyne n k)
    (canonicalExtension_standard_anodyne (n+1))

/-- Applying `Ex` to a generating horn inclusion is anodyne, by the
original horn attachment followed by the exact relative comparison. -/
theorem extension_horn_anodyne (n : ℕ) (k : Fin (n+2)) :
    SSet.anodyneExtensions (SSet.ex.map (Λ[n+1, k].ι :
      (Λ[n+1, k] : SSet.{0}) ⟶ (Δ[n+1] : SSet.{0}))) := by
  rw [← relativeCanonicalExtension_inr]
  apply SSet.anodyneExtensions.comp_mem
  · exact SSet.anodyneExtensions.of_isPushout
      (IsPushout.of_hasPushout (Λ[n+1, k].ι :
        (Λ[n+1, k] : SSet.{0}) ⟶ (Δ[n+1] : SSet.{0}))
        (canonicalExtension.app (Λ[n+1, k] : SSet.{0}))).flip
      (SSet.anodyneExtensions.horn_ι k)
  · exact relativeCanonicalExtension_horn_anodyne n k

end

end Thomason.Construction

end

end OAI
