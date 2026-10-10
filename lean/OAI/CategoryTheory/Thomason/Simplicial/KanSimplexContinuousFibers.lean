import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Simplicial.FixedInternalPathMaps
import OAI.CategoryTheory.Thomason.Simplicial.HomotopyFiberPathEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.KanContractedFamilyLifting
import OAI.CategoryTheory.Thomason.Simplicial.KanFiberComponentTransport
import OAI.CategoryTheory.Thomason.Simplicial.KanRealizedEdgeComposition
import OAI.CategoryTheory.Thomason.Simplicial.RealizationSubcomplexSemantics
import OAI.CategoryTheory.Thomason.Simplicial.SingularKanComplex
import OAI.CategoryTheory.Thomason.Simplicial.SingularPathSpaceAdjunction
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages
import OAI.CategoryTheory.Thomason.Simplicial.TopologicalDeformationTransport
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition

namespace OAI

section

/-! # Exact finite cubical families in the original Kan total space -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- With finite source, the entire exact higher family and its two given
faces live in a single finite subcomplex of the original total space. -/
theorem finite_kan_cube_family_lift {A K E B : SSet.{0}} [K.Finite]
    (i : A ⟶ K) [Mono i] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (n : ℕ) (f : K ⟶ E) (h : A ⊗ (obj n) ⟶ E)
    (b : K ⊗ (obj n) ⟶ B)
    (h₀ : productChosenVertex A (initialVertex n) ≫ h = i ≫ f)
    (hb : h ≫ p = i ▷ (obj n) ≫ b)
    (hf : f ≫ p = productChosenVertex K (initialVertex n) ≫ b) :
    ∃ (S : E.Subcomplex) (_ : SSet.Finite S.toSSet)
      (eS : K ⊗ (obj n) ⟶ S.toSSet)
      (fS : K ⟶ S.toSSet) (hS : A ⊗ (obj n) ⟶ S.toSSet),
      fS ≫ S.ι = f ∧ hS ≫ S.ι = h ∧
      productChosenVertex K (initialVertex n) ≫ eS = fS ∧
      i ▷ (obj n) ≫ eS = hS ∧ eS ≫ S.ι ≫ p = b := by
  obtain ⟨e, he₀, hei, hep⟩ := exists_kan_contracted_family_lift i p (initialVertex n) (initialContraction n)
    (initialContraction_stationary n) f h b h₀ hb hf
  have : (obj n).Finite := realizedCube_finite n
  let S := SSet.Subcomplex.range e
  let eS := SSet.Subcomplex.toRange e
  let fS := productChosenVertex K (initialVertex n) ≫ eS
  let hS := i ▷ (obj n) ≫ eS
  refine ⟨S, inferInstance, eS, fS, hS, ?_, ?_, rfl, rfl, ?_⟩
  · dsimp only [fS]
    rw [Category.assoc, SSet.Subcomplex.toRange_ι, he₀]
  · dsimp only [hS]
    rw [Category.assoc, SSet.Subcomplex.toRange_ι, hei]
  · rw [← Category.assoc, SSet.Subcomplex.toRange_ι, hep]

end

end Thomason.Construction.RealizedCube

end

section

/-! # Realized fibrewise homotopies retain the literal continuous fibre -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- An exact simplicial homotopy over a base stays over that same
base point at every real cylinder parameter. -/
theorem realizedHomotopy_over {E F B : SSet.{0}} (p : E ⟶ B) (q : F ⟶ B)
    {f g : E ⟶ F} (H : SSet.Homotopy f g)
    (hH : H.h ≫ q = fst E Δ[1] ≫ p)
    (t : unitInterval) (x : SSet.toTop.obj E) :
    (SSet.toTop.map q).hom (RealizedCylinder.homotopy H (t,x)) =
      (SSet.toTop.map p).hom x := by
  rw [realizedHomotopy_apply]
  change (SSet.toTop.map H.h ≫ SSet.toTop.map q).hom
    ((RealizedCylinder.comparison E).hom (x,t)) = _
  rw [← SSet.toTop.map_comp, hH, SSet.toTop.map_comp]
  change (SSet.toTop.map p).hom ((SSet.toTop.map (fst E Δ[1])).hom
    ((RealizedCylinder.comparison E).hom (x,t))) = _
  rw [RealizedCylinder.comparison_first]

/-- Literal point fibres of a realized fibrewise simplicial homotopy
equivalence are weakly equivalent at EVERY real base point. -/
theorem realizedFiberMap_weak {E F B : SSet.{0}} (p : E ⟶ B) (q : F ⟶ B)
    (f : E ⟶ F) (g : F ⟶ E) (hf : f ≫ q = p) (hg : g ≫ p = q)
    (H : SSet.Homotopy (𝟙 E) (f ≫ g)) (K : SSet.Homotopy (𝟙 F) (g ≫ f))
    (hH : H.h ≫ p = fst E Δ[1] ≫ p)
    (hK : K.h ≫ q = fst F Δ[1] ≫ q) (b : SSet.toTop.obj B) :
    topologicalWeakEquivalences (continuousFiberMap (SSet.toTop.map p) (SSet.toTop.map q)
      b (SSet.toTop.map f) (by rw [← SSet.toTop.map_comp, hf])) := by
  let H' : (ContinuousMap.id (SSet.toTop.obj E)).Homotopy
      ((SSet.toTop.map g).hom.comp (SSet.toTop.map f).hom) := (RealizedCylinder.homotopy H).cast
    (by rw [SSet.toTop.map_id]; rfl) (by rw [SSet.toTop.map_comp]; rfl)
  let K' : (ContinuousMap.id (SSet.toTop.obj F)).Homotopy
      ((SSet.toTop.map f).hom.comp (SSet.toTop.map g).hom) := (RealizedCylinder.homotopy K).cast
    (by rw [SSet.toTop.map_id]; rfl) (by rw [SSet.toTop.map_comp]; rfl)
  exact continuousFiberMap_weak_of_over_equivalence _ _ b
    (SSet.toTop.map f) (SSet.toTop.map g)
    (by rw [← SSet.toTop.map_comp, hf]) (by rw [← SSet.toTop.map_comp, hg])
    H' K' (realizedHomotopy_over p p H hH) (realizedHomotopy_over q q K hK)

end

end Thomason.Construction

end

section

/-! # The exact base path of a realized Kan transport cylinder -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- The nondegenerate edge of the simplicial interval, with its actual
initial and final vertices. -/
def intervalEdge : SSet.Edge (initialSimplexVertex 1) (finalSimplexVertex 1) :=
  SSet.Edge.mk (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{0})))
    (by
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro j
      fin_cases j
      rfl)
    (by
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro j
      fin_cases j
      rfl)

/-- The canonical interval edge uses precisely the affine time coordinate
of the realized cylinder. -/
theorem intervalEdge_time (t : unitInterval) :
    PrismBarycentric.realizationTime.hom (RealizationPrism.edgePath intervalEdge t) = t := by
  change PrismBarycentric.realizationTime.hom
    (RealizationPrism.simplexPoint (Δ[1] : SSet.{0})
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{0}))) (Convexity.StdSimplex.homeomorphI.symm t)) = t
  change PrismBarycentric.realizationTime.hom
    ((RealizationPrism.leg (Δ[1] : SSet.{0})
      (CostructuredArrow.mk (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (𝟙 _))))).hom
      (ULift.up (Convexity.StdSimplex.homeomorphI.symm t))) = t
  rw [Equiv.symm_apply_apply]
  exact (PrismBarycentric.realizationTime_base _).trans
    (Convexity.StdSimplex.homeomorphI.apply_symm_apply t)

/-- Affine time distinguishes all points in the realized interval. -/
theorem realizationTime_injective : Function.Injective PrismBarycentric.realizationTime.hom := by
  intro x y h
  apply (SimplexCategory.mk 1).toTopHomeo.injective
  apply Convexity.StdSimplex.homeomorphI.injective
  exact h

/-- Every point of the cylinder has the same interval coordinate as the
canonical edge at that time. -/
theorem realizedCylinder_second {K : SSet.{0}} (x : SSet.toTop.obj K) (t : unitInterval) :
    (SSet.toTop.map (snd K (Δ[1] : SSet.{0}))).hom ((RealizedCylinder.comparison K).hom (x,t)) =
      RealizationPrism.edgePath intervalEdge t := by
  apply realizationTime_injective
  rw [RealizedCylinder.comparison_time, intervalEdge_time]

/-- The path realized by a base interval, with the exact image vertices. -/
def realizedIntervalPath {B : SSet.{0}} (g : (Δ[1] : SSet.{0}) ⟶ B) :
    Path (RealizationPrism.vertexPoint B (g.app _ (initialSimplexVertex 1)))
      (RealizationPrism.vertexPoint B (g.app _ (finalSimplexVertex 1))) :=
  ((RealizationPrism.edgePath intervalEdge).map (SSet.toTop.map g).hom.continuous).cast
    (RealizationPrism.map_vertexPoint g _).symm (RealizationPrism.map_vertexPoint g _).symm

/-- A simplicial cylinder lying exactly over the base interval realizes
to a continuous lift of that same parametrized path. -/
theorem realized_interval_homotopy_projection {K E B : SSet.{0}}
    (p : E ⟶ B) (g : (Δ[1] : SSet.{0}) ⟶ B) {f h : K ⟶ E}
    (H : SSet.Homotopy f h) (hH : H.h ≫ p = snd K Δ[1] ≫ g)
    (t : unitInterval) (x : SSet.toTop.obj K) :
    (SSet.toTop.map p).hom (RealizedCylinder.homotopy H (t,x)) = realizedIntervalPath g t := by
  rw [realizedHomotopy_apply]
  change (SSet.toTop.map H.h ≫ SSet.toTop.map p).hom
      ((RealizedCylinder.comparison K).hom (x,t)) = _
  rw [← SSet.toTop.map_comp, hH, SSet.toTop.map_comp]
  change (SSet.toTop.map g).hom
    ((SSet.toTop.map (snd K Δ[1])).hom ((RealizedCylinder.comparison K).hom (x,t))) = _
  rw [realizedCylinder_second]
  rfl

end

end Thomason.Construction

end

section

/-! # From a realized simplicial fibre to the genuine homotopy fibre -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The realized point-fibre inclusion has exactly the specified constant image. -/
theorem realizedPointFiber_projection {E B : SSet.{0}} (p : E ⟶ B) (b : B _⦋0⦌)
    (z : SSet.toTop.obj (simplicialPointFiber p b).toSSet) :
    (SSet.toTop.map p).hom ((SSet.toTop.map (simplicialPointFiber p b).ι).hom z) =
      RealizationPrism.vertexPoint B b := by
  have h := congrArg (fun f => f.hom z) (SSet.toTop.congr_map (simplicialPointFiber_ι_comp p b))
  rw [SSet.toTop.map_comp] at h
  exact h.trans (RealizationPrism.realization_const b z)

/-- The canonical comparison attaches the constant path at the specified vertex.
No preservation of pullbacks by realization is assumed. -/
def realizedPointFiberComparison {E B : SSet.{0}} (p : E ⟶ B) (b : B _⦋0⦌) :
    SSet.toTop.obj (simplicialPointFiber p b).toSSet ⟶
      continuousHomotopyFiber (SSet.toTop.map p) (RealizationPrism.vertexPoint B b) :=
  TopCat.ofHom {
    toFun z := ⟨⟨((SSet.toTop.map (simplicialPointFiber p b).ι).hom z,
      ContinuousMap.const _ (RealizationPrism.vertexPoint B b)),
      (realizedPointFiber_projection p b z).symm⟩, rfl⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact (SSet.toTop.map (simplicialPointFiber p b).ι).hom.continuous.prodMk continuous_const }

@[reassoc]
theorem realizedPointFiberComparison_retraction {E B : SSet.{0}} (p : E ⟶ B)
    (b : B _⦋0⦌) :
    realizedPointFiberComparison p b ≫
      continuousHomotopyFiberRetraction (SSet.toTop.map p) (RealizationPrism.vertexPoint B b) =
        SSet.toTop.map (simplicialPointFiber p b).ι := rfl

/-- For any Kan fibration over a standard simplex, the actual point-fibre
comparison is a weak equivalence. This is the local geometric homotopy-fibre
statement, proved independently of general acyclic Kan lifting. -/
theorem kan_simplex_realizedPointFiberComparison_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (b : (Δ[n] : SSet.{0}) _⦋0⦌) :
    topologicalWeakEquivalences (realizedPointFiberComparison p b) := by
  have hr : topologicalWeakEquivalences
      (continuousHomotopyFiberRetraction (SSet.toTop.map p)
        (RealizationPrism.vertexPoint (Δ[n] : SSet.{0}) b)) :=
    homotopyEquiv_isWeakHomotopyEquivalence
      (simplexHomotopyFiberEquiv n (SSet.toTop.map p) _)
  apply topologicalWeakEquivalences.of_postcomp _ _ hr
  rw [realizedPointFiberComparison_retraction]
  exact kan_simplex_anyFiber_weak n p b

end

end Thomason.Construction

end

section

/-! # Kan transport commutes with the genuine homotopy-fibre comparison -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Attach the actual realized base edge to the initial point fibre. -/
def realizedFiberAlongInterval {E B : SSet.{0}} (p : E ⟶ B)
    (g : (Δ[1] : SSet.{0}) ⟶ B) :
    SSet.toTop.obj (simplicialPointFiber p (g.app _ (initialSimplexVertex 1))).toSSet ⟶
      continuousHomotopyFiber (SSet.toTop.map p)
        (RealizationPrism.vertexPoint B (g.app _ (finalSimplexVertex 1))) :=
  homotopyFiberFromPath (SSet.toTop.map p)
    (SSet.toTop.map (simplicialPointFiber p (g.app _ (initialSimplexVertex 1))).ι)
    (realizedIntervalPath g) (realizedPointFiber_projection p _)

/-- The weak simplicial transport furnished by the Kan lifting property
commutes, by a constructed continuous homotopy, with the actual comparison
to the terminal homotopy fibre. The homotopy retains the prescribed base
edge and the remaining-path coordinate. -/
theorem kan_transport_homotopy_fiber {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (g : (Δ[1] : SSet.{0}) ⟶ B) :
    ∃ t : (simplicialPointFiber p (g.app _ (initialSimplexVertex 1))).toSSet ⟶
        (simplicialPointFiber p (g.app _ (finalSimplexVertex 1))).toSSet,
      realizationWeakEquivalences t ∧
      Nonempty ((realizedFiberAlongInterval p g).hom.Homotopy
        (SSet.toTop.map t ≫ realizedPointFiberComparison p (g.app _ (finalSimplexVertex 1))).hom) := by
  obtain ⟨t, ht, H, hH⟩ := kan_interval_fiber_transport p g
  let R := RealizedCylinder.homotopy H
  have hR (s : unitInterval)
      (a : SSet.toTop.obj (simplicialPointFiber p (g.app _ (initialSimplexVertex 1))).toSSet) :
      (SSet.toTop.map p).hom (R (s,a)) = realizedIntervalPath g s :=
    realized_interval_homotopy_projection p g H hH s a
  let T := homotopyFiberLiftedPath (SSet.toTop.map p) R (realizedIntervalPath g) hR
  have he : homotopyFiberFromPath (SSet.toTop.map p)
      (SSet.toTop.map (t ≫ (simplicialPointFiber p (g.app _ (finalSimplexVertex 1))).ι))
      (Path.refl (RealizationPrism.vertexPoint B (g.app _ (finalSimplexVertex 1))))
      (fun a => (congrArg (SSet.toTop.map p).hom (R.apply_one a)).symm.trans
        ((hR 1 a).trans (realizedIntervalPath g).target)) =
      SSet.toTop.map t ≫ realizedPointFiberComparison p (g.app _ (finalSimplexVertex 1)) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change (SSet.toTop.map (t ≫ _)).hom z = _
      rw [SSet.toTop.map_comp]
      rfl
    · rfl
  refine ⟨t, ht, ⟨T.cast ?_ (congrArg TopCat.Hom.hom he)⟩⟩
  rfl

/-- Weakness of the canonical comparison is detected after transporting
any neighbouring fibre along its actual base edge. This uses all homotopy
groups, with no global fibration-realization theorem assumed. -/
theorem kan_transport_homotopy_fiber_weak_iff {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (g : (Δ[1] : SSet.{0}) ⟶ B) :
    topologicalWeakEquivalences (realizedFiberAlongInterval p g) ↔
      topologicalWeakEquivalences
        (realizedPointFiberComparison p (g.app _ (finalSimplexVertex 1))) := by
  obtain ⟨t, ht, ⟨H⟩⟩ := kan_transport_homotopy_fiber p g
  exact (isWeakHomotopyEquivalence_homotopy_iff H).trans
    (topologicalWeakEquivalences.precomp_iff _ _ ht)

end

end Thomason.Construction

end

section

/-! # The genuine fibre comparison is invariant along base paths -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Homotopic chosen paths produce homotopic maps from a fixed point
fibre into the actual terminal homotopy fibre. -/
def homotopyFiberFromPathHomotopy {A E B : TopCat.{0}} (p : E ⟶ B) (f : A ⟶ E)
    {x y : B} {γ δ : Path x y} (H : γ.Homotopy δ) (hf : ∀ a, p.hom (f.hom a) = x) :
    (homotopyFiberFromPath p f γ hf).hom.Homotopy
      (homotopyFiberFromPath p f δ hf).hom where
  toFun z := ⟨⟨(f.hom z.2, (H.eval z.1).toContinuousMap),
    (H.eval z.1).source.trans (hf z.2).symm⟩, (H.eval z.1).target⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × A) × unitInterval => H (z.1.1,z.2))
    fun_prop
  map_zero_left a := by
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    exact congrArg Path.toContinuousMap H.eval_zero
  map_one_left a := by
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    exact congrArg Path.toContinuousMap H.eval_one

/-- The exact comparison with a transported point fibre agrees with
appending the base path, up to the canonical left-unit homotopy. -/
theorem realizedFiberAlongInterval_append {E B : SSet.{0}} (p : E ⟶ B)
    (g : (Δ[1] : SSet.{0}) ⟶ B) :
    Nonempty ((realizedPointFiberComparison p (g.app _ (initialSimplexVertex 1)) ≫
      homotopyFiberPathTransport (SSet.toTop.map p) (realizedIntervalPath g)).hom.Homotopy
      (realizedFiberAlongInterval p g).hom) := by
  let x := RealizationPrism.vertexPoint B (g.app _ (initialSimplexVertex 1))
  let γ := realizedIntervalPath g
  have U : ((Path.refl x).trans γ).Homotopy γ := Path.Homotopy.reflTrans γ
  let H := homotopyFiberFromPathHomotopy (SSet.toTop.map p)
    (SSet.toTop.map (simplicialPointFiber p (g.app _ (initialSimplexVertex 1))).ι)
    U (realizedPointFiber_projection p _)
  refine ⟨H.cast ?_ rfl⟩
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Subtype.ext
  refine Prod.ext (by rfl) ?_
  rfl

/-- For an arbitrary Kan fibration, the full actual weak-equivalence test
for its point-fibre comparison is unchanged along a base interval. -/
theorem kan_fiber_comparison_weak_iff_of_interval {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (g : (Δ[1] : SSet.{0}) ⟶ B) :
    topologicalWeakEquivalences
      (realizedPointFiberComparison p (g.app _ (initialSimplexVertex 1))) ↔
    topologicalWeakEquivalences
      (realizedPointFiberComparison p (g.app _ (finalSimplexVertex 1))) := by
  obtain ⟨H⟩ := realizedFiberAlongInterval_append p g
  have hγ := homotopyFiberPathTransport_weak (SSet.toTop.map p) (realizedIntervalPath g)
  exact (topologicalWeakEquivalences.postcomp_iff _ _ hγ).symm.trans
    ((isWeakHomotopyEquivalence_homotopy_iff H).trans
      (kan_transport_homotopy_fiber_weak_iff p g))

/-- The same genuine comparison test is invariant along every simplicial
edge, with its given endpoints. -/
theorem kan_fiber_comparison_weak_iff_of_edge {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] {x y : B _⦋0⦌} (e : SSet.Edge x y) :
    topologicalWeakEquivalences (realizedPointFiberComparison p x) ↔
      topologicalWeakEquivalences (realizedPointFiberComparison p y) := by
  let g : (Δ[1] : SSet.{0}) ⟶ B := SSet.yonedaEquiv.symm e.edge
  have hi : g.app _ (initialSimplexVertex 1) = x := by
    dsimp only [g, initialSimplexVertex]
    rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
    have hv : RealizationPrism.vertexOperator (0 : Fin 2) = SimplexCategory.δ (1 : Fin 2) := by
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro j
      fin_cases j
      rfl
    rw [hv]
    exact e.src_eq
  have ht : g.app _ (finalSimplexVertex 1) = y := by
    dsimp only [g, finalSimplexVertex]
    rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
    have hv : RealizationPrism.vertexOperator (Fin.last 1) = SimplexCategory.δ (0 : Fin 2) := by
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro j
      fin_cases j
      rfl
    rw [hv]
    exact e.tgt_eq
  have h := kan_fiber_comparison_weak_iff_of_interval p g
  rw [hi, ht] at h
  exact h

/-- The actual point-fibre/homotopy-fibre comparison is weak at one vertex
if and only if it is weak at any vertex joined to it by a continuous path. -/
theorem kan_fiber_comparison_weak_iff_of_realization_path {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] {x y : B _⦋0⦌}
    (h : Path (RealizationPrism.vertexPoint B x) (RealizationPrism.vertexPoint B y)) :
    topologicalWeakEquivalences (realizedPointFiberComparison p x) ↔
      topologicalWeakEquivalences (realizedPointFiberComparison p y) := by
  have hz := RealizationPrism.edge_zigzag_of_realization_path h
  clear h
  induction hz with
  | rel a b h => exact kan_fiber_comparison_weak_iff_of_edge p (Classical.choice h)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end

end Thomason.Construction

end

section

/-! # Realization identifies literal simplicial vertex fibres with actual fibres -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

theorem realizedVertexSubcomplex_range (B : SSet.{0}) (b : B _⦋0⦌) :
    Set.range (SSet.toTop.map (SSet.Subcomplex.ofSimplex b).ι).hom =
      {RealizationPrism.vertexPoint B b} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rw [SSet.Subcomplex.ofSimplex_ι, RealizationPrism.realization_const]
    exact Set.mem_singleton _
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    let a : (SSet.Subcomplex.ofSimplex b).toSSet _⦋0⦌ :=
      ⟨b, SSet.Subcomplex.mem_ofSimplex_obj b⟩
    refine ⟨RealizationPrism.vertexPoint _ a, ?_⟩
    exact RealizationPrism.map_vertexPoint _ a

/-- Realization commutes homeomorphically with a fibre over a simplicial
vertex, using the closed subcomplex embedding. -/
def realizedPointFiberHomeomorph {E B : SSet.{0}} (p : E ⟶ B) (b : B _⦋0⦌) :
    SSet.toTop.obj (simplicialPointFiber p b).toSSet ≃ₜ
      {x : SSet.toTop.obj E // (SSet.toTop.map p).hom x = RealizationPrism.vertexPoint B b} :=
  (RealizationPrism.preimageHomeomorph p (SSet.Subcomplex.ofSimplex b)).trans
    (Homeomorph.setCongr (by
      ext x
      rw [Set.mem_preimage, realizedVertexSubcomplex_range, Set.mem_singleton_iff]
      rfl))

/-- The homeomorphism retains the original total-space point exactly. -/
theorem realizedPointFiberHomeomorph_val {E B : SSet.{0}} (p : E ⟶ B) (b : B _⦋0⦌)
    (x : SSet.toTop.obj (simplicialPointFiber p b).toSSet) :
    (realizedPointFiberHomeomorph p b x).val =
      (SSet.toTop.map (simplicialPointFiber p b).ι).hom x := rfl

/-- The canonical map from the literal continuous point fibre into the
homotopy fibre appends its constant path. -/
def continuousPointFiberComparison {X Y : TopCat.{0}} (p : X ⟶ Y) (b : Y) :
    TopCat.of {x : X // p.hom x = b} ⟶ continuousHomotopyFiber p b :=
  TopCat.ofHom {
    toFun x := ⟨⟨(x.val, ContinuousMap.const _ b), x.property.symm⟩, rfl⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.prodMk continuous_const }

/-- The two fibre comparisons commute exactly under the homeomorphism. -/
theorem realizedPointFiberComparison_homeomorph {E B : SSet.{0}} (p : E ⟶ B)
    (b : B _⦋0⦌) :
    (TopCat.isoOfHomeo (realizedPointFiberHomeomorph p b)).hom ≫
      continuousPointFiberComparison (SSet.toTop.map p) (RealizationPrism.vertexPoint B b) =
        realizedPointFiberComparison p b := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- At every vertex of a standard simplex, the realized Kan fibration is
quasifibrant: its literal continuous fibre maps weakly to its homotopy fibre. -/
theorem kan_simplex_continuousPointFiberComparison_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (b : (Δ[n] : SSet.{0}) _⦋0⦌) :
    topologicalWeakEquivalences
      (continuousPointFiberComparison (SSet.toTop.map p) (RealizationPrism.vertexPoint _ b)) := by
  apply (topologicalWeakEquivalences.cancel_left_of_respectsIso
    (TopCat.isoOfHomeo (realizedPointFiberHomeomorph p b)).hom _).mp
  rw [realizedPointFiberComparison_homeomorph]
  exact kan_simplex_realizedPointFiberComparison_weak n p b

end

end Thomason.Construction

end

section

/-! # Naturality of the literal-fibre to homotopy-fibre comparison -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- The constant-path comparison commutes exactly with every commutative
square of continuous maps, including the full path coordinate. -/
@[reassoc] theorem continuousPointFiberComparison_naturality {X Y A B : TopCat.{0}}
    (p : X ⟶ A) (q : Y ⟶ B) (f : X ⟶ Y) (g : A ⟶ B)
    (h : f ≫ q = p ≫ g) (b : A) :
    continuousFiberBaseChangeMap p q f g h b ≫
        continuousPointFiberComparison q (g.hom b) =
      continuousPointFiberComparison p b ≫ continuousHomotopyFiberMap p q f g h b := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    rfl

/-- If the two canonical comparisons are weak equivalences, a square
induces a weak equivalence on literal fibres precisely when it does on
homotopy fibres. This transports the actual weak-equivalence tests. -/
theorem continuousFiberBaseChange_weak_iff_homotopyFiberMap {X Y A B : TopCat.{0}}
    (p : X ⟶ A) (q : Y ⟶ B) (f : X ⟶ Y) (g : A ⟶ B)
    (h : f ≫ q = p ≫ g) (b : A)
    (hp : topologicalWeakEquivalences (continuousPointFiberComparison p b))
    (hq : topologicalWeakEquivalences (continuousPointFiberComparison q (g.hom b))) :
    topologicalWeakEquivalences (continuousFiberBaseChangeMap p q f g h b) ↔
      topologicalWeakEquivalences (continuousHomotopyFiberMap p q f g h b) := by
  have he := congrArg
    (fun k : continuousFiber p b ⟶ continuousHomotopyFiber q (g.hom b) =>
      topologicalWeakEquivalences k)
    (continuousPointFiberComparison_naturality p q f g h b)
  constructor
  · intro hf
    apply topologicalWeakEquivalences.of_precomp _ _ hp
    exact he.mp (topologicalWeakEquivalences.comp_mem _ _ hf hq)
  · intro hf
    apply topologicalWeakEquivalences.of_postcomp _ _ hq
    exact he.mpr (topologicalWeakEquivalences.comp_mem _ _ hp hf)

end

end Thomason.Construction

end

section

/-! # Actual Kan fibre comparisons and base changes over finite cubes -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The literal realized vertex fibre of a Kan fibration over a finite cube
maps weakly to its genuine continuous homotopy fibre. -/
theorem kan_realizedPointFiberComparison_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ obj n) [HomotopicalAlgebra.Fibration p] (b : (obj n) _⦋0⦌) :
    topologicalWeakEquivalences (realizedPointFiberComparison p b) := by
  have hr : topologicalWeakEquivalences
      (continuousHomotopyFiberRetraction (SSet.toTop.map p)
        (RealizationPrism.vertexPoint (obj n) b)) :=
    homotopyEquiv_isWeakHomotopyEquivalence (homotopyFiberEquiv n (SSet.toTop.map p) _)
  apply topologicalWeakEquivalences.of_postcomp _ _ hr
  rw [realizedPointFiberComparison_retraction]
  exact kan_any_fiber_weak n p b

/-- Under the constructed fibre homeomorphism, the comparison is exactly
the ordinary continuous point-fibre map which appends a constant path. -/
theorem kan_continuousPointFiberComparison_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ obj n) [HomotopicalAlgebra.Fibration p] (b : (obj n) _⦋0⦌) :
    topologicalWeakEquivalences
      (continuousPointFiberComparison (SSet.toTop.map p) (RealizationPrism.vertexPoint _ b)) := by
  apply (topologicalWeakEquivalences.cancel_left_of_respectsIso
    (TopCat.isoOfHomeo (realizedPointFiberHomeomorph p b)).hom _).mp
  rw [realizedPointFiberComparison_homeomorph]
  exact kan_realizedPointFiberComparison_weak n p b

/-- Every simplicial map between finite cubes preserves the total space
of a Kan fibration up to the actual realization weak-equivalence test. -/
theorem kan_baseChange_weak {E : SSet.{0}} (n m : ℕ)
    (p : E ⟶ obj n) [HomotopicalAlgebra.Fibration p] (g : obj m ⟶ obj n) :
    realizationWeakEquivalences (pullback.fst p g) := by
  have : HomotopicalAlgebra.Fibration (pullback.snd p g) := kan_pullback_snd_fibration p g
  have hi : realizationWeakEquivalences (pointFiberToPullback p g (finalVertex m)) := by
    rw [← simplicialPointFiberBaseChangeIso_hom_ι]
    exact realizationWeakEquivalences.comp_mem _ _
      (realizationWeakEquivalences.of_isIso _) (kan_any_fiber_weak m _ _)
  apply realizationWeakEquivalences.of_precomp (pointFiberToPullback p g (finalVertex m)) _ hi
  rw [pointFiberToPullback_fst]
  exact kan_any_fiber_weak n p _

/-- The actual map on continuous homotopy fibres induced by a cubical
base change retains both point and path coordinates. -/
def homotopyFiberMap {E : SSet.{0}} (n m : ℕ)
    (p : E ⟶ obj n) (g : obj m ⟶ obj n) (b : SSet.toTop.obj (obj m)) :
    continuousHomotopyFiber (SSet.toTop.map (pullback.snd p g)) b ⟶
      continuousHomotopyFiber (SSet.toTop.map p) ((SSet.toTop.map g).hom b) :=
  continuousHomotopyFiberMap _ _ (SSet.toTop.map (pullback.fst p g)) (SSet.toTop.map g)
    (by rw [← SSet.toTop.map_comp, pullback.condition, SSet.toTop.map_comp]) b

/-- Cubical base change commutes with the genuine continuous homotopy fibre
by an actual weak equivalence. -/
theorem homotopyFiberMap_weak {E : SSet.{0}} (n m : ℕ)
    (p : E ⟶ obj n) [HomotopicalAlgebra.Fibration p] (g : obj m ⟶ obj n)
    (b : SSet.toTop.obj (obj m)) :
    topologicalWeakEquivalences (homotopyFiberMap n m p g b) := by
  apply continuousHomotopyFiberMap_weak
  · exact homotopyEquiv_isWeakHomotopyEquivalence (homotopyFiberEquiv m _ _)
  · exact homotopyEquiv_isWeakHomotopyEquivalence (homotopyFiberEquiv n _ _)
  · exact kan_baseChange_weak n m p g

end

end Thomason.Construction.RealizedCube

end

section

/-! # All continuous fibres of a Kan fibration over a cube -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The literal fibre inclusion of a realized product projection over any
point of the cube is a weak equivalence. -/
theorem realizedProductCubeFiberInclusion_weak (F : SSet.{0}) (n : ℕ)
    (b : SSet.toTop.obj (obj n)) :
    topologicalWeakEquivalences (continuousFiberInclusion
      (SSet.toTop.map (snd F (obj n))) b) := by
  have := realizationProductComparison_cube_isIso F n
  exact continuousFiberInclusion_weak_of_iso _
    (continuousProductProjection (SSet.toTop.obj F) (SSet.toTop.obj (obj n))) b
    (asIso (realizationProductComparison F (obj n))) rfl
    (homotopyEquiv_isWeakHomotopyEquivalence
      (continuousProductFiberEquiv _ _ b (pointInterpolation n)
        (pointInterpolation_zero n) (pointInterpolation_one n)))

/-- For a Kan fibration over a standard cube, EVERY literal continuous
fibre includes by a weak equivalence. The point need not be a vertex. -/
theorem kan_cube_continuousFiberInclusion_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (obj n)) [HomotopicalAlgebra.Fibration p]
    (b : SSet.toTop.obj (obj n)) :
    topologicalWeakEquivalences (continuousFiberInclusion (SSet.toTop.map p) b) := by
  obtain ⟨q, s, hq, hs, _, _, H, T, hH, hT⟩ := kan_contracted_base_trivialization (initialVertex n) (initialContraction n)
    (initialContraction_stationary n) p
  let F := (simplicialPointFiber p (initialVertex n)).toSSet
  have hqW := (simplicial_homotopy_inverse_weak_pair q s H T).1
  have hqF := realizedFiberMap_weak p (snd F (obj n)) q s hq hs H T hH hT b
  have hprod := realizedProductCubeFiberInclusion_weak F n b
  apply topologicalWeakEquivalences.of_postcomp _ (SSet.toTop.map q) hqW
  rw [← continuousFiberMap_inclusion (SSet.toTop.map p)
    (SSet.toTop.map (snd F (obj n))) b (SSet.toTop.map q)
    (by rw [← SSet.toTop.map_comp, hq])]
  exact topologicalWeakEquivalences.comp_mem _ _ hqF hprod

/-- The canonical constant-path comparison from the literal continuous
fibre to the actual homotopy fibre is weak at every point of a cube. -/
theorem kan_cube_allPointFiberComparison_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (obj n)) [HomotopicalAlgebra.Fibration p]
    (b : SSet.toTop.obj (obj n)) :
    topologicalWeakEquivalences (continuousPointFiberComparison (SSet.toTop.map p) b) := by
  have hr : topologicalWeakEquivalences
      (continuousHomotopyFiberRetraction (SSet.toTop.map p) b) :=
    homotopyEquiv_isWeakHomotopyEquivalence (homotopyFiberEquiv n _ b)
  apply topologicalWeakEquivalences.of_postcomp _ _ hr
  exact kan_cube_continuousFiberInclusion_weak n p b

end

end Thomason.Construction.RealizedCube

end

section

/-! # Pointwise quasifibration compatibility on every cube restriction -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Restriction along any map of standard cubes induces a weak
equivalence of the literal continuous fibres at every real point. This
includes all faces, degeneracies, and their composites. -/
theorem kan_cube_continuousFiberBaseChange_weak {E : SSet.{0}} (n m : ℕ)
    (p : E ⟶ (obj n)) [HomotopicalAlgebra.Fibration p]
    (g : (obj m) ⟶ obj n) (b : SSet.toTop.obj (obj m)) :
    topologicalWeakEquivalences (continuousFiberBaseChangeMap
      (SSet.toTop.map (pullback.snd p g)) (SSet.toTop.map p)
      (SSet.toTop.map (pullback.fst p g)) (SSet.toTop.map g)
      (by rw [← SSet.toTop.map_comp, pullback.condition, SSet.toTop.map_comp]) b) := by
  have : HomotopicalAlgebra.Fibration (pullback.snd p g) := kan_pullback_snd_fibration p g
  exact continuousFiberBaseChangeMap_weak _ _ _ _ _ b
    (kan_baseChange_weak n m p g)
    (kan_cube_continuousFiberInclusion_weak m (pullback.snd p g) b)
    (kan_cube_continuousFiberInclusion_weak n p _)

end

end Thomason.Construction.RealizedCube

end

section

/-! # Literal fibres over finite contracted simplicial parameter spaces -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The fibre of the ordinary second projection is canonically its first
factor. This identification retains the literal subspace topology. -/
def continuousProductFiberHomeomorph (X B : TopCat.{0}) (b : B) :
    continuousFiber (continuousProductProjection X B) b ≃ₜ X where
  toFun z := z.val.1
  invFun x := ⟨(x, b), rfl⟩
  left_inv z := by
    apply Subtype.ext
    exact Prod.ext rfl z.property.symm
  right_inv _ := rfl
  continuous_toFun := continuous_fst.comp continuous_subtype_val
  continuous_invFun := (continuous_id.prodMk continuous_const).subtype_mk _

/-- A stationary contraction of a finite simplicial base makes the
inclusion of every literal fibre of the realized product weak, even at a
point which is not a simplicial vertex. -/
theorem realizedFiniteContractedProductFiberInclusion_weak
    (F B : SSet.{0}) [B.Finite] (v : B _⦋0⦌)
    (C : SSet.Homotopy (SSet.const v) (𝟙 B))
    (hC : ∀ L : SSet.{0}, (SSet.const (X := L) v) ▷ Δ[1] ≫ C.h =
      fst L Δ[1] ≫ SSet.const v)
    (b : SSet.toTop.obj B) :
    topologicalWeakEquivalences (continuousFiberInclusion
      (SSet.toTop.map (snd F B)) b) := by
  let := realizationProductComparison_finite_isIso F B
  have hj := anodyne_realization_weak (productChosenVertex F v)
    (productChosenVertex_anodyne F v C hC)
  have hfst : realizationWeakEquivalences (fst F B) := by
    apply realizationWeakEquivalences.of_precomp (productChosenVertex F v) _ hj
    rw [show productChosenVertex F v ≫ fst F B = 𝟙 F from lift_fst _ _]
    exact realizationWeakEquivalences.id_mem F
  let π : TopCat.of (SSet.toTop.obj F × SSet.toTop.obj B) ⟶ SSet.toTop.obj F :=
    TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  have hπ : topologicalWeakEquivalences π := by
    apply topologicalWeakEquivalences.of_precomp (realizationProductComparison F B) π
      (topologicalWeakEquivalences.of_isIso _)
    exact hfst
  have hι : topologicalWeakEquivalences (continuousFiberInclusion
      (continuousProductProjection (SSet.toTop.obj F) (SSet.toTop.obj B)) b) := by
    apply topologicalWeakEquivalences.of_postcomp _ π hπ
    exact homotopyEquiv_isWeakHomotopyEquivalence
      (continuousProductFiberHomeomorph (SSet.toTop.obj F) (SSet.toTop.obj B) b).toHomotopyEquiv
  exact continuousFiberInclusion_weak_of_iso _
    (continuousProductProjection (SSet.toTop.obj F) (SSet.toTop.obj B)) b
    (asIso (realizationProductComparison F B)) rfl hι

/-- The exact fibrewise Kan trivialization transports the preceding
product theorem to any Kan fibration over the finite contracted base. -/
theorem kan_finite_contracted_continuousFiberInclusion_weak
    {E B : SSet.{0}} [B.Finite] (v : B _⦋0⦌)
    (C : SSet.Homotopy (SSet.const v) (𝟙 B))
    (hC : ∀ L : SSet.{0}, (SSet.const (X := L) v) ▷ Δ[1] ≫ C.h =
      fst L Δ[1] ≫ SSet.const v)
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p] (b : SSet.toTop.obj B) :
    topologicalWeakEquivalences (continuousFiberInclusion (SSet.toTop.map p) b) := by
  obtain ⟨q, s, hq, hs, _, _, H, T, hH, hT⟩ :=
    kan_contracted_base_trivialization v C hC p
  let F := (simplicialPointFiber p v).toSSet
  have hqW := (simplicial_homotopy_inverse_weak_pair q s H T).1
  have hqF := realizedFiberMap_weak p (snd F B) q s hq hs H T hH hT b
  have hprod := realizedFiniteContractedProductFiberInclusion_weak F B v C hC b
  apply topologicalWeakEquivalences.of_postcomp _ (SSet.toTop.map q) hqW
  rw [← continuousFiberMap_inclusion (SSet.toTop.map p)
    (SSet.toTop.map (snd F B)) b (SSet.toTop.map q)
    (by rw [← SSet.toTop.map_comp, hq])]
  exact topologicalWeakEquivalences.comp_mem _ _ hqF hprod

/-- At a vertex this is the inclusion of the original simplicial fibre,
via the proved realization homeomorphism of literal point fibres. -/
theorem kan_finite_contracted_simplicialFiberInclusion_weak
    {E B : SSet.{0}} [B.Finite] (v : B _⦋0⦌)
    (C : SSet.Homotopy (SSet.const v) (𝟙 B))
    (hC : ∀ L : SSet.{0}, (SSet.const (X := L) v) ▷ Δ[1] ≫ C.h =
      fst L Δ[1] ≫ SSet.const v)
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p] (b : B _⦋0⦌) :
    realizationWeakEquivalences (simplicialPointFiber p b).ι := by
  have h := kan_finite_contracted_continuousFiberInclusion_weak v C hC p
    (RealizationPrism.vertexPoint B b)
  exact topologicalWeakEquivalences.comp_mem
    (TopCat.isoOfHomeo (realizedPointFiberHomeomorph p b)).hom
    (continuousFiberInclusion (SSet.toTop.map p) (RealizationPrism.vertexPoint B b))
    (topologicalWeakEquivalences.of_isIso _) h

end

end Thomason.Construction

end

section

/-! # Weak base change between finite contracted parameter spaces -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The pullback projection of a Kan fibration along a map between finite
contracted parameter complexes is weak. The proof identifies a common
literal vertex fibre; it does not assume right properness. -/
theorem kan_finite_contracted_baseChange_weak
    {E B D : SSet.{0}} [B.Finite] [D.Finite]
    (v : B _⦋0⦌) (w : D _⦋0⦌)
    (C : SSet.Homotopy (SSet.const v) (𝟙 B))
    (T : SSet.Homotopy (SSet.const w) (𝟙 D))
    (hC : ∀ L : SSet.{0}, (SSet.const (X := L) v) ▷ Δ[1] ≫ C.h =
      fst L Δ[1] ≫ SSet.const v)
    (hT : ∀ L : SSet.{0}, (SSet.const (X := L) w) ▷ Δ[1] ≫ T.h =
      fst L Δ[1] ≫ SSet.const w)
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p] (g : D ⟶ B) :
    realizationWeakEquivalences (pullback.fst p g) := by
  have : HomotopicalAlgebra.Fibration (pullback.snd p g) :=
    kan_pullback_snd_fibration p g
  have hsource := kan_finite_contracted_simplicialFiberInclusion_weak w T hT
    (pullback.snd p g) w
  have htarget := kan_finite_contracted_simplicialFiberInclusion_weak v C hC p
    (g.app _ w)
  have he : realizationWeakEquivalences (pointFiberToPullback p g w) := by
    rw [← simplicialPointFiberBaseChangeIso_hom_ι]
    exact realizationWeakEquivalences.comp_mem _ _
      (realizationWeakEquivalences.of_isIso _) hsource
  apply realizationWeakEquivalences.of_precomp (pointFiberToPullback p g w) _ he
  rw [pointFiberToPullback_fst]
  exact htarget

/-- Under the same finite-parameter hypotheses, every real-point fibre
map induced by base change is weak. This retains the exact specified
point, rather than replacing it by a chosen vertex. -/
theorem kan_finite_contracted_continuousFiberBaseChange_weak
    {E B D : SSet.{0}} [B.Finite] [D.Finite]
    (v : B _⦋0⦌) (w : D _⦋0⦌)
    (C : SSet.Homotopy (SSet.const v) (𝟙 B))
    (T : SSet.Homotopy (SSet.const w) (𝟙 D))
    (hC : ∀ L : SSet.{0}, (SSet.const (X := L) v) ▷ Δ[1] ≫ C.h =
      fst L Δ[1] ≫ SSet.const v)
    (hT : ∀ L : SSet.{0}, (SSet.const (X := L) w) ▷ Δ[1] ≫ T.h =
      fst L Δ[1] ≫ SSet.const w)
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p] (g : D ⟶ B)
    (b : SSet.toTop.obj D) :
    topologicalWeakEquivalences (continuousFiberBaseChangeMap
      (SSet.toTop.map (pullback.snd p g)) (SSet.toTop.map p)
      (SSet.toTop.map (pullback.fst p g)) (SSet.toTop.map g)
      (by rw [← SSet.toTop.map_comp, pullback.condition, SSet.toTop.map_comp]) b) := by
  have : HomotopicalAlgebra.Fibration (pullback.snd p g) :=
    kan_pullback_snd_fibration p g
  exact continuousFiberBaseChangeMap_weak _ _ _ _ _ b
    (kan_finite_contracted_baseChange_weak v w C T hC hT p g)
    (kan_finite_contracted_continuousFiberInclusion_weak w T hT (pullback.snd p g) b)
    (kan_finite_contracted_continuousFiberInclusion_weak v C hC p _)

end

end Thomason.Construction

end

section

/-! # All continuous fibres of a Kan fibration over a simplex -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The literal fibre inclusion of a realized product projection over any
point of the simplex is a weak equivalence. -/
theorem realizedProductSimplexFiberInclusion_weak (F : SSet.{0}) (n : ℕ)
    (b : SSet.toTop.obj (Δ[n] : SSet.{0})) :
    topologicalWeakEquivalences (continuousFiberInclusion
      (SSet.toTop.map (snd F (Δ[n] : SSet.{0}))) b) := by
  have := realizationProductComparison_simplex_isIso F n
  exact continuousFiberInclusion_weak_of_iso _
    (continuousProductProjection (SSet.toTop.obj F) (SSet.toTop.obj (Δ[n] : SSet.{0}))) b
    (asIso (realizationProductComparison F (Δ[n] : SSet.{0}))) rfl
    (continuousProductSimplexFiberInclusion_weak _ n b)

/-- For a Kan fibration over a standard simplex, EVERY literal continuous
fibre includes by a weak equivalence. The point need not be a vertex. -/
theorem kan_simplex_continuousFiberInclusion_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (b : SSet.toTop.obj (Δ[n] : SSet.{0})) :
    topologicalWeakEquivalences (continuousFiberInclusion (SSet.toTop.map p) b) := by
  obtain ⟨q, s, hq, hs, _, _, H, T, hH, hT⟩ := kan_simplex_fibrewise_trivialization n p
  let F := (simplicialPointFiber p (initialSimplexVertex n)).toSSet
  have hqW := (simplicial_homotopy_inverse_weak_pair q s H T).1
  have hqF := realizedFiberMap_weak p (snd F (Δ[n] : SSet.{0})) q s hq hs H T hH hT b
  have hprod := realizedProductSimplexFiberInclusion_weak F n b
  apply topologicalWeakEquivalences.of_postcomp _ (SSet.toTop.map q) hqW
  rw [← continuousFiberMap_inclusion (SSet.toTop.map p)
    (SSet.toTop.map (snd F (Δ[n] : SSet.{0}))) b (SSet.toTop.map q)
    (by rw [← SSet.toTop.map_comp, hq])]
  exact topologicalWeakEquivalences.comp_mem _ _ hqF hprod

/-- The canonical constant-path comparison from the literal continuous
fibre to the actual homotopy fibre is weak at every point of a simplex. -/
theorem kan_simplex_allPointFiberComparison_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (b : SSet.toTop.obj (Δ[n] : SSet.{0})) :
    topologicalWeakEquivalences (continuousPointFiberComparison (SSet.toTop.map p) b) := by
  have hr : topologicalWeakEquivalences
      (continuousHomotopyFiberRetraction (SSet.toTop.map p) b) :=
    homotopyEquiv_isWeakHomotopyEquivalence (simplexHomotopyFiberEquiv n _ b)
  apply topologicalWeakEquivalences.of_postcomp _ _ hr
  exact kan_simplex_continuousFiberInclusion_weak n p b

end

end Thomason.Construction

end

end OAI
