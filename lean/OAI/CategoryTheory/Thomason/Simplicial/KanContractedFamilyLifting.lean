import OAI.CategoryTheory.Thomason.Simplicial.KanFiberComponentTransport
import OAI.CategoryTheory.Thomason.Simplicial.RealizationTopology
import OAI.CategoryTheory.Thomason.Simplicial.SingularKanComplex
import OAI.CategoryTheory.Thomason.Simplicial.SkeletalWeakEquivalences
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

namespace OAI

section

/-! # Stationary contractions and Kan fibres over finite cubes -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The final vertex in every coordinate of the finite simplicial cube. -/
def finalVertex : (n : ℕ) → (obj n) _⦋0⦌
  | 0 => finalSimplexVertex 0
  | n+1 => (finalVertex n, finalSimplexVertex 1)

/-- Simultaneously contract all interval coordinates to their final vertex. -/
def finalContractionMap (n : ℕ) : obj n ⊗ (Δ[1] : SSet.{0}) ⟶ obj n :=
  Nat.rec (motive := fun n => obj n ⊗ (Δ[1] : SSet.{0}) ⟶ obj n)
    (fst _ _) (fun n f => {
      app d := ↾fun z => (f.app d (z.1.1, z.2),
        (simplexFinalContraction 1).h.app d (z.1.2, z.2))
      naturality d e g := by
        apply ConcreteCategory.hom_ext
        intro z
        apply Prod.ext
        · exact congrArg (fun h : (obj n ⊗ (Δ[1] : SSet.{0})).obj d ⟶ (obj n).obj e =>
            h (z.1.1, z.2)) (f.naturality g)
        · exact congrArg (fun h : ((Δ[1] : SSet.{0}) ⊗ Δ[1]).obj d ⟶
            (Δ[1] : SSet.{0}).obj e => h (z.1.2, z.2))
              ((simplexFinalContraction 1).h.naturality g) }) n

theorem finalContractionMap_zero (n : ℕ) :
    SSet.ι₀ ≫ finalContractionMap n = 𝟙 (obj n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · exact congrArg (fun f : obj n ⟶ obj n => f.app d z.1) ih
    · exact congrArg (fun f : (Δ[1] : SSet.{0}) ⟶ Δ[1] => f.app d z.2)
        (simplexFinalContraction 1).h₀

theorem finalContractionMap_one (n : ℕ) :
    SSet.ι₁ ≫ finalContractionMap n = SSet.const (finalVertex n) := by
  induction n with
  | zero =>
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  | succ n ih =>
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · exact congrArg (fun f : obj n ⟶ obj n => f.app d z.1) ih
    · exact congrArg (fun f : (Δ[1] : SSet.{0}) ⟶ Δ[1] => f.app d z.2)
        (simplexFinalContraction 1).h₁

/-- The simultaneous contraction is an actual simplicial homotopy. -/
def finalContraction (n : ℕ) : SSet.Homotopy (𝟙 (obj n)) (SSet.const (finalVertex n)) where
  h := finalContractionMap n
  h₀ := finalContractionMap_zero n
  h₁ := finalContractionMap_one n
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- The entire constant family at the final vertex stays fixed. -/
theorem finalContraction_stationary (n : ℕ) (K : SSet.{0}) :
    (SSet.const (X := K) (finalVertex n)) ▷ Δ[1] ≫ (finalContraction n).h =
      fst K Δ[1] ≫ SSet.const (finalVertex n) := by
  induction n with
  | zero =>
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  | succ n ih =>
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · exact congrArg (fun f : K ⊗ (Δ[1] : SSet.{0}) ⟶ obj n => f.app d z) ih
    · exact congrArg (fun f : K ⊗ (Δ[1] : SSet.{0}) ⟶ Δ[1] => f.app d z)
        (simplexFinalContraction_stationary 1 K)

/-- Every Kan fibration over a finite simplicial cube retracts, by a
stationary simplicial homotopy, onto its final-vertex fibre. -/
theorem kan_final_fiber_deformation {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ obj n) [HomotopicalAlgebra.Fibration p] :
    ∃ r : E ⟶ (simplicialPointFiber p (finalVertex n)).toSSet,
      (simplicialPointFiber p (finalVertex n)).ι ≫ r = 𝟙 _ ∧
      ∃ T : SSet.Homotopy (𝟙 E) (r ≫ (simplicialPointFiber p (finalVertex n)).ι),
        (simplicialPointFiber p (finalVertex n)).ι ▷ Δ[1] ≫ T.h =
          fst (simplicialPointFiber p (finalVertex n)).toSSet Δ[1] ≫
            (simplicialPointFiber p (finalVertex n)).ι ∧
        T.h ≫ p = p ▷ Δ[1] ≫ (finalContraction n).h := by
  apply kan_fiber_deformation p _ (finalContraction n)
  rw [simplicialPointFiber_ι_comp]
  exact finalContraction_stationary n _

/-- The final fibre includes by an actual realization weak equivalence. -/
theorem kan_final_fiber_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ obj n) [HomotopicalAlgebra.Fibration p] :
    realizationWeakEquivalences (simplicialPointFiber p (finalVertex n)).ι := by
  obtain ⟨r, hr, T, _, _⟩ := kan_final_fiber_deformation n p
  exact simplicial_retraction_weak _ r hr T

/-- Every vertex fibre of a Kan fibration over a cube includes weakly.
The already proved realization component comparison transports the final
fibre result to all vertices, without a global fibre-preservation premise. -/
theorem kan_any_fiber_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ obj n) [HomotopicalAlgebra.Fibration p] (b : (obj n) _⦋0⦌) :
    realizationWeakEquivalences (simplicialPointFiber p b).ι := by
  let x := RealizationPrism.vertexPoint (obj n) b
  let y := RealizationPrism.vertexPoint (obj n) (finalVertex n)
  let H := RealizedCylinder.homotopy (finalContraction n)
  have h : Path x y := {
    toFun t := H (t, x)
    continuous_toFun := by fun_prop
    source' := by
      rw [H.apply_zero]
      exact congrArg (fun f => f.hom x) (SSet.toTop.map_id (obj n))
    target' := by
      rw [H.apply_one]
      exact RealizationPrism.realization_const (finalVertex n) x }
  exact (kan_fiber_weak_iff_of_realization_path p h).mpr
    (kan_final_fiber_weak n p)

end

end Thomason.Construction.RealizedCube

end

section

/-! # Actual weak simplicial transport maps between the ends of a base edge -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The final contraction on the interval, started at zero, is the original
interval parameter, in every simplicial degree. -/
theorem simplexFinalContraction_initial (K : SSet.{0}) :
    (SSet.const (X := K) (initialSimplexVertex 1)) ▷ Δ[1] ≫
      (simplexFinalContraction 1).h = snd K (Δ[1] : SSet.{0}) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro j
  change (if (SSet.stdSimplex.objEquiv z.2).toOrderHom j = 0 then (0 : Fin 2)
    else 1) = (SSet.stdSimplex.objEquiv z.2).toOrderHom j
  generalize (SSet.stdSimplex.objEquiv z.2).toOrderHom j = v
  fin_cases v <;> decide

/-- A Kan fibration transports its initial fibre to its final fibre along
any base edge by an actual simplicial weak equivalence. The transporting
homotopy projects exactly onto that edge, with the same interval parameter. -/
theorem kan_interval_fiber_transport {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (g : (Δ[1] : SSet.{0}) ⟶ B) :
    ∃ t : (simplicialPointFiber p (g.app _ (initialSimplexVertex 1))).toSSet ⟶
        (simplicialPointFiber p (g.app _ (finalSimplexVertex 1))).toSSet,
      realizationWeakEquivalences t ∧
      ∃ H : SSet.Homotopy (simplicialPointFiber p (g.app _ (initialSimplexVertex 1))).ι
          (t ≫ (simplicialPointFiber p (g.app _ (finalSimplexVertex 1))).ι),
        H.h ≫ p = snd _ (Δ[1] : SSet.{0}) ≫ g := by
  let q := pullback.snd p g
  have : HomotopicalAlgebra.Fibration q := kan_pullback_snd_fibration p g
  let F₀ := simplicialPointFiber p (g.app _ (initialSimplexVertex 1))
  let F₁ := simplicialPointFiber p (g.app _ (finalSimplexVertex 1))
  let V := simplicialPointFiber q (finalSimplexVertex 1)
  let j₀ := pointFiberToPullback p g (initialSimplexVertex 1)
  let e := simplicialPointFiberBaseChangeIso p g (finalSimplexVertex 1)
  obtain ⟨r, _, T, _, hT⟩ := kan_simplex_fiber_deformation 1 q
  have hr : realizationWeakEquivalences r := by
    apply realizationWeakEquivalences.of_postcomp r V.ι (kan_simplex_fiber_weak 1 q)
    exact (RealizedCylinder.weakEquivalence_iff T).mp (realizationWeakEquivalences.id_mem _)
  let t : F₀.toSSet ⟶ F₁.toSSet := j₀ ≫ r ≫ e.inv
  have ht : realizationWeakEquivalences t :=
    realizationWeakEquivalences.comp_mem _ _
      (kan_simplex_baseChange_initialFiber_weak p 1 g)
      (realizationWeakEquivalences.comp_mem _ _ hr (realizationWeakEquivalences.of_isIso _))
  have he : V.ι ≫ pullback.fst p g = e.inv ≫ F₁.ι := rfl
  let H : SSet.Homotopy F₀.ι (t ≫ F₁.ι) := {
    h := j₀ ▷ Δ[1] ≫ T.h ≫ pullback.fst p g
    h₀ := by
      have hn : SSet.ι₀ ≫ j₀ ▷ (Δ[1] : SSet.{0}) = j₀ ≫ SSet.ι₀ := by
        apply NatTrans.ext
        funext d
        apply ConcreteCategory.hom_ext
        intro z
        rfl
      rw [← Category.assoc, hn, Category.assoc, ← Category.assoc SSet.ι₀,
        T.h₀, Category.id_comp, pointFiberToPullback_fst]
      rfl
    h₁ := by
      have hn : SSet.ι₁ ≫ j₀ ▷ (Δ[1] : SSet.{0}) = j₀ ≫ SSet.ι₁ := by
        apply NatTrans.ext
        funext d
        apply ConcreteCategory.hom_ext
        intro z
        rfl
      rw [← Category.assoc, hn, Category.assoc, ← Category.assoc SSet.ι₁,
        T.h₁, Category.assoc r, he]
      rfl
    rel := by
      apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  refine ⟨t, ht, H, ?_⟩
  change (j₀ ▷ Δ[1] ≫ T.h ≫ pullback.fst p g) ≫ p = _
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc T.h,
    hT, ← Category.assoc (j₀ ▷ Δ[1]), ← comp_whiskerRight_assoc,
    pointFiberToPullback_snd, simplexFinalContraction_initial]

end

end Thomason.Construction

end

section

/-! # Every simplex restriction of a Kan fibration is an actual weak equivalence -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

noncomputable section

/-- The canonical restriction map on total spaces above a simplex map. -/
def kanSimplexRestriction {E B : SSet.{0}} (p : E ⟶ B) {n m : SimplexCategory}
    (b : SSet.stdSimplex.obj n ⟶ B) (f : m ⟶ n) :
    pullback p (SSet.stdSimplex.map f ≫ b) ⟶ pullback p b :=
  (pullbackLeftPullbackSndIso p b (SSet.stdSimplex.map f)).inv ≫
    pullback.fst (pullback.snd p b) (SSet.stdSimplex.map f)

@[reassoc]
theorem kanSimplexRestriction_fst {E B : SSet.{0}} (p : E ⟶ B) {n m : SimplexCategory}
    (b : SSet.stdSimplex.obj n ⟶ B) (f : m ⟶ n) :
    kanSimplexRestriction p b f ≫ pullback.fst p b =
      pullback.fst p (SSet.stdSimplex.map f ≫ b) := by
  rw [kanSimplexRestriction, Category.assoc, pullbackLeftPullbackSndIso_inv_fst]

@[reassoc]
theorem kanSimplexRestriction_snd {E B : SSet.{0}} (p : E ⟶ B) {n m : SimplexCategory}
    (b : SSet.stdSimplex.obj n ⟶ B) (f : m ⟶ n) :
    kanSimplexRestriction p b f ≫ pullback.snd p b =
      pullback.snd p (SSet.stdSimplex.map f ≫ b) ≫ SSet.stdSimplex.map f := by
  rw [kanSimplexRestriction, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd]

/-- For an arbitrary Kan fibration, every simplex restriction is a weak
homotopy equivalence on the actual realization of its pullback total spaces.
Both face and degeneracy maps are included. -/
theorem kanSimplexRestriction_weak {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] {n m : SimplexCategory}
    (b : SSet.stdSimplex.obj n ⟶ B) (f : m ⟶ n) :
    realizationWeakEquivalences (kanSimplexRestriction p b f) := by
  have : HomotopicalAlgebra.Fibration (pullback.snd p b) := kan_pullback_snd_fibration p b
  apply realizationWeakEquivalences.comp_mem
  · exact realizationWeakEquivalences.of_isIso _
  · exact kan_simplex_baseChange_weak n.len m.len (pullback.snd p b) (SSet.stdSimplex.map f)

end

end Thomason.Construction

end

section

/-! # Pulling back a horn along an arbitrary Kan fibration is weak -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The distinguished-vertex fibre of a Kan fibration over a horn is weakly
 equivalent to its total space. Both homotopies fix that entire fibre. -/
theorem kan_horn_fiber_weak {E : SSet.{0}} (n : ℕ) (i : Fin (n+2))
    (p : E ⟶ (Λ[n+1, i] : SSet.{0})) [HomotopicalAlgebra.Fibration p] :
    realizationWeakEquivalences (simplicialPointFiber p (hornVertex n i)).ι :=
  kan_fiber_weak_of_zigzag p (hornVertex n i) (hornClamp n i)
    (hornClampToId n i) (hornClampToVertex n i)
    (hornClampToId_stationary n i) (hornClampToVertex_stationary n i)

/-- For a Kan fibration over a standard simplex, the preimage of each horn
 includes by an actual realization weak equivalence. This is proved directly
 from local fibre contractions, without acyclic-Kan lifting or right properness. -/
theorem kan_horn_baseChange_weak {E : SSet.{0}} (n : ℕ) (i : Fin (n+2))
    (p : E ⟶ (Δ[n+1] : SSet.{0})) [HomotopicalAlgebra.Fibration p] :
    realizationWeakEquivalences (pullback.fst p (Λ[n+1, i] : SSet.Subcomplex _).ι) := by
  let j := (Λ[n+1, i] : SSet.Subcomplex (Δ[n+1] : SSet.{0})).ι
  let q := pullback.snd p j
  have : HomotopicalAlgebra.Fibration q := kan_pullback_snd_fibration p j
  have hf : realizationWeakEquivalences (pointFiberToPullback p j (hornVertex n i)) := by
    rw [← simplicialPointFiberBaseChangeIso_hom_ι]
    exact realizationWeakEquivalences.comp_mem _ _
      (realizationWeakEquivalences.of_isIso _) (kan_horn_fiber_weak n i q)
  apply realizationWeakEquivalences.of_precomp (pointFiberToPullback p j (hornVertex n i)) _ hf
  rw [pointFiberToPullback_fst]
  exact kan_simplex_anyFiber_weak (n+1) p _

/-- The same comparison in a general base, restricted over a chosen simplex.
 The actual iterated pullback is retained in the statement. -/
theorem kan_simplex_horn_restriction_weak {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (n : ℕ) (i : Fin (n+2))
    (b : (Δ[n+1] : SSet.{0}) ⟶ B) :
    realizationWeakEquivalences
      (pullback.fst (pullback.snd p b) (Λ[n+1, i] : SSet.Subcomplex _).ι) := by
  have : HomotopicalAlgebra.Fibration (pullback.snd p b) := kan_pullback_snd_fibration p b
  exact kan_horn_baseChange_weak n i _

end

end Thomason.Construction

end

section

/-! # The weakly constant diagram of simplex pullbacks -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

noncomputable section

def simplexPullbackMap {E B : SSet.{0}} (p : E ⟶ B) {n m : SimplexCategory}
    (a : SSet.stdSimplex.obj m ⟶ B) (b : SSet.stdSimplex.obj n ⟶ B)
    (f : m ⟶ n) (h : SSet.stdSimplex.map f ≫ b = a) :
    pullback p a ⟶ pullback p b :=
  pullback.lift (pullback.fst p a) (pullback.snd p a ≫ SSet.stdSimplex.map f)
    (by rw [Category.assoc, h, pullback.condition])

@[reassoc]
theorem simplexPullbackMap_fst {E B : SSet.{0}} (p : E ⟶ B) {n m : SimplexCategory}
    (a : SSet.stdSimplex.obj m ⟶ B) (b : SSet.stdSimplex.obj n ⟶ B)
    (f : m ⟶ n) (h : SSet.stdSimplex.map f ≫ b = a) :
    simplexPullbackMap p a b f h ≫ pullback.fst p b = pullback.fst p a :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem simplexPullbackMap_snd {E B : SSet.{0}} (p : E ⟶ B) {n m : SimplexCategory}
    (a : SSet.stdSimplex.obj m ⟶ B) (b : SSet.stdSimplex.obj n ⟶ B)
    (f : m ⟶ n) (h : SSet.stdSimplex.map f ≫ b = a) :
    simplexPullbackMap p a b f h ≫ pullback.snd p b =
      pullback.snd p a ≫ SSet.stdSimplex.map f := pullback.lift_snd _ _ _

theorem simplexPullbackMap_weak {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] {n m : SimplexCategory}
    (a : SSet.stdSimplex.obj m ⟶ B) (b : SSet.stdSimplex.obj n ⟶ B)
    (f : m ⟶ n) (h : SSet.stdSimplex.map f ≫ b = a) :
    realizationWeakEquivalences (simplexPullbackMap p a b f h) := by
  subst a
  have he : simplexPullbackMap p (SSet.stdSimplex.map f ≫ b) b f rfl =
      kanSimplexRestriction p b f := by
    apply pullback.hom_ext
    · rw [simplexPullbackMap_fst, kanSimplexRestriction_fst]
    · rw [simplexPullbackMap_snd, kanSimplexRestriction_snd]
  rw [he]
  exact kanSimplexRestriction_weak p b f

/-- Pull back the original fibration along every simplex of its base,
including degenerate simplices and every ordinal map between them. -/
abbrev simplexPullbackDiagram {E B : SSet.{0}} (p : E ⟶ B) :
    CostructuredArrow SSet.stdSimplex B ⥤ SSet.{0} where
  obj s := pullback p s.hom
  map {s t} f := simplexPullbackMap p s.hom t.hom f.left f.w
  map_id s := by
    apply pullback.hom_ext
    · simp only [simplexPullbackMap_fst, Category.id_comp]
    · rw [simplexPullbackMap_snd, Category.id_comp]
      change pullback.snd p s.hom ≫ SSet.stdSimplex.map (𝟙 s.left) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
  map_comp f g := by
    apply pullback.hom_ext
    · simp only [Category.assoc, simplexPullbackMap_fst]
    · simp only [Category.assoc, simplexPullbackMap_snd]
      rw [← Category.assoc, simplexPullbackMap_snd, Category.assoc]
      change pullback.snd p _ ≫ SSet.stdSimplex.map (f.left ≫ g.left) = _
      rw [SSet.stdSimplex.map_comp]

/-- The canonical cocone is compatible with the original total space. -/
def simplexPullbackCocone {E B : SSet.{0}} (p : E ⟶ B) :
    Cocone (simplexPullbackDiagram p) where
  pt := E
  ι := {
    app s := pullback.fst p s.hom
    naturality s t f := by
      change simplexPullbackMap p s.hom t.hom f.left f.w ≫ pullback.fst p t.hom = pullback.fst p s.hom ≫ 𝟙 E
      rw [simplexPullbackMap_fst, Category.comp_id] }

/-- Every arrow in this actual pullback diagram is a realization weak
 equivalence. No homotopy-colimit or global fibre theorem is assumed. -/
theorem simplexPullbackDiagram_map_weak {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] {s t : CostructuredArrow SSet.stdSimplex B}
    (f : s ⟶ t) : realizationWeakEquivalences ((simplexPullbackDiagram p).map f) :=
  simplexPullbackMap_weak p s.hom t.hom f.left f.w

end

end Thomason.Construction

end

section

/-! # A Kan fibration over a simplex is fibrewise homotopy trivial -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The initial-vertex inclusion with an arbitrary simplicial parameter. -/
def productInitialVertex (K : SSet.{0}) (n : ℕ) : K ⟶ K ⊗ (Δ[n] : SSet.{0}) :=
  lift (𝟙 K) (SSet.const (initialSimplexVertex n))

/-- The entire parameterized initial face is anodyne. -/
theorem productInitialVertex_anodyne (K : SSet.{0}) (n : ℕ) :
    SSet.anodyneExtensions (productInitialVertex K n) := by
  have he : productInitialVertex K n =
      (ρ_ K).inv ≫ K ◁ (unitZeroIso.hom ≫ initialVertexInclusion n) := by
    apply NatTrans.ext
    funext j
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [he]
  exact SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
    ((SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
      (initialVertexInclusion_anodyne n)).whiskerLeft K)

/-- An actual fibrewise homotopy trivialization over a standard simplex.
Both homotopies project to the constant base homotopy, and both maps retain
the entire initial fibre exactly. No acyclic lifting or realization
preservation of pullbacks is assumed. -/
theorem kan_simplex_fibrewise_trivialization {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p] :
    ∃ (q : E ⟶ (simplicialPointFiber p (initialSimplexVertex n)).toSSet ⊗ (Δ[n] : SSet.{0}))
      (s : (simplicialPointFiber p (initialSimplexVertex n)).toSSet ⊗ (Δ[n] : SSet.{0}) ⟶ E),
      q ≫ snd _ _ = p ∧ s ≫ p = snd _ _ ∧
      (simplicialPointFiber p (initialSimplexVertex n)).ι ≫ q = productInitialVertex _ n ∧
      productInitialVertex _ n ≫ s = (simplicialPointFiber p (initialSimplexVertex n)).ι ∧
      ∃ (H : SSet.Homotopy (𝟙 E) (q ≫ s))
        (T : SSet.Homotopy (𝟙 _) (s ≫ q)),
        H.h ≫ p = fst E Δ[1] ≫ p ∧
        T.h ≫ snd _ _ = fst _ Δ[1] ≫ snd _ _ := by
  let F := simplicialPointFiber p (initialSimplexVertex n)
  have : SSet.KanComplex F.toSSet := simplicialPointFiber_kan p _
  have hstat : (F.ι ≫ p) ▷ Δ[1] ≫ (simplexInitialContraction n).h =
      fst F.toSSet Δ[1] ≫ F.ι ≫ p := by
    rw [simplicialPointFiber_ι_comp]
    exact simplexInitialContraction_const n _
  obtain ⟨r, hr, _, _, _⟩ :=
    kan_fiber_deformation_reverse p _ (simplexInitialContraction n) hstat
  let q : E ⟶ F.toSSet ⊗ (Δ[n] : SSet.{0}) := lift r p
  let j := productInitialVertex F.toSSet n
  have hj : SSet.anodyneExtensions j := productInitialVertex_anodyne _ n
  have : HasLiftingProperty j p := hj _ ((fibration_iff p).mp inferInstance)
  let sq : CommSq F.ι j p (snd F.toSSet (Δ[n] : SSet.{0})) := ⟨by
    rw [simplicialPointFiber_ι_comp]
    exact (lift_snd _ _).symm⟩
  let s := sq.lift
  have hs : s ≫ p = snd F.toSSet (Δ[n] : SSet.{0}) := sq.fac_right
  have hjs : j ≫ s = F.ι := sq.fac_left
  have hq : q ≫ snd F.toSSet (Δ[n] : SSet.{0}) = p := lift_snd _ _
  have hiq : F.ι ≫ q = j := by
    apply hom_ext
    · dsimp only [q, j, productInitialVertex]
      rw [Category.assoc, lift_fst, hr, lift_fst]
    · dsimp only [q, j, productInitialVertex]
      rw [Category.assoc, lift_snd, simplicialPointFiber_ι_comp, lift_snd]
  obtain ⟨H, hH, _⟩ := kan_lifts_homotopic_relative F.ι
    (kan_simplex_initialFiber_anodyne n p) p (𝟙 E) (q ≫ s)
    (by rw [Category.id_comp, Category.assoc, hs, hq])
    (by rw [Category.comp_id, ← Category.assoc, hiq, hjs])
  have : HomotopicalAlgebra.Fibration (snd F.toSSet (Δ[n] : SSet.{0})) :=
    kan_product_snd_fibration _ _
  obtain ⟨T, hT, _⟩ := kan_lifts_homotopic_relative j hj
    (snd F.toSSet (Δ[n] : SSet.{0})) (𝟙 _) (s ≫ q)
    (by rw [Category.id_comp, Category.assoc, hq, hs])
    (by rw [Category.comp_id, ← Category.assoc, hjs, hiq])
  exact ⟨q, s, hq, hs, hiq, hjs, H, T,
    by simpa only [Category.id_comp] using hH,
    by simpa only [Category.id_comp] using hT⟩

/-- The fibrewise trivialization maps are actual realization weak
 equivalences, while still commuting exactly with the base projection. -/
theorem kan_simplex_trivialization_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p] :
    ∃ (q : E ⟶ (simplicialPointFiber p (initialSimplexVertex n)).toSSet ⊗ (Δ[n] : SSet.{0}))
      (s : (simplicialPointFiber p (initialSimplexVertex n)).toSSet ⊗ (Δ[n] : SSet.{0}) ⟶ E),
      realizationWeakEquivalences q ∧ realizationWeakEquivalences s ∧
      q ≫ snd _ _ = p ∧ s ≫ p = snd _ _ := by
  obtain ⟨q, s, hq, hs, _, _, H, T, _, _⟩ := kan_simplex_fibrewise_trivialization n p
  obtain ⟨hqW, hsW⟩ := simplicial_homotopy_inverse_weak_pair q s H T
  exact ⟨q, s, hqW, hsW, hq, hs⟩

end

end Thomason.Construction

end

section

/-! # Fibrewise Kan trivialization over an explicitly contracted base -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- A chosen vertex as a map from the terminal standard simplex. -/
def contractedVertexInclusion {B : SSet.{0}} (b : B _⦋0⦌) : (Δ[0] : SSet.{0}) ⟶ B :=
  SSet.const b

/-- The product inclusion of that same chosen vertex. -/
def productChosenVertex {B : SSet.{0}} (K : SSet.{0}) (b : B _⦋0⦌) : K ⟶ K ⊗ B :=
  lift (𝟙 K) (SSet.const b)

/-- An explicit stationary reverse contraction makes the vertex inclusion
anodyne by relative cylinder lifting. -/
theorem contractedVertexInclusion_anodyne {B : SSet.{0}} (b : B _⦋0⦌)
    (C : SSet.Homotopy (SSet.const b) (𝟙 B))
    (hC : ∀ K : SSet.{0}, (SSet.const (X := K) b) ▷ Δ[1] ≫ C.h =
      fst K Δ[1] ≫ SSet.const b) : SSet.anodyneExtensions (contractedVertexInclusion b) := by
  let i := contractedVertexInclusion b
  have : Mono i := by
    rw [NatTrans.mono_iff_mono_app]
    intro d
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro x y _
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro k
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  let r : B ⟶ (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from B
  have hir : i ≫ r = 𝟙 _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  let H : SSet.Homotopy (r ≫ i) (𝟙 B) := {
    h := C.h
    h₀ := by
      change SSet.ι₀ ≫ C.h = r ≫ i
      simpa only [i, contractedVertexInclusion, SSet.comp_const] using C.h₀
    h₁ := C.h₁
    rel := by
      apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property }
  exact anodyne_of_simplicial_deformation i r hir H (hC (Δ[0] : SSet.{0}))

theorem productChosenVertex_anodyne {B : SSet.{0}} (K : SSet.{0}) (b : B _⦋0⦌)
    (C : SSet.Homotopy (SSet.const b) (𝟙 B))
    (hC : ∀ L : SSet.{0}, (SSet.const (X := L) b) ▷ Δ[1] ≫ C.h =
      fst L Δ[1] ≫ SSet.const b) : SSet.anodyneExtensions (productChosenVertex K b) := by
  have he : productChosenVertex K b =
      (ρ_ K).inv ≫ K ◁ (unitZeroIso.hom ≫ contractedVertexInclusion b) := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [he]
  exact SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
    ((SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
      (contractedVertexInclusion_anodyne b C hC)).whiskerLeft K)

/-- The same explicit contraction yields a fibrewise homotopy trivialization
of every Kan fibration over that base. The hypotheses specify actual maps
and their stationary equation, not a weak or lifting conclusion. -/
theorem kan_contracted_base_trivialization {E B : SSet.{0}} (b : B _⦋0⦌)
    (C : SSet.Homotopy (SSet.const b) (𝟙 B))
    (hC : ∀ L : SSet.{0}, (SSet.const (X := L) b) ▷ Δ[1] ≫ C.h =
      fst L Δ[1] ≫ SSet.const b)
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p] :
    ∃ (q : E ⟶ (simplicialPointFiber p b).toSSet ⊗ B)
      (s : (simplicialPointFiber p b).toSSet ⊗ B ⟶ E),
      q ≫ snd _ _ = p ∧ s ≫ p = snd _ _ ∧
      (simplicialPointFiber p b).ι ≫ q = productChosenVertex _ b ∧
      productChosenVertex _ b ≫ s = (simplicialPointFiber p b).ι ∧
      ∃ (H : SSet.Homotopy (𝟙 E) (q ≫ s))
        (T : SSet.Homotopy (𝟙 _) (s ≫ q)),
        H.h ≫ p = fst E Δ[1] ≫ p ∧
        T.h ≫ snd _ _ = fst _ Δ[1] ≫ snd _ _ := by
  let F := simplicialPointFiber p b
  have : SSet.KanComplex F.toSSet := simplicialPointFiber_kan p b
  have hstat : (F.ι ≫ p) ▷ Δ[1] ≫ C.h = fst F.toSSet Δ[1] ≫ F.ι ≫ p := by
    rw [simplicialPointFiber_ι_comp]
    exact hC _
  obtain ⟨r, hr, D, hD, _⟩ := kan_fiber_deformation_reverse p b C hstat
  have hF : SSet.anodyneExtensions F.ι := anodyne_of_simplicial_deformation F.ι r hr D hD
  let q : E ⟶ F.toSSet ⊗ B := lift r p
  let j := productChosenVertex F.toSSet b
  have hj : SSet.anodyneExtensions j := productChosenVertex_anodyne _ b C hC
  have : HasLiftingProperty j p := hj _ ((fibration_iff p).mp inferInstance)
  let sq : CommSq F.ι j p (snd F.toSSet B) := ⟨by
    rw [simplicialPointFiber_ι_comp]
    exact (lift_snd _ _).symm⟩
  let s := sq.lift
  have hs : s ≫ p = snd F.toSSet B := sq.fac_right
  have hjs : j ≫ s = F.ι := sq.fac_left
  have hq : q ≫ snd F.toSSet B = p := lift_snd _ _
  have hiq : F.ι ≫ q = j := by
    apply hom_ext
    · dsimp only [q, j, productChosenVertex]
      rw [Category.assoc, lift_fst, hr, lift_fst]
    · dsimp only [q, j, productChosenVertex]
      rw [Category.assoc, lift_snd, simplicialPointFiber_ι_comp, lift_snd]
  obtain ⟨H, hH, _⟩ := kan_lifts_homotopic_relative F.ι hF p (𝟙 E) (q ≫ s)
    (by rw [Category.id_comp, Category.assoc, hs, hq])
    (by rw [Category.comp_id, ← Category.assoc, hiq, hjs])
  have : HomotopicalAlgebra.Fibration (snd F.toSSet B) := kan_product_snd_fibration _ _
  obtain ⟨T, hT, _⟩ := kan_lifts_homotopic_relative j hj (snd F.toSSet B) (𝟙 _) (s ≫ q)
    (by rw [Category.id_comp, Category.assoc, hq, hs])
    (by rw [Category.comp_id, ← Category.assoc, hjs, hiq])
  exact ⟨q, s, hq, hs, hiq, hjs, H, T,
    by simpa only [Category.id_comp] using hH,
    by simpa only [Category.id_comp] using hT⟩

end

end Thomason.Construction

end

section

/-! # Stationary contractions and Kan fibres over finite cubes -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The initial vertex in every coordinate of the finite simplicial cube. -/
def initialVertex : (n : ℕ) → (obj n) _⦋0⦌
  | 0 => initialSimplexVertex 0
  | n+1 => (initialVertex n, initialSimplexVertex 1)

/-- Simultaneously expand all interval coordinates from the initial vertex. -/
def initialContractionMap (n : ℕ) : obj n ⊗ (Δ[1] : SSet.{0}) ⟶ obj n :=
  Nat.rec (motive := fun n => obj n ⊗ (Δ[1] : SSet.{0}) ⟶ obj n)
    (fst _ _) (fun n f => {
      app d := ↾fun z => (f.app d (z.1.1, z.2),
        (simplexInitialContraction 1).h.app d (z.1.2, z.2))
      naturality d e g := by
        apply ConcreteCategory.hom_ext
        intro z
        apply Prod.ext
        · exact congrArg (fun h : (obj n ⊗ (Δ[1] : SSet.{0})).obj d ⟶ (obj n).obj e =>
            h (z.1.1, z.2)) (f.naturality g)
        · exact congrArg (fun h : ((Δ[1] : SSet.{0}) ⊗ Δ[1]).obj d ⟶
            (Δ[1] : SSet.{0}).obj e => h (z.1.2, z.2))
              ((simplexInitialContraction 1).h.naturality g) }) n

theorem initialContractionMap_one (n : ℕ) :
    SSet.ι₁ ≫ initialContractionMap n = 𝟙 (obj n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · exact congrArg (fun f : obj n ⟶ obj n => f.app d z.1) ih
    · exact congrArg (fun f : (Δ[1] : SSet.{0}) ⟶ Δ[1] => f.app d z.2)
        (simplexInitialContraction 1).h₁

theorem initialContractionMap_zero (n : ℕ) :
    SSet.ι₀ ≫ initialContractionMap n = SSet.const (initialVertex n) := by
  induction n with
  | zero =>
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  | succ n ih =>
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · exact congrArg (fun f : obj n ⟶ obj n => f.app d z.1) ih
    · exact congrArg (fun f : (Δ[1] : SSet.{0}) ⟶ Δ[1] => f.app d z.2)
        (simplexInitialContraction 1).h₀

/-- The simultaneous contraction is an actual simplicial homotopy. -/
def initialContraction (n : ℕ) : SSet.Homotopy (SSet.const (initialVertex n)) (𝟙 (obj n)) where
  h := initialContractionMap n
  h₀ := initialContractionMap_zero n
  h₁ := initialContractionMap_one n
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- The entire constant family at the initial vertex stays fixed. -/
theorem initialContraction_stationary (n : ℕ) (K : SSet.{0}) :
    (SSet.const (X := K) (initialVertex n)) ▷ Δ[1] ≫ (initialContraction n).h =
      fst K Δ[1] ≫ SSet.const (initialVertex n) := by
  induction n with
  | zero =>
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  | succ n ih =>
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · exact congrArg (fun f : K ⊗ (Δ[1] : SSet.{0}) ⟶ obj n => f.app d z) ih
    · exact congrArg (fun f : K ⊗ (Δ[1] : SSet.{0}) ⟶ Δ[1] => f.app d z)
        (simplexInitialContraction_const 1 K)


end

end Thomason.Construction.RealizedCube

end

section

/-! # Parametric fibre comparison after arbitrary simplex base change -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Pulling back a product projection gives the actual product over the
new base. All maps are canonical and preserve the new base coordinate. -/
def productBaseChangeIso (F : SSet.{0}) {A B : SSet.{0}} (g : A ⟶ B) :
    pullback (snd F B) g ≅ F ⊗ A where
  hom := lift (pullback.fst (snd F B) g ≫ fst F B) (pullback.snd (snd F B) g)
  inv := pullback.lift (lift (fst F A) (snd F A ≫ g)) (snd F A) (by rw [lift_snd])
  hom_inv_id := by
    apply pullback.hom_ext
    · apply hom_ext
      · simp only [Category.assoc, pullback.lift_fst, lift_fst, Category.id_comp]
      · simp only [Category.assoc, pullback.lift_fst, lift_snd, Category.id_comp]
        exact (pullback.condition (f := snd F B) (g := g)).symm
    · simp only [Category.assoc, pullback.lift_snd, lift_snd, Category.id_comp]
  inv_hom_id := by
    apply hom_ext
    · simp only [Category.assoc, lift_fst, pullback.lift_fst_assoc, Category.id_comp]
    · simp only [Category.assoc, lift_snd, pullback.lift_snd, Category.id_comp]

@[reassoc] theorem productBaseChangeIso_hom_snd (F : SSet.{0}) {A B : SSet.{0}} (g : A ⟶ B) :
    (productBaseChangeIso F g).hom ≫ snd F A = pullback.snd (snd F B) g :=
  lift_snd _ _

/-- For a Kan fibration over a simplex, restriction along ANY simplicial
map into that simplex is weakly equivalent, over its actual new base,
to the product with the initial fibre. This is not a claim that arbitrary
base change preserves all weak equivalences. -/
theorem kan_simplex_arbitrary_baseChange_product {E A : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (g : A ⟶ (Δ[n] : SSet.{0})) :
    ∃ t : pullback p g ⟶ (simplicialPointFiber p (initialSimplexVertex n)).toSSet ⊗ A,
      realizationWeakEquivalences t ∧ t ≫ snd _ A = pullback.snd p g := by
  obtain ⟨q, s, hq, hs, _, _, H, T, hH, hT⟩ := kan_simplex_fibrewise_trivialization n p
  let F := (simplicialPointFiber p (initialSimplexVertex n)).toSSet
  have hw := (overBaseChange_homotopy_inverse_weak p (snd F (Δ[n] : SSet.{0}))
    g q s hq hs H T hH hT).1
  let t := overBaseChangeMap p (snd F (Δ[n] : SSet.{0})) g q hq ≫
    (productBaseChangeIso F g).hom
  refine ⟨t, realizationWeakEquivalences.comp_mem _ _ hw
    (realizationWeakEquivalences.of_isIso _), ?_⟩
  dsimp only [t]
  rw [Category.assoc, productBaseChangeIso_hom_snd, overBaseChangeMap_snd]

end

end Thomason.Construction

end

section

/-! # Relative Kan lifting of higher simplex families with finite carriers -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Whiskering the initial vertex is the actual product initial face. -/
@[reassoc] theorem whisker_initialSimplexVertex (K : SSet.{0}) (n : ℕ) :
    K ◁ initialVertexInclusion n = fst K (Δ[0] : SSet.{0}) ≫ productInitialVertex K n := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- A Kan fibration lifts a family parameterized by an arbitrary standard
simplex, retaining its initial value and its entire prescribed subfamily.
This is the exact higher-parameter version of relative cylinder lifting. -/
theorem exists_kan_simplex_family_lift {A K E B : SSet.{0}}
    (i : A ⟶ K) [Mono i] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (n : ℕ) (f : K ⟶ E) (h : A ⊗ (Δ[n] : SSet.{0}) ⟶ E)
    (b : K ⊗ (Δ[n] : SSet.{0}) ⟶ B)
    (h₀ : productInitialVertex A n ≫ h = i ≫ f)
    (hb : h ≫ p = i ▷ (Δ[n] : SSet.{0}) ≫ b)
    (hf : f ≫ p = productInitialVertex K n ≫ b) :
    ∃ e : K ⊗ (Δ[n] : SSet.{0}) ⟶ E,
      productInitialVertex K n ≫ e = f ∧
      i ▷ (Δ[n] : SSet.{0}) ≫ e = h ∧ e ≫ p = b := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i (initialVertexInclusion n)
  have hc : i ▷ (Δ[0] : SSet.{0}) ≫ fst K (Δ[0] : SSet.{0}) ≫ f =
      A ◁ initialVertexInclusion n ≫ h := by
    rw [whisker_initialSimplexVertex, Category.assoc, h₀]
    rw [← Category.assoc, whiskerRight_fst, Category.assoc]
  let g : sq.pt ⟶ E := sq.isPushout.desc (fst K (Δ[0] : SSet.{0}) ≫ f) h hc
  have gl : sq.inl ≫ g = fst K (Δ[0] : SSet.{0}) ≫ f := sq.isPushout.inl_desc _ _ _
  have gr : sq.inr ≫ g = h := sq.isPushout.inr_desc _ _ _
  have il : sq.inl ≫ sq.ι = K ◁ initialVertexInclusion n := sq.inl_ι
  have ir : sq.inr ≫ sq.ι = i ▷ (Δ[n] : SSet.{0}) := sq.inr_ι
  have hg : g ≫ p = sq.ι ≫ b := by
    apply sq.hom_ext
    · rw [← Category.assoc, gl, Category.assoc, hf]
      rw [← Category.assoc sq.inl sq.ι b, il, whisker_initialSimplexVertex, Category.assoc]
    · rw [← Category.assoc, gr, hb, ← Category.assoc, ir]
  have ha : SSet.anodyneExtensions sq.ι :=
    SSet.anodyneExtensions_pushoutObjObjι sq (initialVertexInclusion_anodyne n)
  have : HasLiftingProperty sq.ι p := ha _ ((fibration_iff p).mp inferInstance)
  let c : CommSq g sq.ι p b := ⟨hg⟩
  refine ⟨c.lift, ?_, ?_, c.fac_right⟩
  · have he : K ◁ initialVertexInclusion n ≫ c.lift = fst K (Δ[0] : SSet.{0}) ≫ f := by
      rw [← il, Category.assoc, c.fac_left, gl]
    have hz := congrArg (fun q => zeroFaceSection K ≫ q) he
    simpa only [whisker_initialSimplexVertex, ← Category.assoc,
      zeroFaceSection_fst, Category.id_comp] using hz
  · rw [← ir, Category.assoc, c.fac_left, gr]

/-- With finite source, the entire exact higher family and its two given
faces live in a single finite subcomplex of the original total space. -/
theorem finite_kan_simplex_family_lift {A K E B : SSet.{0}} [K.Finite]
    (i : A ⟶ K) [Mono i] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (n : ℕ) (f : K ⟶ E) (h : A ⊗ (Δ[n] : SSet.{0}) ⟶ E)
    (b : K ⊗ (Δ[n] : SSet.{0}) ⟶ B)
    (h₀ : productInitialVertex A n ≫ h = i ≫ f)
    (hb : h ≫ p = i ▷ (Δ[n] : SSet.{0}) ≫ b)
    (hf : f ≫ p = productInitialVertex K n ≫ b) :
    ∃ (S : E.Subcomplex) (_ : SSet.Finite S.toSSet)
      (eS : K ⊗ (Δ[n] : SSet.{0}) ⟶ S.toSSet)
      (fS : K ⟶ S.toSSet) (hS : A ⊗ (Δ[n] : SSet.{0}) ⟶ S.toSSet),
      fS ≫ S.ι = f ∧ hS ≫ S.ι = h ∧
      productInitialVertex K n ≫ eS = fS ∧
      i ▷ (Δ[n] : SSet.{0}) ≫ eS = hS ∧ eS ≫ S.ι ≫ p = b := by
  obtain ⟨e, he₀, hei, hep⟩ := exists_kan_simplex_family_lift i p n f h b h₀ hb hf
  let S := SSet.Subcomplex.range e
  let eS := SSet.Subcomplex.toRange e
  let fS := productInitialVertex K n ≫ eS
  let hS := i ▷ (Δ[n] : SSet.{0}) ≫ eS
  refine ⟨S, inferInstance, eS, fS, hS, ?_, ?_, rfl, rfl, ?_⟩
  · dsimp only [fS]
    rw [Category.assoc, SSet.Subcomplex.toRange_ι, he₀]
  · dsimp only [hS]
    rw [Category.assoc, SSet.Subcomplex.toRange_ι, hei]
  · rw [← Category.assoc, SSet.Subcomplex.toRange_ι, hep]

end

end Thomason.Construction

end

section

/-! # Exact relative Kan lifts with a contracted parameter -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Whiskering the initial vertex is the actual product initial face. -/
@[reassoc] theorem whisker_contractedVertex (K : SSet.{0}) {P : SSet.{0}} (v : P _⦋0⦌) :
    K ◁ contractedVertexInclusion v = fst K (Δ[0] : SSet.{0}) ≫ productChosenVertex K v := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- A Kan fibration lifts a family parameterized by an explicitly contracted
simplicial parameter, retaining its initial value and its entire prescribed subfamily.
This is the exact higher-parameter version of relative cylinder lifting, including finite cube parameters. -/
theorem exists_kan_contracted_family_lift {A K E B : SSet.{0}}
    (i : A ⟶ K) [Mono i] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    {P : SSet.{0}} (v : P _⦋0⦌)
    (C : SSet.Homotopy (SSet.const v) (𝟙 P))
    (hC : ∀ L : SSet.{0}, (SSet.const (X := L) v) ▷ Δ[1] ≫ C.h =
      fst L Δ[1] ≫ SSet.const v)
    (f : K ⟶ E) (h : A ⊗ P ⟶ E)
    (b : K ⊗ P ⟶ B)
    (h₀ : productChosenVertex A v ≫ h = i ≫ f)
    (hb : h ≫ p = i ▷ P ≫ b)
    (hf : f ≫ p = productChosenVertex K v ≫ b) :
    ∃ e : K ⊗ P ⟶ E,
      productChosenVertex K v ≫ e = f ∧
      i ▷ P ≫ e = h ∧ e ≫ p = b := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i (contractedVertexInclusion v)
  have hc : i ▷ (Δ[0] : SSet.{0}) ≫ fst K (Δ[0] : SSet.{0}) ≫ f =
      A ◁ contractedVertexInclusion v ≫ h := by
    rw [whisker_contractedVertex, Category.assoc, h₀]
    rw [← Category.assoc, whiskerRight_fst, Category.assoc]
  let g : sq.pt ⟶ E := sq.isPushout.desc (fst K (Δ[0] : SSet.{0}) ≫ f) h hc
  have gl : sq.inl ≫ g = fst K (Δ[0] : SSet.{0}) ≫ f := sq.isPushout.inl_desc _ _ _
  have gr : sq.inr ≫ g = h := sq.isPushout.inr_desc _ _ _
  have il : sq.inl ≫ sq.ι = K ◁ contractedVertexInclusion v := sq.inl_ι
  have ir : sq.inr ≫ sq.ι = i ▷ P := sq.inr_ι
  have hg : g ≫ p = sq.ι ≫ b := by
    apply sq.hom_ext
    · rw [← Category.assoc, gl, Category.assoc, hf]
      rw [← Category.assoc sq.inl sq.ι b, il, whisker_contractedVertex, Category.assoc]
    · rw [← Category.assoc, gr, hb, ← Category.assoc, ir]
  have ha : SSet.anodyneExtensions sq.ι :=
    SSet.anodyneExtensions_pushoutObjObjι sq (contractedVertexInclusion_anodyne v C hC)
  have : HasLiftingProperty sq.ι p := ha _ ((fibration_iff p).mp inferInstance)
  let c : CommSq g sq.ι p b := ⟨hg⟩
  refine ⟨c.lift, ?_, ?_, c.fac_right⟩
  · have he : K ◁ contractedVertexInclusion v ≫ c.lift = fst K (Δ[0] : SSet.{0}) ≫ f := by
      rw [← il, Category.assoc, c.fac_left, gl]
    have hz := congrArg (fun q => zeroFaceSection K ≫ q) he
    simpa only [whisker_contractedVertex, ← Category.assoc,
      zeroFaceSection_fst, Category.id_comp] using hz
  · rw [← ir, Category.assoc, c.fac_left, gr]

end

end Thomason.Construction

end

end OAI
