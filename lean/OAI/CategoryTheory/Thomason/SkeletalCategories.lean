import Mathlib
import OAI.CategoryTheory.Thomason.GlobularComplexes

namespace OAI

/-! Skeletal Categories. -/

noncomputable section
universe u v w z


namespace Thomason

open DirectedComplex NormalizedChains OmegaCategory

lemma lambdaNuForward_counit {K : DirectedComplex.{u}} {L : DirectedComplex.{v}}
    (f : Hom K L) : lambdaNuForward (Hom.comp K.lambdaCounit f) = f.nu := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Table.ext
  funext p b
  cases b
  · change f.map p (K.lambdaCounitMap p (K.nu.lambdaGen (K.nu.sourceCell p x))) = f.map p (x.row p false)
    rw [K.lambdaCounitMap_gen]
    exact congrArg (f.map p) (Table.truncate_top_row p false x false)
  · change f.map p (K.lambdaCounitMap p (K.nu.lambdaGen (K.nu.targetCell p x))) = f.map p (x.row p true)
    rw [K.lambdaCounitMap_gen]
    exact congrArg (f.map p) (Table.truncate_top_row p true x false)

noncomputable def orientalChain (N : ℕ) {K : DirectedComplex.{u}}
    (F : OmegaCategory.Functor (Oriental N) K.nu) : Hom (complex (Fin (N+1))) K :=
  Hom.comp (simplexCounitInverse N) (lambdaNuBackward F)

lemma orientalChain_nu (N : ℕ) {K : DirectedComplex.{u}}
    (F : OmegaCategory.Functor (Oriental N) K.nu) : (orientalChain N F).nu = F := by
  rw [← lambdaNuForward_counit]
  change lambdaNuForward (Hom.comp
    (Hom.comp (complex (Fin (N+1))).lambdaCounit (simplexCounitInverse N))
    (lambdaNuBackward F)) = F
  rw [counit_simplexCounitInverse]
  exact lambdaNu_right_inv F

lemma orientalChain_of_nu (N : ℕ) {K : DirectedComplex.{u}}
    (f : Hom (complex (Fin (N+1))) K) : orientalChain N f.nu = f := by
  unfold orientalChain
  rw [← lambdaNuForward_counit f, lambdaNu_left_inv]
  change Hom.comp (Hom.comp (simplexCounitInverse N)
    (complex (Fin (N+1))).lambdaCounit) f = f
  rw [simplexCounitInverse_counit]
  rfl

lemma oriental_nu_injective {N : ℕ} {K : DirectedComplex.{u}}
    {f g : Hom (complex (Fin (N+1))) K} (h : f.nu = g.nu) : f = g := by
  simpa only [orientalChain_of_nu] using congrArg (orientalChain N) h

noncomputable def orientalChainEquiv (N : ℕ) (K : DirectedComplex.{u}) :
    Hom (complex (Fin (N+1))) K ≃ OmegaCategory.Functor (Oriental N) K.nu where
  toFun := Hom.nu
  invFun := orientalChain N
  left_inv := orientalChain_of_nu N
  right_inv := orientalChain_nu N

lemma orientalChain_natural {m n : ℕ} {K : DirectedComplex.{u}}
    (a : Fin (m+1) →o Fin (n+1)) (F : OmegaCategory.Functor (Oriental n) K.nu) :
    orientalChain m (OmegaCategory.Functor.comp (complexMap a).nu F) =
      Hom.comp (complexMap a) (orientalChain n F) := by
  apply oriental_nu_injective
  rw [orientalChain_nu]
  change OmegaCategory.Functor.comp (complexMap a).nu F =
    OmegaCategory.Functor.comp (complexMap a).nu (orientalChain n F).nu
  rw [orientalChain_nu]

lemma orientalChain_postcomp {m : ℕ} {K : DirectedComplex.{u}} {L : DirectedComplex.{v}}
    (F : OmegaCategory.Functor (Oriental m) K.nu) (g : Hom K L) :
    orientalChain m (OmegaCategory.Functor.comp F g.nu) = Hom.comp (orientalChain m F) g := by
  apply oriental_nu_injective
  rw [orientalChain_nu]
  change OmegaCategory.Functor.comp F g.nu =
    OmegaCategory.Functor.comp (orientalChain m F).nu g.nu
  rw [orientalChain_nu]
  rfl

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open DirectedComplex NormalizedChains OmegaCategory
open CategoryTheory Simplicial MonoidalCategory Opposite

noncomputable def chainNerveCylinderSimplex {K L : DirectedComplex.{u}}
    (h : Hom K.cylinder L) (N : ℕ) (F : OmegaCategory.Functor (Oriental N) K.nu)
    (θ : Fin (N+1) →o Fin 2) : OmegaCategory.Functor (Oriental N) L.nu :=
  (Hom.comp (awHom θ) (Hom.comp (orientalChain N F).cylinder h)).nu

lemma chainNerveCylinderSimplex_natural {K L : DirectedComplex.{u}}
    (h : Hom K.cylinder L) {m n : ℕ} (a : Fin (m+1) →o Fin (n+1))
    (F : OmegaCategory.Functor (Oriental n) K.nu) (θ : Fin (n+1) →o Fin 2) :
    chainNerveCylinderSimplex h m (OmegaCategory.Functor.comp (complexMap a).nu F)
      (θ.comp a) = OmegaCategory.Functor.comp (complexMap a).nu
        (chainNerveCylinderSimplex h n F θ) := by
  unfold chainNerveCylinderSimplex
  rw [orientalChain_natural, Hom.cylinder_comp]
  change (Hom.comp (Hom.comp (awHom (θ.comp a)) (complexMap a).cylinder)
      (Hom.comp (orientalChain n F).cylinder h)).nu =
    (Hom.comp (Hom.comp (complexMap a) (awHom θ))
      (Hom.comp (orientalChain n F).cylinder h)).nu
  rw [awHom_naturality]

lemma chainNerveCylinderSimplex_endpoint {K L : DirectedComplex.{u}}
    (h : Hom K.cylinder L) (N : ℕ) (F : OmegaCategory.Functor (Oriental N) K.nu)
    (b : Bool) : chainNerveCylinderSimplex h N F
      (OrderHom.const _ (if b then 1 else 0)) =
      OmegaCategory.Functor.comp F (Hom.comp (K.cylinderEndpoint b) h).nu := by
  unfold chainNerveCylinderSimplex
  rw [awHom_endpoint]
  change (Hom.comp (Hom.comp ((complex (Fin (N+1))).cylinderEndpoint b)
    (orientalChain N F).cylinder) h).nu = _
  rw [Hom.cylinder_endpoint]
  change OmegaCategory.Functor.comp (orientalChain N F).nu
    (Hom.comp (K.cylinderEndpoint b) h).nu = _
  rw [orientalChain_nu]
  rfl

noncomputable def chainNerveCylinder {K L : DirectedComplex.{u}} (h : Hom K.cylinder L) :
    streetNerve K.nu ⊗ Δ[1] ⟶ streetNerve L.nu where
  app m := ↾fun x => chainNerveCylinderSimplex h m.unop.len x.1
    (SSet.stdSimplex.objEquiv x.2).toOrderHom
  naturality m n a := by
    apply ConcreteCategory.hom_ext
    intro x
    exact chainNerveCylinderSimplex_natural h a.unop.toOrderHom x.1
      (SSet.stdSimplex.objEquiv x.2).toOrderHom

lemma chainNerveCylinder_endpoint {K L : DirectedComplex.{u}} (h : Hom K.cylinder L)
    (b : Bool) : (if b then SSet.ι₁ else SSet.ι₀) ≫ chainNerveCylinder h =
      streetNerveMap (Hom.comp (K.cylinderEndpoint b) h).nu := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  cases b
  · exact chainNerveCylinderSimplex_endpoint h m.unop.len F false
  · exact chainNerveCylinderSimplex_endpoint h m.unop.len F true

noncomputable def chainNerveHomotopy {K L : DirectedComplex.{u}} (h : Hom K.cylinder L) :
    SSet.Homotopy (streetNerveMap (Hom.comp (K.cylinderEndpoint false) h).nu)
      (streetNerveMap (Hom.comp (K.cylinderEndpoint true) h).nu) where
  h := chainNerveCylinder h
  h₀ := chainNerveCylinder_endpoint h false
  h₁ := chainNerveCylinder_endpoint h true
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x, hx⟩, θ⟩
    exact False.elim hx

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory DirectedComplex

lemma simplicialWeakEquivalences_homotopy {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) : simplicialWeakEquivalences f ↔ simplicialWeakEquivalences g := by
  have hf : simplicialWeakEquivalences f ↔ simplicialWeakEquivalences H.h := by
    constructor
    · intro hf
      apply simplicialWeakEquivalences.of_precomp SSet.ι₀ H.h
        (SimplicialCylinder.endpoint_weak X).1
      rwa [H.h₀]
    · intro hh
      rw [← H.h₀]
      exact simplicialWeakEquivalences.comp_mem _ _ (SimplicialCylinder.endpoint_weak X).1 hh
  have hg : simplicialWeakEquivalences g ↔ simplicialWeakEquivalences H.h := by
    constructor
    · intro hg
      apply simplicialWeakEquivalences.of_precomp SSet.ι₁ H.h
        (SimplicialCylinder.endpoint_weak X).2
      rwa [H.h₁]
    · intro hh
      rw [← H.h₁]
      exact simplicialWeakEquivalences.comp_mem _ _ (SimplicialCylinder.endpoint_weak X).2 hh
  exact hf.trans hg.symm

lemma simplicialWeakEquivalence_of_simplicial_retract {X Y : SSet.{u}} (f : X ⟶ Y)
    (g : Y ⟶ X) (hr : g ≫ f = 𝟙 Y) (H : SSet.Homotopy (𝟙 X) (f ≫ g)) :
    simplicialWeakEquivalences f := by
  have hw := (simplicialWeakEquivalences_homotopy H).mp (simplicialWeakEquivalences.id_mem X)
  have hret : RetractArrow f (f ≫ g) :=
    { i := Arrow.homMk (𝟙 X) g (by change 𝟙 X ≫ (f ≫ g) = f ≫ g; simp)
      r := Arrow.homMk (𝟙 X) f (by change 𝟙 X ≫ f = (f ≫ g) ≫ f; simp [Category.assoc,hr])
      retract := by ext <;> simp [hr] }
  exact simplicialWeakEquivalences.of_retract hret hw

namespace DirectedComplex.PositiveAntihomotopy

variable {K L : DirectedComplex.{u}} {f g : Hom K L}

noncomputable def nerveHomotopy (h : PositiveAntihomotopy f g) :
    SSet.Homotopy (streetNerveMap f.nu) (streetNerveMap g.nu) := by
  simpa only [h.cylinderHom_endpoint_false, h.cylinderHom_endpoint_true] using
    chainNerveHomotopy h.cylinderHom

lemma nerve_weak_iff (h : PositiveAntihomotopy f g) :
    simplicialWeakEquivalences (streetNerveMap f.nu) ↔
      simplicialWeakEquivalences (streetNerveMap g.nu) :=
  simplicialWeakEquivalences_homotopy h.nerveHomotopy

end DirectedComplex.PositiveAntihomotopy

namespace RelativePrismData

open NormalizedChains

variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)

noncomputable def tableNerveHomotopy :
    SSet.Homotopy (streetNerveMap (complexMap d.f).nu)
      (streetNerveMap (complexMap d.g).nu) := d.antihomotopy.nerveHomotopy

lemma tableNerve_weak_iff :
    simplicialWeakEquivalences (streetNerveMap (complexMap d.f).nu) ↔
      simplicialWeakEquivalences (streetNerveMap (complexMap d.g).nu) :=
  d.antihomotopy.nerve_weak_iff

end RelativePrismData

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def twoLoopWords : OmegaCategory.{0} where
  Cell := List Bool
  source n x := if n = 0 then [] else x
  target n x := if n = 0 then [] else x
  source_source i j x := by cases i <;> cases j <;> simp
  target_target i j x := by cases i <;> cases j <;> simp
  source_target i j x := by cases i <;> cases j <;> simp
  target_source i j x := by cases i <;> cases j <;> simp
  comp k x y _ := if k = 0 then x ++ y else x
  source_comp_le i k hik x y h := by cases i <;> cases k <;> simp_all
  target_comp_le i k hik x y h := by cases i <;> cases k <;> simp_all
  source_comp_gt i k hki x y h hs := by cases i <;> simp_all
  target_comp_gt i k hki x y h ht := by cases i <;> simp_all
  unit_left k x h := by cases k <;> simp
  unit_right k x h := by cases k <;> simp
  assoc k x y z hxy hyz hxy_z hx_yz := by cases k <;> simp [List.append_assoc]
  interchange k l hkl a b c d hab hcd hac hbd hab_cd hac_bd := by
    have hl : l ≠ 0 := by omega
    simp only [hl, ite_false]
  finite_dimension x := ⟨1, rfl⟩

lemma twoLoopWords_lambda_commutes (a b : List Bool) :
    twoLoopWords.lambdaUnit.map (a ++ b) = twoLoopWords.lambdaUnit.map (b ++ a) := by
  apply DirectedComplex.Table.ext
  funext p e
  cases p with
  | zero => cases e <;> rfl
  | succ p =>
    cases p with
    | zero =>
      have h (a b : List Bool) : twoLoopWords.lambdaGen
          (twoLoopWords.sourceCell 1 (a ++ b)) =
          twoLoopWords.lambdaGen (twoLoopWords.sourceCell 1 a) +
          twoLoopWords.lambdaGen (twoLoopWords.sourceCell 1 b) := by
        exact twoLoopWords.lambdaGen_comp (by decide : 0 < 1)
          (twoLoopWords.sourceCell 1 a) (twoLoopWords.sourceCell 1 b) rfl
      cases e <;> change twoLoopWords.lambdaGen (twoLoopWords.sourceCell 1 (a ++ b)) =
        twoLoopWords.lambdaGen (twoLoopWords.sourceCell 1 (b ++ a))
      all_goals rw [h, h, add_comm]
    | succ p =>
      have h (a : List Bool) : twoLoopWords.lambdaGen (twoLoopWords.sourceCell (p+2) a) = 0 :=
        twoLoopWords.lambdaGen_degenerate (show 1 < p+2 by omega)
          (twoLoopWords.sourceCell (p+2) a) rfl
      cases e <;> change twoLoopWords.lambdaGen (twoLoopWords.sourceCell (p+2) (a ++ b)) =
        twoLoopWords.lambdaGen (twoLoopWords.sourceCell (p+2) (b ++ a))
      all_goals rw [h, h]

theorem lambdaUnit_not_always_injective :
    ¬ Function.Injective twoLoopWords.lambdaUnit.map := by
  intro hi
  have he := hi (twoLoopWords_lambda_commutes [false] [true])
  have hn : ([false,true] : List Bool) ≠ [true,false] := by decide
  exact hn he

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.KanQuillen

open CategoryTheory Limits Simplicial Opposite

variable {X Y : SSet.{u}}

def vertexOf {n : SimplexCategory} (x : X.obj (op n)) (i : Fin (n.len+1)) : X _⦋0⦌ :=
  X.map (SimplexCategory.const ⦋0⦌ n i).op x

lemma vertexOf_map {n m : SimplexCategory} (a : n ⟶ m) (x : X.obj (op m))
    (i : Fin (n.len+1)) :
    vertexOf (X.map a.op x) i = vertexOf x (a.toOrderHom i) := by
  change (X.map a.op ≫ X.map (SimplexCategory.const ⦋0⦌ n i).op) x = _
  rw [← X.map_comp]
  rfl

lemma vertexOf_natural (f : X ⟶ Y) {n : SimplexCategory} (x : X.obj (op n))
    (i : Fin (n.len+1)) : vertexOf (f.app _ x) i = f.app _ (vertexOf x i) :=
  (NatTrans.naturality_apply f _ x).symm

lemma vertexOf_zero (x : X _⦋0⦌) : vertexOf x 0 = x := by
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := Subsingleton.elim _ _
  simp [vertexOf, h]

lemma component_vertices {n : SimplexCategory} (x : X.obj (op n))
    (i j : Fin (n.len+1)) : SSet.π₀.mk (vertexOf x i) = SSet.π₀.mk (vertexOf x j) := by
  suffices hh : ∀ i j : Fin (n.len+1), i ≤ j →
      SSet.π₀.mk (vertexOf x i) = SSet.π₀.mk (vertexOf x j) by
    rcases le_total i j with h | h
    · exact hh i j h
    · exact (hh j i h).symm
  intro i j hij
  let e := SSet.stdSimplex.edge n.len i j hij
  have hs : (Δ[n.len] : SSet.{u}).δ 1 e = SSet.stdSimplex.const _ i _ := by
    ext k : 1
    fin_cases k
    rfl
  have ht : (Δ[n.len] : SSet.{u}).δ 0 e = SSet.stdSimplex.const _ j _ := by
    ext k : 1
    fin_cases k
    rfl
  let E : (Δ[n.len] : SSet.{u}).Edge (SSet.stdSimplex.const _ i _) (SSet.stdSimplex.const _ j _) :=
    SSet.Edge.mk e hs ht
  exact SSet.π₀.sound (E.map (SSet.yonedaEquiv.symm x))

def componentLabel (X : SSet.{u}) {n : SimplexCategoryᵒᵖ} (x : X.obj n) : SSet.π₀ X :=
  SSet.π₀.mk (vertexOf x 0)

lemma componentLabel_map (X : SSet.{u}) {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m)
    (x : X.obj n) : componentLabel X (X.map a x) = componentLabel X x := by
  change SSet.π₀.mk (vertexOf (X.map a.unop.op x) 0) = _
  rw [vertexOf_map]
  exact component_vertices x _ _

lemma componentLabel_natural (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    componentLabel Y (f.app n x) = SSet.mapπ₀ f (componentLabel X x) := by
  exact congrArg SSet.π₀.mk (vertexOf_natural f (n := n.unop) x 0)

lemma componentLabel_zero (x : X _⦋0⦌) : componentLabel X x = SSet.π₀.mk x := by
  simp only [componentLabel, vertexOf_zero]

end Thomason.KanQuillen

end

noncomputable section
universe u v w z


namespace Thomason.KanQuillen

open CategoryTheory Limits Simplicial Opposite

variable {X Y : SSet.{u}}

def componentSpace (X : SSet.{u}) : TopCat.{u} := @TopCat.of (SSet.π₀ X) ⊥

instance (X : SSet.{u}) : DiscreteTopology (componentSpace X) := ⟨rfl⟩

noncomputable def componentCocone (X : SSet.{u}) :
    Cocone ((CostructuredArrow.proj uliftYoneda.{u,0,0} X ⋙ uliftYoneda.{u,0,0}) ⋙ SSet.toTop.{u}) where
  pt := componentSpace X
  ι := {
    app j := TopCat.const (componentLabel X (SSet.yonedaEquiv j.hom))
    naturality j k a := by
      ext z
      change componentLabel X (SSet.yonedaEquiv k.hom) =
        componentLabel X (SSet.yonedaEquiv j.hom)
      have hw : SSet.stdSimplex.map a.left ≫ k.hom = j.hom := CostructuredArrow.w a
      exact (componentLabel_map X a.left.op _).symm.trans
        (congrArg (componentLabel X) ((SSet.yonedaEquiv_naturality a.left k.hom).trans
          (congrArg SSet.yonedaEquiv hw))) }

noncomputable def realizationIsColimit (X : SSet.{u}) :
    IsColimit (SSet.toTop.mapCocone (Presheaf.tautologicalCocone'.{u} X)) :=
  isColimitOfPreserves SSet.toTop (Presheaf.isColimitTautologicalCocone'.{u} X)

noncomputable def componentTop (X : SSet.{u}) : |X| ⟶ componentSpace X :=
  (realizationIsColimit X).desc (componentCocone X)

lemma componentTop_simplex {n : SimplexCategory} (s : SSet.stdSimplex.obj n ⟶ X)
    (z : |SSet.stdSimplex.obj n|) :
    componentTop X (SSet.toTop.map s z) = componentLabel X (SSet.yonedaEquiv s) :=
  ConcreteCategory.congr_hom ((realizationIsColimit X).fac (componentCocone X)
    (CostructuredArrow.mk s)) z

noncomputable def realVertex (x : X _⦋0⦌) : |X| :=
  SSet.toTop.map (SSet.yonedaEquiv.symm x) default

lemma componentTop_vertex (x : X _⦋0⦌) : componentTop X (realVertex x) = SSet.π₀.mk x := by
  rw [realVertex, componentTop_simplex, Equiv.apply_symm_apply, componentLabel_zero]

lemma realVertex_natural (f : X ⟶ Y) (x : X _⦋0⦌) :
    realVertex (f.app _ x) = SSet.toTop.map f (realVertex x) := by
  rw [realVertex, ← SSet.yonedaEquiv_symm_comp, SSet.toTop.map_comp]
  rfl

lemma realVertex_of_simplex {n : SimplexCategory} (x : X.obj (op n)) (i : Fin (n.len+1)) :
    realVertex (vertexOf x i) = SSet.toTop.map (SSet.yonedaEquiv.symm x)
      (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ n i)) default) := by
  rw [realVertex, vertexOf, ← SSet.yonedaEquiv_symm_naturality_left, SSet.toTop.map_comp]
  rfl

lemma joined_simplex_vertex {n : SimplexCategory} (x : X.obj (op n))
    (i : Fin (n.len+1)) (z : |SSet.stdSimplex.obj n|) :
    Joined (realVertex (vertexOf x i)) (SSet.toTop.map (SSet.yonedaEquiv.symm x) z) := by
  let : PathConnectedSpace |SSet.stdSimplex.obj n| :=
    n.toTopHomeo.symm.surjective.pathConnectedSpace n.toTopHomeo.symm.continuous
  rw [realVertex_of_simplex]
  exact (PathConnectedSpace.joined _ _).map (SSet.toTop.map (SSet.yonedaEquiv.symm x)).hom.continuous

lemma exists_vertex_joined (z : |X|) : ∃ x : X _⦋0⦌, Joined (realVertex x) z := by
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) (realizationIsColimit X)) z
  refine ⟨vertexOf (SSet.yonedaEquiv j.hom) 0, ?_⟩
  change SSet.toTop.map j.hom y = z at hy
  rw [← hy]
  have he : SSet.yonedaEquiv.symm (SSet.yonedaEquiv j.hom) = j.hom :=
    SSet.yonedaEquiv.symm_apply_apply j.hom
  have hj := joined_simplex_vertex (SSet.yonedaEquiv j.hom) 0 y
  rw [he] at hj
  exact hj

lemma joined_real_edge {x y : X _⦋0⦌} (e : X.Edge x y) : Joined (realVertex x) (realVertex y) := by
  have h0 : SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 = SimplexCategory.δ (1 : Fin 2) := by decide
  have h1 : SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 = SimplexCategory.δ (0 : Fin 2) := by decide
  have hs : vertexOf e.edge 0 = x := by simpa only [vertexOf, h0, SimplicialObject.δ] using e.src_eq
  have ht : vertexOf e.edge 1 = y := by simpa only [vertexOf, h1, SimplicialObject.δ] using e.tgt_eq
  have hj := joined_simplex_vertex e.edge 0
    (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)) default)
  rw [← realVertex_of_simplex e.edge 1] at hj
  simpa only [hs, ht] using hj

noncomputable def componentComparison (X : SSet.{u}) : SSet.π₀ X → ZerothHomotopy |X| :=
  SSet.π₀.lift (fun x => ZerothHomotopy.mk (realVertex x))
    (fun _ _ e => Quotient.sound (joined_real_edge e))

lemma componentTop_eq_of_joined {x y : |X|} (h : Joined x y) : componentTop X x = componentTop X y := by
  obtain ⟨p⟩ := h
  have he : (componentTop X) (p 0) = componentTop X (p 1) :=
    PreconnectedSpace.constant inferInstance ((componentTop X).hom.continuous.comp p.continuous)
  simpa only [p.source, p.target] using he

lemma componentComparison_injective (X : SSet.{u}) : Function.Injective (componentComparison X) := by
  intro a b h
  induction a using SSet.π₀.rec with | mk a =>
    induction b using SSet.π₀.rec with | mk b =>
      have hj : Joined (realVertex a) (realVertex b) := Quotient.exact h
      have hh := componentTop_eq_of_joined hj
      rw [componentTop_vertex, componentTop_vertex] at hh
      exact hh

lemma componentComparison_surjective (X : SSet.{u}) : Function.Surjective (componentComparison X) := by
  intro z
  induction z using ZerothHomotopy.rec with | mk z =>
    obtain ⟨x, hx⟩ := exists_vertex_joined z
    exact ⟨SSet.π₀.mk x, Quotient.sound hx⟩

noncomputable def componentEquiv (X : SSet.{u}) : SSet.π₀ X ≃ ZerothHomotopy |X| :=
  Equiv.ofBijective (componentComparison X)
    ⟨componentComparison_injective X, componentComparison_surjective X⟩

lemma componentComparison_natural (f : X ⟶ Y) (a : SSet.π₀ X) :
    componentComparison Y (SSet.mapπ₀ f a) =
      WeakHomotopy.componentsMap (SSet.toTop.map f).hom (componentComparison X a) := by
  induction a using SSet.π₀.rec with | mk a =>
    exact congrArg ZerothHomotopy.mk (realVertex_natural f a)

lemma map_components_bijective_of_weak (f : X ⟶ Y) (hf : simplicialWeakEquivalences f) :
    Function.Bijective (SSet.mapπ₀ f) := by
  have he : SSet.mapπ₀ f = (componentEquiv Y).symm ∘
      WeakHomotopy.componentsMap (SSet.toTop.map f).hom ∘ componentEquiv X := by
    funext a
    apply (componentEquiv Y).injective
    change componentComparison Y (SSet.mapπ₀ f a) =
      (componentEquiv Y) ((componentEquiv Y).symm _)
    rw [Equiv.apply_symm_apply]
    exact componentComparison_natural f a
  rw [he]
  exact (componentEquiv Y).symm.bijective.comp (hf.1.comp (componentEquiv X).bijective)

end Thomason.KanQuillen

end

noncomputable section
universe u v w z


namespace Thomason.KanQuillen

open CategoryTheory Simplicial Opposite

variable {X Y : SSet.{u}}

lemma lift_edge_endpoint (p : X ⟶ Y) (hp : simplicialFibrations p)
    (j : Fin 2) (e : Y _⦋1⦌) (x : X _⦋0⦌) (hx : p.app _ x = Y.δ j e) :
    ∃ e' : X _⦋1⦌, X.δ j e' = x ∧ p.app _ e' = e := by
  have : HasLiftingProperty (SSet.stdSimplex.δ (n := 0) j) p :=
    SimplicialCylinder.delta_one_anodyne j p hp
  let sq : CommSq (SSet.yonedaEquiv.symm x) (SSet.stdSimplex.δ j) p
      (SSet.yonedaEquiv.symm e) := ⟨by
    rw [SSet.yonedaEquiv_symm_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm, hx]⟩
  refine ⟨SSet.yonedaEquiv sq.lift, ?_, ?_⟩
  · have h := congrArg SSet.yonedaEquiv sq.fac_left
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using h
  · have h := congrArg SSet.yonedaEquiv sq.fac_right
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h

lemma fibration_range_edge (p : X ⟶ Y) (hp : simplicialFibrations p)
    {a b : Y _⦋0⦌} (e : Y.Edge a b) :
    (∃ x, p.app _ x = a) ↔ (∃ x, p.app _ x = b) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨e', _, he'⟩ := lift_edge_endpoint p hp 1 e.edge x (hx.trans e.src_eq.symm)
    refine ⟨X.δ 0 e', ?_⟩
    have hn := ConcreteCategory.congr_hom (p.naturality (SimplexCategory.δ (0 : Fin 2)).op) e'
    change p.app _ (X.δ 0 e') = Y.δ 0 (p.app _ e') at hn
    exact hn.trans ((congrArg (Y.δ 0) he').trans e.tgt_eq)
  · rintro ⟨x, hx⟩
    obtain ⟨e', _, he'⟩ := lift_edge_endpoint p hp 0 e.edge x (hx.trans e.tgt_eq.symm)
    refine ⟨X.δ 1 e', ?_⟩
    have hn := ConcreteCategory.congr_hom (p.naturality (SimplexCategory.δ (1 : Fin 2)).op) e'
    change p.app _ (X.δ 1 e') = Y.δ 1 (p.app _ e') at hn
    exact hn.trans ((congrArg (Y.δ 1) he').trans e.src_eq)

lemma fibration_range_components (p : X ⟶ Y) (hp : simplicialFibrations p)
    {a b : Y _⦋0⦌} (h : SSet.π₀.mk a = SSet.π₀.mk b) :
    (∃ x, p.app _ x = a) ↔ (∃ x, p.app _ x = b) := by
  let r : SSet.π₀ Y → Prop := SSet.π₀.lift (fun y => ∃ x, p.app _ x = y)
    (fun _ _ e => propext (fibration_range_edge p hp e))
  exact Iff.of_eq (congrArg r h)

theorem weak_fibration_surjective_vertices (p : X ⟶ Y)
    (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p) :
    Function.Surjective (p.app (op ⦋0⦌)) := by
  intro y
  obtain ⟨a, ha⟩ := (map_components_bijective_of_weak p hw).2 (SSet.π₀.mk y)
  induction a using SSet.π₀.rec with | mk x =>
    exact (fibration_range_components p hp ha).1 ⟨x, rfl⟩

end Thomason.KanQuillen

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

namespace CategoryCell

variable {C : Type u} [Category.{v} C]

def source : ℕ → Arrow C → Arrow C
  | 0, x => Arrow.mk (𝟙 x.left)
  | _+1, x => x

def target : ℕ → Arrow C → Arrow C
  | 0, x => Arrow.mk (𝟙 x.right)
  | _+1, x => x

def comp : (k : ℕ) → (x y : Arrow C) → target k x = source k y → Arrow C
  | 0, x, y, h => Arrow.mk (x.hom ≫ eqToHom (congrArg Arrow.left h) ≫ y.hom)
  | _+1, x, _, _ => x

@[simp] lemma source_zero (x : Arrow C) : source 0 x = Arrow.mk (𝟙 x.left) := rfl
@[simp] lemma source_succ (k : ℕ) (x : Arrow C) : source (k+1) x = x := rfl
@[simp] lemma target_zero (x : Arrow C) : target 0 x = Arrow.mk (𝟙 x.right) := rfl
@[simp] lemma target_succ (k : ℕ) (x : Arrow C) : target (k+1) x = x := rfl
@[simp] lemma comp_succ (k : ℕ) (x y : Arrow C) (h) : comp (k+1) x y h = x := rfl

end CategoryCell

def ofCategory (C : Type u) [Category.{v} C] : OmegaCategory.{max u v} where
  Cell := Arrow C
  source := CategoryCell.source
  target := CategoryCell.target
  source_source i j x := by cases i <;> cases j <;> simp [CategoryCell.source]
  target_target i j x := by cases i <;> cases j <;> simp [CategoryCell.target]
  source_target i j x := by cases i <;> cases j <;> simp [CategoryCell.source, CategoryCell.target]
  target_source i j x := by cases i <;> cases j <;> simp [CategoryCell.source, CategoryCell.target]
  comp := CategoryCell.comp
  source_comp_le i k hik x y h := by
    cases k with
    | zero =>
      have hi : i = 0 := by omega
      subst i
      rfl
    | succ k => rfl
  target_comp_le i k hik x y h := by
    cases k with
    | zero =>
      have hi : i = 0 := by omega
      subst i
      rfl
    | succ k => exact congrArg (CategoryCell.target i) h
  source_comp_gt i k hki x y h hs := by cases i <;> first | omega | rfl
  target_comp_gt i k hki x y h hs := by cases i <;> first | omega | rfl
  unit_left k x h := by
    cases k with
    | zero =>
      refine Arrow.ext (by rfl) (by rfl) ?_
      dsimp [CategoryCell.comp, CategoryCell.source]
      simp
      exact (Category.id_comp _).symm
    | succ k => rfl
  unit_right k x h := by
    cases k with
    | zero =>
      refine Arrow.ext (by rfl) (by rfl) ?_
      dsimp [CategoryCell.comp, CategoryCell.target]
      simp
      exact (Category.id_comp _).symm
    | succ k => rfl
  assoc k x y z hxy hyz hxy_z hx_yz := by
    cases k with
    | zero =>
      refine Arrow.ext (by rfl) (by rfl) ?_
      dsimp [CategoryCell.comp]
      change (x.hom ≫ eqToHom (congrArg Arrow.left hxy) ≫ y.hom) ≫
        eqToHom (congrArg Arrow.left hyz) ≫ z.hom =
        (𝟙 x.left) ≫ (x.hom ≫ eqToHom (congrArg Arrow.left hxy) ≫
          (y.hom ≫ eqToHom (congrArg Arrow.left hyz) ≫ z.hom)) ≫ 𝟙 z.right
      simp only [Category.id_comp, Category.comp_id, Category.assoc]
      exact congrArg (fun f => x.hom ≫ f) (Category.assoc _ _ _)
    | succ k => rfl
  interchange k l hkl a b c d hab hcd hac hbd hab_cd hac_bd := by
    cases l with
    | zero => omega
    | succ l => rfl
  finite_dimension x := ⟨1, rfl⟩

lemma ofCategory_truncated (C : Type u) [Category.{v} C] :
    (ofCategory C).IsTruncated 1 := fun _ => rfl

def ofCategoryMap {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    (F : C ⥤ D) : Functor (ofCategory C) (ofCategory D) where
  map x := Arrow.mk (F.map x.hom)
  map_source k x := by
    cases k with
    | zero =>
      refine Arrow.ext (by rfl) (by rfl) ?_
      dsimp [ofCategory, CategoryCell.source]
      simp
      rfl
    | succ k => rfl
  map_target k x := by
    cases k with
    | zero =>
      refine Arrow.ext (by rfl) (by rfl) ?_
      dsimp [ofCategory, CategoryCell.target]
      simp
      rfl
    | succ k => rfl
  map_comp k x y h h' := by
    cases k with
    | zero =>
      refine Arrow.ext (by rfl) (by rfl) ?_
      dsimp [ofCategory, CategoryCell.comp]
      change F.map (x.hom ≫ eqToHom (congrArg Arrow.left h) ≫ y.hom) =
        (𝟙 (F.obj x.left)) ≫
          (F.map x.hom ≫ eqToHom (congrArg Arrow.left h') ≫ F.map y.hom) ≫
            𝟙 (F.obj y.right)
      simp only [Category.id_comp, Category.comp_id, F.map_comp]
      congr 2
      exact (F.map_comp _ _).trans
        (congrArg (fun q => q ≫ F.map y.hom) (eqToHom_map F _))
    | succ k => rfl

lemma ofCategoryMap_id (C : Type u) [Category.{v} C] :
    ofCategoryMap (𝟭 C) = Functor.id (ofCategory C) := by
  ext x
  rfl

lemma ofCategoryMap_comp {C D E : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} E] (F : C ⥤ D) (G : D ⥤ E) :
    ofCategoryMap (F ⋙ G) = Functor.comp (ofCategoryMap F) (ofCategoryMap G) := by
  ext x
  rfl

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

lemma comp_congr_cells (C : OmegaCategory.{u}) (k : ℕ) {x y x' y' : C.Cell}
    (h : C.target k x = C.source k y) (h' : C.target k x' = C.source k y')
    (hx : x = x') (hy : y = y') : C.comp k x y h = C.comp k x' y' h' := by
  subst x'; subst y'; rfl

def OneSkeleton (C : OmegaCategory.{u}) := C.Objects

def OneHom (C : OmegaCategory.{u}) (a b : OneSkeleton C) :=
  {x : C.Cell // C.source 1 x = x ∧ C.source 0 x = a.val ∧ C.target 0 x = b.val}

namespace OneHom

variable {C : OmegaCategory.{u}}

 def id (a : OneSkeleton C) : OneHom C a a :=
  ⟨a.val, C.source_fixed_upwards (by omega) a.property, a.property,
    C.target_eq_self_of_source_eq_self a.property⟩

 def comp {a b c : OneSkeleton C} (f : OneHom C a b) (g : OneHom C b c) :
    OneHom C a c :=
  ⟨C.comp 0 f.val g.val (f.property.2.2.trans g.property.2.1.symm), by
      rw [C.source_comp_gt 1 0 (by omega) _ _ _
        (C.source_composable (by omega) (f.property.2.2.trans g.property.2.1.symm))]
      simp only [f.property.1, g.property.1],
    (C.source_comp_le 0 0 le_rfl _ _ _).trans f.property.2.1,
    (C.target_comp_le 0 0 le_rfl _ _ _).trans g.property.2.2⟩

end OneHom

instance oneSkeletonCategory (C : OmegaCategory.{u}) : Category (OneSkeleton C) where
  Hom := OneHom C
  id := OneHom.id
  comp := OneHom.comp
  id_comp {a b} f := by
    apply Subtype.ext
    change C.comp 0 a.val f.val _ = f.val
    have ha : a.val = C.source 0 f.val := f.property.2.1.symm
    exact (C.comp_congr_cells 0 _ (C.target_source_self 0 _) ha rfl).trans
      (C.unit_left 0 f.val _)
  comp_id {a b} f := by
    apply Subtype.ext
    change C.comp 0 f.val b.val _ = f.val
    have hb : b.val = C.target 0 f.val := f.property.2.2.symm
    exact (C.comp_congr_cells 0 _ (C.source_target_self 0 _).symm rfl hb).trans
      (C.unit_right 0 f.val _)
  assoc f g h := by
    apply Subtype.ext
    exact C.assoc 0 f.val g.val h.val _ _ _ _

@[simp] lemma one_id_val {C : OmegaCategory.{u}} (a : C.OneSkeleton) :
    (𝟙 a : a ⟶ a).val = a.val := rfl

@[simp] lemma one_comp_val {C : OmegaCategory.{u}} {a b c : C.OneSkeleton}
    (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).val = C.comp 0 f.val g.val (f.property.2.2.trans g.property.2.1.symm) := rfl

@[simp] lemma one_eqToHom_val {C : OmegaCategory.{u}} {a b : C.OneSkeleton} (h : a = b) :
    (eqToHom h).val = a.val := by subst b; rfl

lemma one_eqToHom_comp_val {C : OmegaCategory.{u}} {a b c : C.OneSkeleton}
    (h : a = b) (f : b ⟶ c) : (eqToHom h ≫ f).val = f.val := by
  subst b
  simp only [eqToHom_refl, Category.id_comp]

lemma one_comp_eqToHom_val {C : OmegaCategory.{u}} {a b c : C.OneSkeleton}
    (f : a ⟶ b) (h : b = c) : (f ≫ eqToHom h).val = f.val := by
  subst c
  simp only [eqToHom_refl, Category.comp_id]

def Functor.oneMap {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) : C.OneSkeleton ⥤ D.OneSkeleton where
  obj a := F.objects a
  map {a b} f := ⟨F.map f.val, by rw [← F.map_source, f.property.1],
    by rw [← F.map_source, f.property.2.1]; rfl,
    by rw [← F.map_target, f.property.2.2]; rfl⟩
  map_id a := rfl
  map_comp f g := by apply Subtype.ext; exact F.map_comp 0 _ _ _ _

def oneSkeletonEvaluation (C : OmegaCategory.{u}) : Functor (ofCategory C.OneSkeleton) C where
  map x := x.hom.val
  map_source k x := by
    cases k with
    | zero => exact x.hom.property.2.1.symm
    | succ k => exact (C.source_fixed_upwards (by omega) x.hom.property.1).symm
  map_target k x := by
    cases k with
    | zero => exact x.hom.property.2.2.symm
    | succ k => exact (C.target_eq_self_of_source_eq_self
        (C.source_fixed_upwards (by omega) x.hom.property.1)).symm
  map_comp k x y h h' := by
    cases k with
    | zero =>
      have hobj : x.right = y.left := congrArg Arrow.left h
      have he : (x.hom ≫ eqToHom hobj).val = x.hom.val := by
        rw [one_comp_val]
        exact (C.comp_congr_cells 0 _ (C.source_target_self 0 _).symm rfl
          ((one_eqToHom_val hobj).trans x.hom.property.2.2.symm)).trans
            (C.unit_right 0 _ _)
      change (x.hom ≫ eqToHom hobj ≫ y.hom).val = _
      rw [← Category.assoc, one_comp_val]
      exact C.comp_congr_cells 0 _ h' he rfl
    | succ k =>
      change x.hom.val = C.comp (k+1) x.hom.val y.hom.val h'
      have hy : C.source (k+1) y.hom.val = y.hom.val :=
        C.source_fixed_upwards (by omega) y.hom.property.1
      have he : y.hom.val = C.target (k+1) x.hom.val := hy.symm.trans h'.symm
      exact ((C.comp_congr_cells (k+1) h' (C.source_target_self (k+1) _).symm rfl he).trans
        (C.unit_right (k+1) _ _)).symm

lemma oneSkeletonEvaluation_injective (C : OmegaCategory.{u}) :
    Function.Injective C.oneSkeletonEvaluation.map := by
  intro x y h
  change Arrow C.OneSkeleton at x y
  change x.hom.val = y.hom.val at h
  have hl : x.left = y.left := Subtype.ext
    (x.hom.property.2.1.symm.trans ((congrArg (C.source 0) h).trans y.hom.property.2.1))
  have hr : x.right = y.right := Subtype.ext
    (x.hom.property.2.2.symm.trans ((congrArg (C.target 0) h).trans y.hom.property.2.2))
  rcases x with ⟨a, b, f⟩
  rcases y with ⟨a', b', g⟩
  change a = a' at hl
  change b = b' at hr
  subst a'; subst b'
  have he : f = g := Subtype.ext h
  cases he
  rfl

lemma oneSkeletonEvaluation_surjective {C : OmegaCategory.{u}} (hC : C.IsTruncated 1) :
    Function.Surjective C.oneSkeletonEvaluation.map := by
  intro x
  let f : OneHom C (C.sourceObject x) (C.targetObject x) := ⟨x, hC x, rfl, rfl⟩
  exact ⟨@Arrow.mk _ (oneSkeletonCategory C) (C.sourceObject x) (C.targetObject x) f, rfl⟩

noncomputable def oneSkeletonIso {C : OmegaCategory.{u}} (hC : C.IsTruncated 1) :
    ofCategory C.OneSkeleton ≅ C :=
  isoOfBijective C.oneSkeletonEvaluation
    ⟨C.oneSkeletonEvaluation_injective, oneSkeletonEvaluation_surjective hC⟩

end Thomason.OmegaCategory

end

end OAI
