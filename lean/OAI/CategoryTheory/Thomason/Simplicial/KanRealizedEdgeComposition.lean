import OAI.CategoryTheory.Thomason.Simplicial.FixedInternalPathMaps
import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.RealizationTopology
import OAI.CategoryTheory.Thomason.Simplicial.TopologicalDeformationTransport
import OAI.CategoryTheory.Thomason.Transfer.KanQuillenLiftingReduction
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
import Mathlib.Topology.Connected.TotallyDisconnected

namespace OAI

section

/-! # Simplicial edge components and actual realization components -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory CategoryTheory.Limits Convexity Opposite Topology
open scoped Simplicial

noncomputable section

def initialVertexEdgeOperator {n : ℕ} (j : Fin (n+1)) :
    SimplexCategory.mk 1 ⟶ .mk n :=
  SimplexCategory.Hom.mk {
    toFun := fun i => if i = 0 then 0 else j
    monotone' := by
      intro a b h
      fin_cases a <;> fin_cases b <;> simp_all }

def initialVertexEdge (K : SSet.{0}) {n : ℕ} (s : K.obj (.op (.mk n)))
    (j : Fin (n+1)) : SSet.Edge (simplexVertex K s 0) (simplexVertex K s j) :=
  SSet.Edge.mk (K.map (initialVertexEdgeOperator j).op s)
    (by
      change K.map (SimplexCategory.δ 1).op (K.map (initialVertexEdgeOperator j).op s) = _
      rw [← Functor.map_comp_apply, ← op_comp]
      have he : SimplexCategory.δ (1 : Fin 2) ≫ initialVertexEdgeOperator j =
          vertexOperator (0 : Fin (n+1)) := by
        apply SimplexCategory.Hom.ext
        apply DFunLike.ext
        intro i
        fin_cases i
        simp [initialVertexEdgeOperator, vertexOperator, SimplexCategory.δ]
        rfl
      rw [he]
      rfl)
    (by
      change K.map (SimplexCategory.δ 0).op (K.map (initialVertexEdgeOperator j).op s) = _
      rw [← Functor.map_comp_apply, ← op_comp]
      rfl)

def simplexComponent (K : SSet.{0}) {n : ℕ} (s : K.obj (.op (.mk n))) : SSet.π₀ K :=
  SSet.π₀.mk (simplexVertex K s 0)

theorem simplexComponent_vertex (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (j : Fin (n+1)) :
    simplexComponent K s = SSet.π₀.mk (simplexVertex K s j) :=
  SSet.π₀.sound (initialVertexEdge K s j)

theorem simplexComponent_map (K : SSet.{0}) {m n : ℕ}
    (f : SimplexCategory.mk m ⟶ .mk n) (s : K.obj (.op (.mk n))) :
    simplexComponent K (K.map f.op s) = simplexComponent K s := by
  unfold simplexComponent
  rw [simplexVertex_map]
  exact (simplexComponent_vertex K s (f.toOrderHom 0)).symm

/-- Edge components carry the discrete topology for this comparison. -/
def simplicialComponentsSpace (K : SSet.{0}) : TopCat.{0} :=
  @TopCat.of (SSet.π₀ K) ⊥

instance (K : SSet.{0}) : DiscreteTopology (simplicialComponentsSpace K) := ⟨rfl⟩

def simplicialComponentsCocone (K : SSet.{0}) : Cocone (diagram K) where
  pt := simplicialComponentsSpace K
  ι := {
    app j := { hom' :=
      ⟨fun _ => simplexComponent K (SSet.yonedaEquiv j.hom), continuous_const⟩ }
    naturality j k f := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      change simplexComponent K (SSet.yonedaEquiv k.hom) =
        simplexComponent K (SSet.yonedaEquiv j.hom)
      have hs : K.map f.left.op (SSet.yonedaEquiv k.hom) = SSet.yonedaEquiv j.hom := by
        rw [SSet.yonedaEquiv_naturality, CostructuredArrow.w f]
      rw [← hs]
      exact (simplexComponent_map K f.left _).symm }

def realizationComponent (K : SSet.{0}) :
    C(SSet.toTop.obj K, simplicialComponentsSpace K) :=
  ((isColimit K).desc (simplicialComponentsCocone K)).hom

theorem realizationComponent_simplex (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (p : StdSimplex ℝ (Fin (n+1))) :
    realizationComponent K (simplexPoint K s p) = simplexComponent K s := by
  have h := congrArg (fun f : _ ⟶ simplicialComponentsSpace K => f.hom (ULift.up p))
    ((isColimit K).fac (simplicialComponentsCocone K)
      (CostructuredArrow.mk (SSet.yonedaEquiv.symm s)))
  change realizationComponent K (simplexPoint K s p) =
    simplexComponent K (SSet.yonedaEquiv (SSet.yonedaEquiv.symm s)) at h
  rw [SSet.yonedaEquiv.apply_symm_apply] at h
  exact h

theorem realizationComponent_vertex (K : SSet.{0}) (v : K.obj (.op (.mk 0))) :
    realizationComponent K (vertexPoint K v) = SSet.π₀.mk v := by
  rw [vertexPoint, realizationComponent_simplex]
  change SSet.π₀.mk (K.map (vertexOperator (0 : Fin 1)).op v) = _
  have he : vertexOperator (0 : Fin 1) = 𝟙 (SimplexCategory.mk 0) := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [he]
  simp

/-- A continuous path in the actual realization cannot change its simplicial
edge component. This direction does not require a Kan condition. -/
theorem realizationComponent_path {K : SSet.{0}} {x y : SSet.toTop.obj K}
    (p : Path x y) : realizationComponent K x = realizationComponent K y := by
  have h := TotallyDisconnectedSpace.eq_of_continuous
    (realizationComponent K ∘ p) ((realizationComponent K).continuous.comp p.continuous) (0 : unitInterval) 1
  simpa only [Function.comp_apply, p.source, p.target] using h

/-- Actual paths between vertices yield finite zigzags of simplicial edges. -/
theorem edge_zigzag_of_realization_path {K : SSet.{0}}
    {v w : K.obj (.op (.mk 0))} (p : Path (vertexPoint K v) (vertexPoint K w)) :
    Relation.EqvGen SSet.π₀Rel v w := by
  apply (SSet.π₀.mk_eq_mk_iff v w).mp
  have h := realizationComponent_path p
  rw [realizationComponent_vertex, realizationComponent_vertex] at h
  exact h


/-- Every point is joined to an actual simplicial vertex, before any
subdivision or fibrancy replacement. -/
theorem point_joined_vertex (K : SSet.{0}) (x : SSet.toTop.obj K) :
    ∃ v : K.obj (.op (.mk 0)), Joined x (vertexPoint K v) := by
  obtain ⟨n, s, u, rfl⟩ := point_representation_simplex K x
  refine ⟨simplexVertex K s 0, ?_⟩
  have hj := (PathConnectedSpace.joined u (StdSimplex.single (0 : Fin (n+1)))).map
    (simplexPoint K s).continuous
  have he : simplexPoint K s (StdSimplex.single (0 : Fin (n+1))) =
      vertexPoint K (simplexVertex K s 0) := by
    unfold vertexPoint simplexVertex
    rw [simplexPoint_map, StdSimplex.map_single]
    rfl
  rwa [he] at hj

/-- Surjectivity on actual path components gives surjectivity on simplicial
edge components. No Kan hypothesis is used in this compatibility bridge. -/
theorem simplicial_components_surjective_of_realization {K L : SSet.{0}}
    (f : K ⟶ L)
    (hf : Function.Surjective (HomotopyMaps.componentsMap (SSet.toTop.map f).hom)) :
    Function.Surjective (SSet.mapπ₀ f) := by
  intro c
  obtain ⟨w, rfl⟩ := SSet.π₀.mk_surjective c
  obtain ⟨a, ha⟩ := hf (ZerothHomotopy.mk (vertexPoint L w))
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective a
  have hj : Joined ((SSet.toTop.map f).hom x) (vertexPoint L w) := Quotient.exact ha
  obtain ⟨v, hv⟩ := point_joined_vertex K x
  have hp := ((hv.map (SSet.toTop.map f).hom.continuous).symm.trans hj).somePath
  rw [map_vertexPoint] at hp
  refine ⟨SSet.π₀.mk v, ?_⟩
  exact (SSet.π₀.mk_eq_mk_iff _ _).mpr (edge_zigzag_of_realization_path hp)


/-- The geometric vertex of any simplex is the geometric point of its
corresponding zero-dimensional face. -/
theorem vertexPoint_simplexVertex (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (i : Fin (n+1)) :
    vertexPoint K (simplexVertex K s i) = simplexPoint K s (StdSimplex.single i) := by
  unfold vertexPoint simplexVertex
  rw [simplexPoint_map, StdSimplex.map_single]
  rfl

/-- Every simplicial edge gives an actual path with exactly its prescribed
vertices as endpoints. -/
theorem edge_joined {K : SSet.{0}} {v w : K.obj (.op (.mk 0))}
    (e : SSet.Edge v w) : Joined (vertexPoint K v) (vertexPoint K w) := by
  have hs : simplexVertex K e.edge 0 = v := by
    change K.map (vertexOperator (0 : Fin 2)).op e.edge = v
    have he : vertexOperator (0 : Fin 2) = SimplexCategory.δ (1 : Fin 2) := by
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro i
      fin_cases i
      simp [vertexOperator, SimplexCategory.δ]
    rw [he]
    exact e.src_eq
  have ht : simplexVertex K e.edge 1 = w := by
    change K.map (vertexOperator (1 : Fin 2)).op e.edge = w
    have he : vertexOperator (1 : Fin 2) = SimplexCategory.δ (0 : Fin 2) := by
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro i
      fin_cases i
      rfl
    rw [he]
    exact e.tgt_eq
  have hj := (PathConnectedSpace.joined (StdSimplex.single (0 : Fin 2))
    (StdSimplex.single 1)).map (simplexPoint K e.edge).continuous
  rw [← vertexPoint_simplexVertex, ← vertexPoint_simplexVertex, hs, ht] at hj
  exact hj

/-- Simplicial edge components map to actual path components. -/
def vertexComponents (K : SSet.{0}) : SSet.π₀ K → ZerothHomotopy (SSet.toTop.obj K) :=
  SSet.π₀.lift (fun v => ZerothHomotopy.mk (vertexPoint K v))
    (fun _ _ e => ZerothHomotopy.sound (edge_joined e).somePath)

/-- The map to discrete edge components descends through actual paths. -/
def realizationComponents (K : SSet.{0}) : ZerothHomotopy (SSet.toTop.obj K) → SSet.π₀ K :=
  ZerothHomotopy.lift (realizationComponent K) (fun _ _ p => realizationComponent_path p)

/-- Actual path components of geometric realization are exactly the
simplicial edge components, without a Kan or model-category hypothesis. -/
def realizationComponentsEquiv (K : SSet.{0}) :
    ZerothHomotopy (SSet.toTop.obj K) ≃ SSet.π₀ K where
  toFun := realizationComponents K
  invFun := vertexComponents K
  left_inv c := by
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
    obtain ⟨v, hv⟩ := point_joined_vertex K x
    have he : realizationComponent K x = SSet.π₀.mk v :=
      (realizationComponent_path hv.somePath).trans (realizationComponent_vertex K v)
    change vertexComponents K (realizationComponent K x) = ZerothHomotopy.mk x
    rw [he]
    exact (ZerothHomotopy.sound hv.somePath).symm
  right_inv c := by
    obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective c
    exact realizationComponent_vertex K v

theorem vertexComponents_naturality {K L : SSet.{0}} (f : K ⟶ L) (c : SSet.π₀ K) :
    HomotopyMaps.componentsMap (SSet.toTop.map f).hom (vertexComponents K c) =
      vertexComponents L (SSet.mapπ₀ f c) := by
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective c
  change ZerothHomotopy.mk ((SSet.toTop.map f).hom (vertexPoint K v)) =
    ZerothHomotopy.mk (vertexPoint L (f.app _ v))
  rw [map_vertexPoint]

/-- The component part of the actual weak-equivalence interface is the
usual simplicial component test. -/
theorem components_bijective_iff {K L : SSet.{0}} (f : K ⟶ L) :
    Function.Bijective (HomotopyMaps.componentsMap (SSet.toTop.map f).hom) ↔
      Function.Bijective (SSet.mapπ₀ f) := by
  let eK := realizationComponentsEquiv K
  let eL := realizationComponentsEquiv L
  have hn : HomotopyMaps.componentsMap (SSet.toTop.map f).hom =
      eL.symm ∘ SSet.mapπ₀ f ∘ eK := by
    funext c
    obtain ⟨v, rfl⟩ := eK.symm.surjective c
    change HomotopyMaps.componentsMap (SSet.toTop.map f).hom (eK.symm v) =
      eL.symm (SSet.mapπ₀ f (eK (eK.symm v)))
    rw [eK.apply_symm_apply]
    exact vertexComponents_naturality f v
  rw [hn]
  rw [Function.Bijective.of_comp_iff' eL.symm.bijective,
    Function.Bijective.of_comp_iff _ eK.bijective]

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Degree-zero acyclic lifting for arbitrary Kan fibrations -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Lift a one-simplex of the base from either prescribed endpoint. -/
theorem kan_fibration_lift_edge_face {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] (j : Fin 2) (x : X _⦋0⦌)
    (b : Δ[1] ⟶ Y) (hb : SSet.const x ≫ p = SSet.stdSimplex.δ j ≫ b) :
    ∃ a : Δ[1] ⟶ X, SSet.stdSimplex.δ j ≫ a = SSet.const x ∧ a ≫ p = b := by
  let f : ∀ (k : Fin 2) (_ : k ≠ j.rev), (Δ[0] : SSet.{0}) ⟶ X := fun _ _ => SSet.const x
  have hf : SSet.horn.IsCompatible f := by simp
  have hc : ∀ (k : Fin 2) (hk : k ≠ j.rev), f k hk ≫ p = SSet.stdSimplex.δ k ≫ b := by
    intro k hk
    have hkj : k = j := by fin_cases j <;> fin_cases k <;> simp_all
    subst k
    exact hb
  obtain ⟨a, ha, hap⟩ := hf.exists_lift p b hc
  refine ⟨a, ha j ?_, hap⟩
  fin_cases j <;> decide

/-- The image on vertices of a Kan fibration is closed in both directions
along every edge of the base. -/
theorem kan_fibration_edge_image_iff {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] {y₀ y₁ : Y _⦋0⦌} (e : SSet.Edge y₀ y₁) :
    (∃ x : X _⦋0⦌, p.app _ x = y₀) ↔ (∃ x : X _⦋0⦌, p.app _ x = y₁) := by
  constructor
  · rintro ⟨x, hx⟩
    have hb : SSet.const x ≫ p = SSet.stdSimplex.δ (1 : Fin 2) ≫
        SSet.yonedaEquiv.symm e.edge := by
      rw [SSet.const_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
        e.src_eq, SSet.yonedaEquiv_symm_zero, hx]
    obtain ⟨a, _, ha⟩ := kan_fibration_lift_edge_face p 1 x _ hb
    have h := congrArg SSet.yonedaEquiv ha
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply] at h
    refine ⟨X.δ 0 (SSet.yonedaEquiv a), ?_⟩
    rw [SSet.δ_naturality_apply, h, e.tgt_eq]
  · rintro ⟨x, hx⟩
    have hb : SSet.const x ≫ p = SSet.stdSimplex.δ (0 : Fin 2) ≫
        SSet.yonedaEquiv.symm e.edge := by
      rw [SSet.const_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
        e.tgt_eq, SSet.yonedaEquiv_symm_zero, hx]
    obtain ⟨a, _, ha⟩ := kan_fibration_lift_edge_face p 0 x _ hb
    have h := congrArg SSet.yonedaEquiv ha
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply] at h
    refine ⟨X.δ 1 (SSet.yonedaEquiv a), ?_⟩
    rw [SSet.δ_naturality_apply, h, e.src_eq]

/-- A vertex image is a union of entire simplicial edge components. -/
theorem kan_fibration_zigzag_image_iff {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] {y₀ y₁ : Y _⦋0⦌}
    (h : Relation.EqvGen SSet.π₀Rel y₀ y₁) :
    (∃ x : X _⦋0⦌, p.app _ x = y₀) ↔ (∃ x : X _⦋0⦌, p.app _ x = y₁) := by
  induction h with
  | rel a b h => exact kan_fibration_edge_image_iff p (Classical.choice h)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A Kan fibration surjective on actual realization components is strictly
surjective on vertices. This is the general, non-singular degree-zero case. -/
theorem kan_fibration_vertices_surjective {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p]
    (hp : Function.Surjective (HomotopyMaps.componentsMap (SSet.toTop.map p).hom)) :
    Function.Surjective (p.app (.op (.mk 0))) := by
  have hs := RealizationPrism.simplicial_components_surjective_of_realization p hp
  intro y
  obtain ⟨c, hc⟩ := hs (SSet.π₀.mk y)
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective c
  have h := (SSet.π₀.mk_eq_mk_iff (p.app _ x) y).mp hc
  exact (kan_fibration_zigzag_image_iff p h).mp ⟨x, rfl⟩

/-- An actual realization-weak Kan fibration has the required degree-zero
boundary lifting property, without assuming the higher-dimensional input. -/
theorem acyclic_kan_boundary_zero {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] (hp : realizationWeakEquivalences p) :
    HasLiftingProperty (SSet.boundary 0).ι p := by
  have hs := kan_fibration_vertices_surjective p hp.1.2
  refine ⟨fun {a b} sq => ?_⟩
  obtain ⟨x, hx⟩ := hs (SSet.yonedaEquiv b)
  refine ⟨⟨{ l := SSet.const x, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim (by simpa using z.property)
  · apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_const] using hx

end

end Thomason.Construction

end

section

/-! # Exact composition of edges and compression of Kan edge zigzags -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Two composable edges lift a prescribed base triangle, retaining both
outer edges and the exact middle face over the base. -/
theorem kan_lift_edge_composition {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] {x y z : X _⦋0⦌}
    (u : SSet.Edge x y) (v : SSet.Edge y z) (s : Y _⦋2⦌)
    (h₂ : Y.δ 2 s = p.app _ u.edge) (h₀ : Y.δ 0 s = p.app _ v.edge) :
    ∃ w : SSet.Edge x z, Nonempty (SSet.Edge.CompStruct u v w) ∧
      p.app _ w.edge = Y.δ 1 s := by
  let f : ∀ (j : Fin 3) (_ : j ≠ (1 : Fin 3)), (Δ[1] : SSet.{0}) ⟶ X :=
    fun j _ => if j = 0 then SSet.yonedaEquiv.symm v.edge else SSet.yonedaEquiv.symm u.edge
  have hf : SSet.horn.IsCompatible (i := (1 : Fin 3)) f := by
    rw [SSet.horn.isCompatible_iff]
    intro j k hj hk hjk
    have indices : ∀ a b : Fin 3, a ≠ 1 → b ≠ 1 → a < b → a = 0 ∧ b = 2 := by decide
    obtain ⟨rfl, rfl⟩ := indices j k hj hk hjk
    change SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm v.edge =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm u.edge
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm, v.src_eq, u.tgt_eq]
  have hp : ∀ (j : Fin 3) (hj : j ≠ (1 : Fin 3)),
      f j hj ≫ p = SSet.stdSimplex.δ j ≫ SSet.yonedaEquiv.symm s := by
    intro j hj
    rcases (show j = 0 ∨ j = 2 by fin_cases j <;> norm_num at *) with rfl | rfl
    · simp only [f, ↓reduceIte, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
      apply SSet.yonedaEquiv.injective
      simpa only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply] using h₀.symm
    · simp only [f, show ¬ (2 : Fin 3) = 0 from by decide, ↓reduceIte,
        SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
      apply SSet.yonedaEquiv.injective
      simpa only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply] using h₂.symm
  obtain ⟨a, ha, hap⟩ := hf.exists_lift p (SSet.yonedaEquiv.symm s) hp
  let t := SSet.yonedaEquiv a
  have ht₂ : X.δ 2 t = u.edge := by
    simpa [t, f, SSet.stdSimplex.yonedaEquiv_δ_comp] using
      congrArg SSet.yonedaEquiv (ha 2 (by decide))
  have ht₀ : X.δ 0 t = v.edge := by
    simpa [t, f, SSet.stdSimplex.yonedaEquiv_δ_comp] using
      congrArg SSet.yonedaEquiv (ha 0 (by decide))
  have ht : p.app _ t = s := by
    simpa [t, SSet.yonedaEquiv_comp] using congrArg SSet.yonedaEquiv hap
  refine ⟨SSet.Edge.mk (X.δ 1 t) ?_ ?_, ?_, ?_⟩
  · calc
      _ = X.δ 1 (X.δ 2 t) := (SSet.δ_comp_δ_apply (S := X) (n := 0)
        (i := 1) (j := 1) (by decide) t).symm
      _ = x := by rw [ht₂]; exact u.src_eq
  · calc
      _ = X.δ 0 (X.δ 0 t) := SSet.δ_comp_δ_apply (S := X) (n := 0)
        (i := 0) (j := 0) (by decide) t
      _ = z := by rw [ht₀]; exact v.tgt_eq
  · exact ⟨SSet.Edge.CompStruct.mk t ht₂ ht₀ rfl⟩
  · change p.app _ (X.δ 1 t) = Y.δ 1 s
    rw [SSet.δ_naturality_apply, ht]

/-- The long edge of a lifted triangle lies over its prescribed base edge. -/
theorem kan_compose_edges_over {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] {x y z : X _⦋0⦌}
    (u : SSet.Edge x y) (v : SSet.Edge y z) (s : Y _⦋2⦌)
    (h₂ : Y.δ 2 s = p.app _ u.edge) (h₀ : Y.δ 0 s = p.app _ v.edge) :
    ∃ w : SSet.Edge x z, p.app _ w.edge = Y.δ 1 s := by
  obtain ⟨w, _, hw⟩ := kan_lift_edge_composition p u v s h₂ h₀
  exact ⟨w, hw⟩

/-- Composable edges in a Kan complex have a composition triangle. -/
theorem kan_compose_edges_triangle {X : SSet.{0}} [SSet.KanComplex X]
    {x y z : X _⦋0⦌} (u : SSet.Edge x y) (v : SSet.Edge y z) :
    ∃ w : SSet.Edge x z, Nonempty (SSet.Edge.CompStruct u v w) := by
  have : Subsingleton ((⊤_ SSet.{0}) _⦋1⦌) := ⟨fun s t =>
    SSet.yonedaEquiv.symm.injective (terminal.hom_ext _ _)⟩
  obtain ⟨w, hw, _⟩ := kan_lift_edge_composition (terminal.from X) u v
    (terminal.from X |>.app _ (X.σ 0 (X.σ 0 x))) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  exact ⟨w, hw⟩

/-- Composable edges in a Kan complex can be represented by one edge. -/
theorem kan_compose_edges {X : SSet.{0}} [SSet.KanComplex X]
    {x y z : X _⦋0⦌} (u : SSet.Edge x y) (v : SSet.Edge y z) :
    Nonempty (SSet.Edge x z) := by
  obtain ⟨w, _⟩ := kan_compose_edges_triangle u v
  exact ⟨w⟩

/-- An edge in a Kan complex has an edge in the opposite direction. -/
theorem kan_right_inverse_edge {X : SSet.{0}} [SSet.KanComplex X]
    {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    ∃ e' : SSet.Edge y x, Nonempty (SSet.Edge.CompStruct e e' (SSet.Edge.id x)) := by
  let f : ∀ (j : Fin 3) (_ : j ≠ (0 : Fin 3)), (Δ[1] : SSet.{0}) ⟶ X :=
    fun j _ => if j = 1 then SSet.yonedaEquiv.symm (SSet.Edge.id x).edge
      else SSet.yonedaEquiv.symm e.edge
  have hf : SSet.horn.IsCompatible (i := (0 : Fin 3)) f := by
    rw [SSet.horn.isCompatible_iff]
    intro j k hj hk hjk
    have indices : ∀ a b : Fin 3, a ≠ 0 → b ≠ 0 → a < b → a = 1 ∧ b = 2 := by decide
    obtain ⟨rfl, rfl⟩ := indices j k hj hk hjk
    change SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm (SSet.Edge.id x).edge =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.Edge.src_eq, e.src_eq]
  obtain ⟨a, ha⟩ := hf.exists_lift_of_kanComplex
  let t := SSet.yonedaEquiv a
  have ht₂ : X.δ 2 t = e.edge := by
    simpa [t, f, SSet.stdSimplex.yonedaEquiv_δ_comp] using
      congrArg SSet.yonedaEquiv (ha 2 (by decide))
  have ht₁ : X.δ 1 t = (SSet.Edge.id x).edge := by
    simpa [t, f, SSet.stdSimplex.yonedaEquiv_δ_comp] using
      congrArg SSet.yonedaEquiv (ha 1 (by decide))
  refine ⟨SSet.Edge.mk (X.δ 0 t) ?_ ?_, ?_⟩
  · calc
      _ = X.δ 0 (X.δ 2 t) := (SSet.δ_comp_δ_apply (S := X) (n := 0)
        (i := 0) (j := 1) (by decide) t).symm
      _ = y := by rw [ht₂]; exact e.tgt_eq
  · calc
      _ = X.δ 0 (X.δ 1 t) := (SSet.δ_comp_δ_apply (S := X) (n := 0)
        (i := 0) (j := 0) (by decide) t).symm
      _ = x := by rw [ht₁]; exact (SSet.Edge.id x).tgt_eq

  · exact ⟨SSet.Edge.CompStruct.mk t ht₂ rfl ht₁⟩

/-- An edge in a Kan complex has an edge in the opposite direction. -/
theorem kan_reverse_edge {X : SSet.{0}} [SSet.KanComplex X]
    {x y : X _⦋0⦌} (e : SSet.Edge x y) : Nonempty (SSet.Edge y x) := by
  obtain ⟨e', _⟩ := kan_right_inverse_edge e
  exact ⟨e'⟩

/-- Finite edge zigzags compress to a single directed edge in a Kan complex. -/
theorem kan_edge_of_zigzag {X : SSet.{0}} [SSet.KanComplex X]
    {x y : X _⦋0⦌} (h : Relation.EqvGen SSet.π₀Rel x y) : Nonempty (SSet.Edge x y) := by
  induction h with
  | rel _ _ h => exact h
  | refl x => exact ⟨SSet.Edge.id x⟩
  | symm _ _ _ ih => exact kan_reverse_edge (Classical.choice ih)
  | trans _ _ _ _ _ ih₁ ih₂ =>
    exact kan_compose_edges (Classical.choice ih₁) (Classical.choice ih₂)

/-- Every continuous path between realized vertices of a Kan complex gives
an exact simplicial edge with those endpoints. -/
theorem kan_edge_of_realization_path {X : SSet.{0}} [SSet.KanComplex X]
    {x y : X _⦋0⦌}
    (h : Path (RealizationPrism.vertexPoint X x) (RealizationPrism.vertexPoint X y)) :
    Nonempty (SSet.Edge x y) :=
  kan_edge_of_zigzag (RealizationPrism.edge_zigzag_of_realization_path h)

end

end Thomason.Construction

end

section

/-! # From exact prescribed-endpoint edges to one-boundary lifting -/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- Exact lifting of all edges with both endpoints prescribed is the
one-dimensional boundary lifting property, with the complete boundary map. -/
theorem boundary_one_lifting_of_edges {X Y : SSet.{0}} (p : X ⟶ Y)
    (h : ∀ (x y : X _⦋0⦌) (b : SSet.Edge (p.app _ x) (p.app _ y)),
      ∃ e : SSet.Edge x y, e.map p = b) :
    HasLiftingProperty (SSet.boundary 1).ι p := by
  refine ⟨fun {a c} sq => ?_⟩
  let x := SSet.yonedaEquiv (SSet.boundary.ι (1 : Fin 2) ≫ a)
  let y := SSet.yonedaEquiv (SSet.boundary.ι (0 : Fin 2) ≫ a)
  have hf (j : Fin 2) :
      p.app _ (SSet.yonedaEquiv (SSet.boundary.ι j ≫ a)) =
        Y.δ j (SSet.yonedaEquiv c) := by
    rw [← SSet.yonedaEquiv_comp, Category.assoc, sq.w, ← Category.assoc,
      SSet.boundary.ι_ι, SSet.stdSimplex.yonedaEquiv_δ_comp]
  let b : SSet.Edge (p.app _ x) (p.app _ y) :=
    SSet.Edge.mk (SSet.yonedaEquiv c) (hf 1).symm (hf 0).symm
  obtain ⟨e, he⟩ := h x y b
  refine ⟨⟨{ l := SSet.yonedaEquiv.symm e.edge, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply SSet.boundary.hom_ext
    intro j
    rw [← Category.assoc, SSet.boundary.ι_ι]
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply]
    fin_cases j
    · exact e.tgt_eq
    · exact e.src_eq
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
    exact congrArg SSet.Edge.edge he

end

end Thomason.Construction

end

section

/-! # Exact edge lifting from connected vertex fibres -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- A Kan edge lift can have its final endpoint corrected inside a connected
literal vertex fibre. The base edge remains exactly the prescribed edge. -/
theorem kan_lift_edge_of_fiber_components {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] (x y : X _⦋0⦌)
    (b : SSet.Edge (p.app _ x) (p.app _ y))
    (hc : Function.Injective (HomotopyMaps.componentsMap
      (ContinuousMap.const (SSet.toTop.obj (simplicialPointFiber p (p.app _ y)).toSSet) ()))) :
    ∃ e : SSet.Edge x y, e.map p = b := by
  have hb : SSet.const x ≫ p = SSet.stdSimplex.δ (1 : Fin 2) ≫
      SSet.yonedaEquiv.symm b.edge := by
    rw [SSet.const_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm, b.src_eq,
      SSet.yonedaEquiv_symm_zero]
  obtain ⟨a, ha, hap⟩ := kan_fibration_lift_edge_face p 1 x _ hb
  let z := X.δ 0 (SSet.yonedaEquiv a)
  have ha₁ : X.δ 1 (SSet.yonedaEquiv a) = x := by
    simpa [SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const] using congrArg SSet.yonedaEquiv ha
  let u : SSet.Edge x z := SSet.Edge.mk (SSet.yonedaEquiv a) ha₁ rfl
  have hu : p.app _ u.edge = b.edge := by
    simpa [u, SSet.yonedaEquiv_comp] using congrArg SSet.yonedaEquiv hap
  have hz : p.app _ z = p.app _ y := by
    change p.app _ (X.δ 0 u.edge) = p.app _ y
    rw [SSet.δ_naturality_apply, hu, b.tgt_eq]
  let F := simplicialPointFiber p (p.app _ y)
  have : SSet.KanComplex F.toSSet := simplicialPointFiber_kan p _
  let zF : F.toSSet _⦋0⦌ := ⟨z, by
    change p.app _ z ∈ (SSet.Subcomplex.ofSimplex (p.app _ y)).obj _
    rw [hz]
    exact SSet.Subcomplex.mem_ofSimplex_obj _⟩
  let yF : F.toSSet _⦋0⦌ := ⟨y, SSet.Subcomplex.mem_ofSimplex_obj _⟩
  have he : ZerothHomotopy.mk (RealizationPrism.vertexPoint F.toSSet zF) =
      ZerothHomotopy.mk (RealizationPrism.vertexPoint F.toSSet yF) := hc rfl
  have hj : Joined (RealizationPrism.vertexPoint F.toSSet zF)
      (RealizationPrism.vertexPoint F.toSSet yF) := Quotient.exact he
  obtain ⟨vF⟩ := kan_edge_of_realization_path hj.somePath
  let v : SSet.Edge z y := vF.map F.ι
  have hv : p.app _ v.edge = (SSet.Edge.id (p.app _ y)).edge := by
    change (F.ι ≫ p).app _ vF.edge = _
    rw [simplicialPointFiber_ι_comp]
    have hconst : (SimplexCategory.mk 1).const (SimplexCategory.mk 0) 0 =
        SimplexCategory.σ (0 : Fin 1) := by
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro j
      exact @Subsingleton.elim (Fin 1) inferInstance _ _
    change Y.map ((SimplexCategory.mk 1).const (SimplexCategory.mk 0) 0).op (p.app _ y) =
      Y.map (SimplexCategory.σ (0 : Fin 1)).op (p.app _ y)
    rw [hconst]
  let s := SSet.Edge.CompStruct.compId b
  obtain ⟨e, he⟩ := kan_compose_edges_over p u v s.simplex
    (s.d₂.trans hu.symm) (s.d₀.trans hv.symm)
  exact ⟨e, SSet.Edge.ext (he.trans s.d₁)⟩

end

end Thomason.Construction

end

section

/-! # Exact lifting of entire simplices from a prescribed initial vertex -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

def initialSimplexVertex (n : ℕ) : (Δ[n] : SSet.{0}) _⦋0⦌ :=
  SSet.stdSimplex.objEquiv.symm (RealizationPrism.vertexOperator (0 : Fin (n+1)))

/-- The ordered simplex contracts simplicially to its initial vertex. -/
def simplexInitialContraction (n : ℕ) :
    SSet.Homotopy (SSet.const (initialSimplexVertex n)) (𝟙 (Δ[n] : SSet.{0})) where
  h := {
    app m := ↾fun x => SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
      (orderInterpolate (OrderHom.const _ (0 : Fin (n+1))) OrderHom.id
        (fun _ => Fin.zero_le _) (SSet.stdSimplex.objEquiv x.1).toOrderHom
        (SSet.stdSimplex.objEquiv x.2).toOrderHom))
    naturality m k a := by
      apply ConcreteCategory.hom_ext
      intro x
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro j
      rfl }
  h₀ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    rfl
  h₁ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    rfl
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- A whole simplex of the base lifts from any chosen point over its
initial vertex. This needs only the Kan fibration condition. -/
theorem kan_fibration_simplex_lift {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] (n : ℕ) (b : Δ[n] ⟶ Y) (x : X _⦋0⦌)
    (hx : p.app _ x = b.app _ (initialSimplexVertex n)) :
    ∃ a : Δ[n] ⟶ X, a ≫ p = b := by
  let H := simplexInitialContraction n
  have hf : SSet.const (X := (Δ[n] : SSet.{0})) x ≫ p = SSet.ι₀ ≫ (H.h ≫ b) := by
    rw [← Category.assoc, H.h₀, SSet.const_comp, SSet.const_comp, hx]
  have : HasLiftingProperty (SSet.ι₀ (X := (Δ[n] : SSet.{0}))) p :=
    anodyne_iota_zero _ p (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let sq : CommSq (SSet.const x) SSet.ι₀ p (H.h ≫ b) := ⟨hf⟩
  refine ⟨SSet.ι₁ ≫ sq.lift, ?_⟩
  rw [Category.assoc, sq.fac_right, ← Category.assoc, H.h₁, Category.id_comp]

/-- Surjectivity on the actual realization components makes a Kan
fibration surjective in every simplicial degree. -/
theorem kan_fibration_degree_surjective {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p]
    (hp : Function.Surjective (HomotopyMaps.componentsMap (SSet.toTop.map p).hom)) (n : ℕ) :
    Function.Surjective (p.app (.op (.mk n))) := by
  intro y
  let b : Δ[n] ⟶ Y := SSet.yonedaEquiv.symm y
  obtain ⟨x, hx⟩ := kan_fibration_vertices_surjective p hp (b.app _ (initialSimplexVertex n))
  obtain ⟨a, ha⟩ := kan_fibration_simplex_lift p n b x hx
  refine ⟨SSet.yonedaEquiv a, ?_⟩
  have h := congrArg SSet.yonedaEquiv ha
  simpa only [SSet.yonedaEquiv_comp, b, SSet.yonedaEquiv.apply_symm_apply] using h

/-- In particular, an actual weak Kan fibration is a simplicial epimorphism. -/
theorem acyclic_kan_epi {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] (hp : realizationWeakEquivalences p) : Epi p := by
  rw [NatTrans.epi_iff_epi_app]
  intro d
  obtain ⟨⟨n⟩⟩ := d
  exact (CategoryTheory.epi_iff_surjective _).mpr (kan_fibration_degree_surjective p hp.1.2 n)

end

end Thomason.Construction

end

section

/-! # Canonical paths of realized simplicial edges -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity
open scoped Simplicial

noncomputable section

theorem edge_initial_vertex {X : SSet.{0}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    simplexVertex X e.edge 0 = x := by
  change X.map (vertexOperator (0 : Fin 2)).op e.edge = x
  have h : vertexOperator (0 : Fin 2) = SimplexCategory.δ (1 : Fin 2) := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    fin_cases j
    rfl
  rw [h]
  exact e.src_eq

theorem edge_final_vertex {X : SSet.{0}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    simplexVertex X e.edge 1 = y := by
  change X.map (vertexOperator (1 : Fin 2)).op e.edge = y
  have h : vertexOperator (1 : Fin 2) = SimplexCategory.δ (0 : Fin 2) := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    fin_cases j
    rfl
  rw [h]
  exact e.tgt_eq

/-- The actual linear path inside the geometric one-simplex of an edge. -/
def edgePath {X : SSet.{0}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    Path (vertexPoint X x) (vertexPoint X y) where
  toFun t := simplexPoint X e.edge (StdSimplex.homeomorphI.symm t)
  continuous_toFun := (simplexPoint X e.edge).continuous.comp StdSimplex.homeomorphI.symm.continuous
  source' := by
    rw [StdSimplex.homeomorphI_symm_zero, ← vertexPoint_simplexVertex, edge_initial_vertex]
  target' := by
    rw [StdSimplex.homeomorphI_symm_one, ← vertexPoint_simplexVertex, edge_final_vertex]

/-- Every map of simplicial sets preserves canonical edge paths exactly,
including their parametrization, after the stated endpoint identifications. -/
theorem edgePath_map {X Y : SSet.{0}} (f : X ⟶ Y) {x y : X _⦋0⦌}
    (e : SSet.Edge x y) :
    ((edgePath e).map (SSet.toTop.map f).hom.continuous).cast
      (map_vertexPoint f x).symm (map_vertexPoint f y).symm = edgePath (e.map f) := by
  apply Path.ext
  funext t
  exact simplexPoint_naturality f e.edge _

/-- A degenerate identity edge gives the constant path, not just its
homotopy class. -/
theorem edgePath_id {X : SSet.{0}} (x : X _⦋0⦌) :
    edgePath (SSet.Edge.id x) = Path.refl (vertexPoint X x) := by
  apply Path.ext
  funext t
  change simplexPoint X (X.map (SimplexCategory.σ (0 : Fin 1)).op x)
    (StdSimplex.homeomorphI.symm t) = vertexPoint X x
  rw [simplexPoint_map]
  exact congrArg (simplexPoint X x) (Subsingleton.elim _ _)

end

end Thomason.Construction.RealizationPrism

end

section

/-! # A simplicial triangle realizes the composition relation for edge paths -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity
open scoped Simplicial

noncomputable section

/-- The two sides and the long edge of a simplicial triangle represent the
same actual path-homotopy class, with both endpoints fixed. -/
theorem edgePath_comp_homotopic {X : SSet.{0}} {x y z : X _⦋0⦌}
    {u : SSet.Edge x y} {v : SSet.Edge y z} {w : SSet.Edge x z}
    (s : SSet.Edge.CompStruct u v w) :
    ((edgePath u).trans (edgePath v)).Homotopic (edgePath w) := by
  let a : Path (StdSimplex.single (0 : Fin 3)) (StdSimplex.single 1) :=
    barycentricEdge (SimplexCategory.δ (2 : Fin 3)).toOrderHom
  let b : Path (StdSimplex.single (1 : Fin 3)) (StdSimplex.single 2) :=
    barycentricEdge (SimplexCategory.δ (0 : Fin 3)).toOrderHom
  let c : Path (StdSimplex.single (0 : Fin 3)) (StdSimplex.single 2) :=
    barycentricEdge (SimplexCategory.δ (1 : Fin 3)).toOrderHom
  let f := simplexPoint X s.simplex
  let H := (barycentricPathHomotopy (a.trans b) c).map f
  refine ⟨ContinuousMap.HomotopyRel.cast H ?_ ?_⟩
  · apply ContinuousMap.ext
    intro t
    change f ((a.trans b) t) = ((edgePath u).trans (edgePath v)) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · change simplexPoint X s.simplex (StdSimplex.map
        (SimplexCategory.δ (2 : Fin 3)).toOrderHom _) = simplexPoint X u.edge _
      rw [← simplexPoint_map]
      exact congrArg (fun e => simplexPoint X e _) s.d₂
    · change simplexPoint X s.simplex (StdSimplex.map
        (SimplexCategory.δ (0 : Fin 3)).toOrderHom _) = simplexPoint X v.edge _
      rw [← simplexPoint_map]
      exact congrArg (fun e => simplexPoint X e _) s.d₀
  · apply ContinuousMap.ext
    intro t
    change simplexPoint X s.simplex (StdSimplex.map
      (SimplexCategory.δ (1 : Fin 3)).toOrderHom _) = simplexPoint X w.edge _
    rw [← simplexPoint_map]
    exact congrArg (fun e => simplexPoint X e _) s.d₁

end

end Thomason.Construction.RealizationPrism

end

section

/-! # The actual realization functor on simplicial homotopy categories -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- A simplicial edge is sent to its actual linear path class. The triangle
relation holds by the explicit barycentric relative homotopy. -/
def homotopyCategoryToFundamentalGroupoid (X : SSet.{0}) :
    X.HomotopyCategory ⥤ FundamentalGroupoid (SSet.toTop.obj X) :=
  SSet.Truncated.HomotopyCategory.lift (V := (SSet.truncation 2).obj X)
    (fun x => FundamentalGroupoid.mk (vertexPoint X x))
    (fun e => Path.Homotopic.Quotient.mk (edgePath (SSet.Edge.ofTruncated e)))
    (fun x => congrArg Path.Homotopic.Quotient.mk (edgePath_id (X := X) x))
    (fun s => by
      exact Quotient.sound (edgePath_comp_homotopic (SSet.Edge.CompStruct.ofTruncated s)))

@[simp]
theorem homotopyCategoryToFundamentalGroupoid_obj (X : SSet.{0}) (x : X _⦋0⦌) :
    (homotopyCategoryToFundamentalGroupoid X).obj (SSet.HomotopyCategory.mk x) =
      FundamentalGroupoid.mk (vertexPoint X x) := rfl

@[simp]
theorem homotopyCategoryToFundamentalGroupoid_map {X : SSet.{0}}
    {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (homotopyCategoryToFundamentalGroupoid X).map (SSet.HomotopyCategory.homMk e) =
      Path.Homotopic.Quotient.mk (edgePath e) :=
  Category.id_comp _

/-- Equality of simplicial edge classes implies an actual relative path
homotopy after realization, without any Kan or fibrancy hypothesis. -/
theorem edgePath_homotopic_of_homMk_eq {X : SSet.{0}} {x y : X _⦋0⦌}
    {u v : SSet.Edge x y} (h : SSet.HomotopyCategory.homMk u = SSet.HomotopyCategory.homMk v) :
    (edgePath u).Homotopic (edgePath v) := by
  have h' : Path.Homotopic.Quotient.mk (edgePath u) =
      Path.Homotopic.Quotient.mk (edgePath v) := by
    simpa using congrArg (homotopyCategoryToFundamentalGroupoid X).map h
  exact Path.Homotopic.Quotient.eq.mp h'

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Edge representatives and inverses in the homotopy category of a Kan complex -/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- Every homotopy-category morphism of a Kan complex is represented by a
single edge, retaining the homotopy-category class under composition. -/
theorem kan_homMk_surjective {X : SSet.{0}} [SSet.KanComplex X] (x y : X _⦋0⦌) :
    Function.Surjective (SSet.HomotopyCategory.homMk :
      SSet.Edge x y → (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y)) := by
  have h : ∀ {a b : X.HomotopyCategory} (f : a ⟶ b),
      ∃ e : SSet.Edge a.as.as b.as.as, SSet.HomotopyCategory.homMk e = f := by
    intro a b f
    induction f using SSet.HomotopyCategory.hom_rec with
    | homMk e => exact ⟨e, rfl⟩
    | comp f g hf hg =>
      obtain ⟨u, rfl⟩ := hf
      obtain ⟨v, rfl⟩ := hg
      obtain ⟨w, ⟨s⟩⟩ := kan_compose_edges_triangle u v
      exact ⟨w, (SSet.HomotopyCategory.homMk_comp_homMk s).symm⟩
  exact fun f => h f

/-- A Kan edge becomes an isomorphism with a represented inverse. -/
theorem kan_homMk_isIso {X : SSet.{0}} [SSet.KanComplex X]
    {x y : X _⦋0⦌} (e : SSet.Edge x y) : IsIso (SSet.HomotopyCategory.homMk e) := by
  obtain ⟨v, ⟨s⟩⟩ := kan_right_inverse_edge e
  obtain ⟨w, ⟨t⟩⟩ := kan_right_inverse_edge v
  have he : SSet.HomotopyCategory.homMk e ≫ SSet.HomotopyCategory.homMk v = 𝟙 _ := by
    rw [SSet.HomotopyCategory.homMk_comp_homMk s, SSet.HomotopyCategory.homMk_id]
  have hv : SSet.HomotopyCategory.homMk v ≫ SSet.HomotopyCategory.homMk w = 𝟙 _ := by
    rw [SSet.HomotopyCategory.homMk_comp_homMk t, SSet.HomotopyCategory.homMk_id]
  have hw : SSet.HomotopyCategory.homMk e = SSet.HomotopyCategory.homMk w := by
    calc
      SSet.HomotopyCategory.homMk e = SSet.HomotopyCategory.homMk e ≫
          (SSet.HomotopyCategory.homMk v ≫ SSet.HomotopyCategory.homMk w) := by rw [hv]; simp
      _ = (SSet.HomotopyCategory.homMk e ≫ SSet.HomotopyCategory.homMk v) ≫
          SSet.HomotopyCategory.homMk w := (Category.assoc _ _ _).symm
      _ = SSet.HomotopyCategory.homMk w := by rw [he]; simp
  exact ⟨⟨SSet.HomotopyCategory.homMk v, he, by rw [hw]; exact hv⟩⟩

/-- In a Kan complex, every homotopy-category morphism is invertible. -/
theorem kan_homotopyCategory_isIso {X : SSet.{0}} [SSet.KanComplex X]
    {x y : X.HomotopyCategory} (f : x ⟶ y) : IsIso f := by
  obtain ⟨x, rfl⟩ := SSet.HomotopyCategory.objEquiv.symm.surjective x
  obtain ⟨y, rfl⟩ := SSet.HomotopyCategory.objEquiv.symm.surjective y
  obtain ⟨e, rfl⟩ := kan_homMk_surjective x y f
  exact kan_homMk_isIso e

end

end Thomason.Construction

end

section

/-! # Kan composition retains the actual realized path class -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Exact composition over a prescribed base triangle preserves the whole
realized relative path class of the two lifted edges. -/
theorem kan_compose_realized_edges_over {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] {x y z : X _⦋0⦌}
    (u : SSet.Edge x y) (v : SSet.Edge y z) (s : Y _⦋2⦌)
    (h₂ : Y.δ 2 s = p.app _ u.edge) (h₀ : Y.δ 0 s = p.app _ v.edge) :
    ∃ w : SSet.Edge x z, p.app _ w.edge = Y.δ 1 s ∧
      ((RealizationPrism.edgePath u).trans (RealizationPrism.edgePath v)).Homotopic
        (RealizationPrism.edgePath w) := by
  obtain ⟨w, ⟨t⟩, hw⟩ := kan_lift_edge_composition p u v s h₂ h₀
  exact ⟨w, hw, RealizationPrism.edgePath_comp_homotopic t⟩

/-- The reverse edge furnished by an outer Kan horn is an inverse on actual
path-homotopy classes, not merely an edge with reversed endpoints. -/
theorem kan_realized_right_inverse {X : SSet.{0}} [SSet.KanComplex X]
    {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    ∃ v : SSet.Edge y x,
      ((RealizationPrism.edgePath e).trans (RealizationPrism.edgePath v)).Homotopic
        (Path.refl (RealizationPrism.vertexPoint X x)) := by
  obtain ⟨v, ⟨s⟩⟩ := kan_right_inverse_edge e
  refine ⟨v, ?_⟩
  simpa only [RealizationPrism.edgePath_id] using RealizationPrism.edgePath_comp_homotopic s

/-- Every realized image of a Kan homotopy-category morphism has a single
edge representative in exactly the same actual path-homotopy class. -/
theorem kan_realized_morphism_edge {X : SSet.{0}} [SSet.KanComplex X]
    (x y : X _⦋0⦌) (f : SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) :
    ∃ e : SSet.Edge x y,
      (RealizationPrism.homotopyCategoryToFundamentalGroupoid X).map f =
        Path.Homotopic.Quotient.mk (RealizationPrism.edgePath e) := by
  obtain ⟨e, rfl⟩ := kan_homMk_surjective x y f
  exact ⟨e, RealizationPrism.homotopyCategoryToFundamentalGroupoid_map e⟩

end

end Thomason.Construction

end

end OAI
