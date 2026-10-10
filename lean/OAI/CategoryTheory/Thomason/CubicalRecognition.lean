import Mathlib
import OAI.CategoryTheory.Thomason.CubicalGeometry

namespace OAI

/-! Cubical Recognition. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

def top_homotopy_rel_pre {A : Type u} {B : Type v} {X : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    {a b : C(A,X)} {S : Set A} (H : a.HomotopyRel b S)
    (f : C(B,A)) (T : Set B) (hf : ∀ x ∈ T, f x ∈ S) :
    (a.comp f).HomotopyRel (b.comp f) T where
  toHomotopy := H.toHomotopy.compContinuousMap f
  prop' := fun t x hx => H.prop t (f x) (hf x hx)

lemma cubical_relative_cancel {A : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (e : A ≃ₜ (Fin (n+1) → unitInterval)) (S : Set A)
    (hS : ∀ a, a ∈ S ↔ e a ∈ Cube.boundary (Fin (n+1)))
    (r : C(X,Y)) (hr : WeakHomotopy.Equivalence r) (x : X)
    (f g : C(A,X)) (hf : ∀ a ∈ S, f a = x) (hg : ∀ a ∈ S, g a = x)
    (H : (r.comp f).HomotopyRel (r.comp g) S) :
    Nonempty (f.HomotopyRel g S) := by
  let f' : GenLoop (Fin (n+1)) X x := ⟨f.comp ⟨e.symm,e.symm.continuous⟩,by
    intro a ha
    exact hf _ ((hS _).mpr (by simpa using ha))⟩
  let g' : GenLoop (Fin (n+1)) X x := ⟨g.comp ⟨e.symm,e.symm.continuous⟩,by
    intro a ha
    exact hg _ ((hS _).mpr (by simpa using ha))⟩
  have hfg : WeakHomotopy.groupMap (Fin (n+1)) r x ⟦f'⟧ =
      WeakHomotopy.groupMap (Fin (n+1)) r x ⟦g'⟧ := by
    apply Quotient.sound
    exact ⟨top_homotopy_rel_pre H ⟨e.symm,e.symm.continuous⟩ (Cube.boundary (Fin (n+1)))
      (fun a ha => (hS _).mpr (by simpa using ha))⟩
  obtain ⟨G⟩ : GenLoop.Homotopic f' g' := Quotient.exact ((hr.2 n x).1 hfg)
  have hh := top_homotopy_rel_pre G ⟨e,e.continuous⟩ S (fun a ha => (hS a).mp ha)
  refine ⟨hh.cast ?_ ?_⟩ <;> ext a <;> simp [f',g']

structure CubicalPair (P B : PartOrd.{u}) (i : B →o P) (n : ℕ) where
  home : PolyPoint P ≃ₜ (Fin (n+1) → unitInterval)
  boundary : ∀ a, a ∈ Set.range (map i (preservesChains_monotone i)) ↔
    home a ∈ Cube.boundary (Fin (n+1))

def CubicalPair.refine {P B : PartOrd.{u}} {i : B →o P} {n : ℕ}
    (c : CubicalPair P B i n) (d : PairRefinement P B i) : CubicalPair d.R d.S d.j n where
  home := d.home.trans c.home
  boundary := by
    intro a
    change _ ↔ c.home (d.home a) ∈ _
    rw [← c.boundary]
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨d.homeB b,(d.natural b).symm⟩
    · rintro ⟨b,hb⟩
      obtain ⟨b',rfl⟩ := d.homeB.surjective b
      refine ⟨b',d.home.injective ?_⟩
      exact (d.natural b').trans hb
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma polyToRealization_natural {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (i : P →o Q) (x : PolyPoint P) :
    SSet.toTop.map (nerveMap i.toFunctor) (polyToRealization x) =
      polyToRealization (map i (preservesChains_monotone i) x) := by
  apply (nerveRealizationHomeomorph (P := Q)).injective
  rw [nerveRealizationHomeomorph_natural]
  change map i _ (realizationToPoly P (polyToRealization x)) =
    realizationToPoly Q (polyToRealization (map i _ x))
  rw [realizationToPoly_polyToRealization,realizationToPoly_polyToRealization]

def polyRealize {P : Type u} [PartialOrder P] {K : SSet.{u}} (a : nerve P ⟶ K) :
    C(PolyPoint P,SSet.toTop.obj K) := (realizeMap a).comp polyToRealizationHom.hom

lemma polyRealize_post {P : Type u} [PartialOrder P] {K L : SSet.{u}}
    (a : nerve P ⟶ K) (r : K ⟶ L) :
    polyRealize (a ≫ r) = (realizeMap r).comp (polyRealize a) := by
  rw [polyRealize,realizeMap_comp,ContinuousMap.comp_assoc]
  rfl

lemma polyRealize_pre {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (i : P →o Q) {K : SSet.{u}} (a : nerve Q ⟶ K) :
    polyRealize (nerveMap i.toFunctor ≫ a) = (polyRealize a).comp (affineMap i) := by
  ext x
  change (SSet.toTop.map (nerveMap i.toFunctor ≫ a)) (polyToRealization x) = _
  rw [Functor.map_comp]
  change SSet.toTop.map a (SSet.toTop.map (nerveMap i.toFunctor) (polyToRealization x)) = _
  rw [polyToRealization_natural]
  rfl

lemma polyRealize_order {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (i : P →o Q) : polyRealize (nerveMap i.toFunctor) =
      polyToRealizationHom.hom.comp (affineMap i) := by
  ext x
  exact polyToRealization_natural i x

lemma poly_realization_homotopy_rel {P B : Type u} [PartialOrder P] [PartialOrder B]
    (i : B →o P) (hi : Function.Injective i) {K : SSet.{u}}
    (z : nerve B ⟶ K) {a b : nerve P ⟶ K}
    (H : BasedHomotopy (nerveMap i.toFunctor) z a b) :
    Nonempty ((polyRealize a).HomotopyRel (polyRealize b)
      (Set.range (map i (preservesChains_monotone i)))) := by
  let : Mono (nerveMap i.toFunctor) := nerveOrderMap_mono i hi
  obtain ⟨G,hG⟩ := H
  have hb := (based_homotopy_boundary _ _ ⟨G,hG⟩).2
  obtain ⟨F⟩ := realization_homotopy_rel (nerveMap i.toFunctor) G
    (by rw [hb]; exact hG)
  refine ⟨top_homotopy_rel_pre F polyToRealizationHom.hom _ ?_⟩
  rintro x ⟨y,rfl⟩
  exact ⟨polyToRealization y,polyToRealization_natural i y⟩

lemma map_constantOrder {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (q : Q) (x : PolyPoint P) :
    map (constantOrder P q) (preservesChains_monotone (constantOrder P q)) x = vertex q := by
  classical
  apply PolyPoint.ext
  ext y
  rw [map_apply]
  change (x.weights.sum fun _ value => if q = y then value else 0) = Finsupp.single q 1 y
  by_cases hy : q = y
  · subst y
    simpa only [ite_true,Finsupp.single_eq_same]
      using x.total
  · simp [hy]

lemma polyRealize_constant {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (q : Q) (x : PolyPoint P) :
    polyRealize (nerveMap (constantOrder P q).toFunctor) x = polyToRealization (vertex q) := by
  rw [polyRealize_order]
  change polyToRealization (map (constantOrder P q) (preservesChains_monotone _) x) = _
  rw [map_constantOrder]

lemma geometric_relative_order_cancel (P B : PartOrd.{u}) (i : B →o P)
    (n : ℕ) (c : CubicalPair P B i n) (Q : PartOrd.{u}) (q : Q)
    (f g : P →o Q) (hf : f.comp i = constantOrder B q) (hg : g.comp i = constantOrder B q)
    {K : SSet.{u}} (r : nerve Q ⟶ K) (hr : simplicialWeakEquivalences r)
    (H : (polyRealize (nerveMap f.toFunctor ≫ r)).HomotopyRel
      (polyRealize (nerveMap g.toFunctor ≫ r)) (Set.range (map i (preservesChains_monotone i)))) :
    ∃ G : (affineMap f).Homotopy (affineMap g),
      ∀ (t : unitInterval) (x : PolyPoint B), G (t,map i (preservesChains_monotone i) x) = vertex q := by
  have hbound (a : P →o Q) (ha : a.comp i = constantOrder B q) :
      ∀ x ∈ Set.range (map i (preservesChains_monotone i)),
        polyRealize (nerveMap a.toFunctor) x = polyToRealization (vertex q) := by
    rintro x ⟨y,rfl⟩
    have hh := congrArg (fun F : C(PolyPoint B,SSet.toTop.obj (nerve Q)) => F y)
      (polyRealize_pre i (nerveMap a.toFunctor))
    rw [← nerveOrderMap_comp,ha] at hh
    exact hh.symm.trans (polyRealize_constant q y)
  obtain ⟨G⟩ := cubical_relative_cancel n c.home _ c.boundary
    (realizeMap r) hr (polyToRealization (vertex q))
    (polyRealize (nerveMap f.toFunctor)) (polyRealize (nerveMap g.toFunctor))
    (hbound f hf) (hbound g hg) (by simpa only [polyRealize_post] using H)
  have he (a : P →o Q) : (realizationToPoly Q).hom.comp (polyRealize (nerveMap a.toFunctor)) =
      affineMap a := by
    rw [polyRealize_order]
    apply ContinuousMap.ext
    intro x
    exact realizationToPoly_polyToRealization (map a (preservesChains_monotone a) x)
  let G' := (G.compContinuousMap (realizationToPoly Q).hom).cast (he f) (he g)
  refine ⟨G'.toHomotopy,?_⟩
  intro t x
  have hh := G'.prop t _ ⟨x,rfl⟩
  change G' (t, map i (preservesChains_monotone i) x) = vertex q
  change G' (t, map i (preservesChains_monotone i) x) = _ at hh
  rw [hh]
  change map f (preservesChains_monotone f) (map i (preservesChains_monotone i) x) = vertex q
  have hm : map f (preservesChains_monotone f) (map i (preservesChains_monotone i) x) =
      map (f.comp i) (preservesChains_monotone (f.comp i)) x :=
    PolyPoint.ext Finsupp.mapDomain_comp.symm
  rw [hm,hf,map_constantOrder]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma poly_rel_pre_pair {P B R S : PartOrd.{u}} (i : B →o P) (j : S →o R)
    (l : R →o P) (k : S →o B) (w : l.comp j = i.comp k)
    {K : SSet.{u}} {a b : nerve P ⟶ K}
    (H : (polyRealize a).HomotopyRel (polyRealize b)
      (Set.range (map i (preservesChains_monotone i)))) :
    Nonempty ((polyRealize (nerveMap l.toFunctor ≫ a)).HomotopyRel
      (polyRealize (nerveMap l.toFunctor ≫ b))
      (Set.range (map j (preservesChains_monotone j)))) := by
  rw [polyRealize_pre,polyRealize_pre]
  refine ⟨top_homotopy_rel_pre H (affineMap l) _ ?_⟩
  rintro x ⟨y,rfl⟩
  refine ⟨map k (preservesChains_monotone k) y,?_⟩
  change map i (preservesChains_monotone i) (map k (preservesChains_monotone k) y) = map l (preservesChains_monotone l) (map j (preservesChains_monotone j) y)
  have h₁ : map i (preservesChains_monotone i) (map k (preservesChains_monotone k) y) = map (i.comp k) (preservesChains_monotone _) y :=
    PolyPoint.ext Finsupp.mapDomain_comp.symm
  have h₂ : map l (preservesChains_monotone l) (map j (preservesChains_monotone j) y) = map (l.comp j) (preservesChains_monotone _) y :=
    PolyPoint.ext Finsupp.mapDomain_comp.symm
  rw [h₁,h₂,w]

lemma pair_refinement_cancel {P B : PartOrd.{u}} (i : B →o P) (hi : Function.Injective i)
    (d : PairRefinement P B i) {K : SSet.{u}} [SSet.KanComplex K]
    (z : nerve B ⟶ K) {a b : nerve P ⟶ K}
    (ha : nerveMap i.toFunctor ≫ a = z) (hb : nerveMap i.toFunctor ≫ b = z)
    (H : BasedHomotopy (nerveMap d.j.toFunctor) (nerveMap d.k.toFunctor ≫ z)
      (nerveMap d.l.toFunctor ≫ a) (nerveMap d.l.toFunctor ≫ b)) :
    BasedHomotopy (nerveMap i.toFunctor) z a b := by
  let : Mono (nerveMap i.toFunctor) := nerveOrderMap_mono i hi
  let : Mono (nerveMap d.j.toFunctor) := nerveOrderMap_mono d.j d.injective
  obtain ⟨H,hH⟩ := H
  exact pair_local_injective_plain _ _ _ _
    (by rw [← nerveOrderMap_comp,← nerveOrderMap_comp,d.square])
    d.local_l d.local_k z a b ha hb H (by simpa only [Category.assoc] using hH)

lemma finite_cubical_realization_faithful (P B : PartOrd.{u}) [Finite P] [Finite B]
    (i : B →o P) (hi : Function.Injective i) (n : ℕ) (c : CubicalPair P B i n)
    {K : SSet.{u}} [SSet.KanComplex K] (x : K _⦋0⦌)
    (a b : nerve P ⟶ K) (ha : nerveMap i.toFunctor ≫ a = SSet.const x)
    (hb : nerveMap i.toFunctor ≫ b = SSet.const x)
    (H : (polyRealize a).HomotopyRel (polyRealize b)
      (Set.range (map i (preservesChains_monotone i)))) :
    BasedHomotopy (nerveMap i.toFunctor) (SSet.const x) a b := by
  obtain ⟨Q,q,r,e,hre,hr,he,hx⟩ := pointed_kan_ex_replacement K x
  obtain ⟨d₁,a₁,ha₁,H₁⟩ := finite_pair_order_representative Q q r e he hre P B i hi a
    (by rw [hx]; exact ha)
  have hb₁ : nerveMap d₁.j.toFunctor ≫ nerveMap d₁.l.toFunctor ≫ b =
      nerveMap (constantOrder d₁.S q).toFunctor ≫ r := by
    rw [← Category.assoc,← nerveOrderMap_comp,d₁.square,nerveOrderMap_comp,
      Category.assoc,hb,hx,SSet.comp_const]
  obtain ⟨d₂,b₂,hb₂,H₂⟩ := finite_pair_order_representative Q q r e he hre
    d₁.R d₁.S d₁.j d₁.injective (nerveMap d₁.l.toFunctor ≫ b) hb₁
  let a₂ : d₂.R →o Q := a₁.comp d₂.l
  have ha₂ : a₂.comp d₂.j = constantOrder d₂.S q := by
    dsimp [a₂]
    rw [OrderHom.comp_assoc,d₂.square,← OrderHom.comp_assoc,ha₁,constantOrder_comp]
  have H₁' := based_homotopy_pre (nerveMap d₁.j.toFunctor) (nerveMap d₂.j.toFunctor)
    (nerveMap d₂.l.toFunctor) (nerveMap d₂.k.toFunctor)
    (by rw [← nerveOrderMap_comp,← nerveOrderMap_comp,d₂.square]) _ H₁
  simp only [nerve_constant_pre'_assoc] at H₁'
  obtain ⟨G₁⟩ := poly_realization_homotopy_rel d₂.j d₂.injective _ H₁'
  obtain ⟨G₂⟩ := poly_realization_homotopy_rel d₂.j d₂.injective _ H₂
  obtain ⟨H'⟩ := poly_rel_pre_pair i d₁.j d₁.l d₁.k d₁.square H
  obtain ⟨H''⟩ := poly_rel_pre_pair d₁.j d₂.j d₂.l d₂.k d₂.square H'
  have HH : (polyRealize (nerveMap a₂.toFunctor ≫ r)).HomotopyRel
      (polyRealize (nerveMap b₂.toFunctor ≫ r))
      (Set.range (map d₂.j (preservesChains_monotone d₂.j))) := by
    have hhh := (G₁.symm.trans H'').trans G₂
    simpa only [a₂,nerveOrderMap_comp,Category.assoc] using hhh
  obtain ⟨G,hG⟩ := geometric_relative_order_cancel d₂.R d₂.S d₂.j n
    ((c.refine d₁).refine d₂) Q q a₂ b₂ ha₂ hb₂ r hr HH
  have H₃ := pair_relative_nerve_descent d₂.R d₂.S d₂.j d₂.injective q a₂ b₂
    ha₂ hb₂ G hG K r
  have H₃' : BasedHomotopy (nerveMap d₂.j.toFunctor)
      (nerveMap (constantOrder d₂.S q).toFunctor ≫ r)
      (nerveMap d₂.l.toFunctor ≫ nerveMap a₁.toFunctor ≫ r)
      (nerveMap b₂.toFunctor ≫ r) := by
    simpa only [a₂,nerveOrderMap_comp,Category.assoc] using H₃
  let : Mono (nerveMap d₂.j.toFunctor) := nerveOrderMap_mono d₂.j d₂.injective
  have H₄ := based_homotopy_trans _ _
    (based_homotopy_trans _ _ H₁' H₃') (based_homotopy_symm _ _ H₂)
  have hax₁ : nerveMap d₁.j.toFunctor ≫ nerveMap d₁.l.toFunctor ≫ a = SSet.const x := by
    rw [← Category.assoc,← nerveOrderMap_comp,d₁.square,nerveOrderMap_comp,
      Category.assoc,ha,SSet.comp_const]
  have hbx₁ : nerveMap d₁.j.toFunctor ≫ nerveMap d₁.l.toFunctor ≫ b = SSet.const x := by
    rw [hb₁,hx]
  have H₅ := pair_refinement_cancel d₁.j d₁.injective d₂ (SSet.const x) hax₁ hbx₁
    (by simpa only [hx,SSet.comp_const] using H₄)
  exact pair_refinement_cancel i hi d₁ (SSet.const x) ha hb
    (by simpa only [SSet.comp_const] using H₅)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma realize_const_apply {A K : SSet.{u}} (x : K _⦋0⦌) (a : SSet.toTop.obj A) :
    realizeMap (SSet.const x) a = KanQuillen.realVertex x := by
  let p : A ⟶ (Δ[0] : SSet.{u}) := SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)
  have h : p ≫ SSet.yonedaEquiv.symm x = SSet.const x := by
    rw [SSet.yonedaEquiv_symm_zero,SSet.comp_const]
  rw [← h,realizeMap_comp]
  change SSet.toTop.map (SSet.yonedaEquiv.symm x) (SSet.toTop.map p a) =
    SSet.toTop.map (SSet.yonedaEquiv.symm x) default
  congr 1
  exact Subsingleton.elim _ _

lemma polyRealize_const {P : Type u} [PartialOrder P] {K : SSet.{u}}
    (x : K _⦋0⦌) (a : PolyPoint P) :
    polyRealize (SSet.const x) a = KanQuillen.realVertex x := realize_const_apply x _

lemma weak_cubical_injective (P B : PartOrd.{u}) [Finite P] [Finite B]
    (i : B →o P) (hi : Function.Injective i) (n : ℕ) (c : CubicalPair P B i n)
    {K L : SSet.{u}} [SSet.KanComplex K] (r : K ⟶ L) (hr : simplicialWeakEquivalences r)
    (x : K _⦋0⦌) (a b : nerve P ⟶ K)
    (ha : nerveMap i.toFunctor ≫ a = SSet.const x)
    (hb : nerveMap i.toFunctor ≫ b = SSet.const x)
    (H : BasedHomotopy (nerveMap i.toFunctor) (SSet.const (r.app _ x)) (a ≫ r) (b ≫ r)) :
    BasedHomotopy (nerveMap i.toFunctor) (SSet.const x) a b := by
  obtain ⟨G⟩ := poly_realization_homotopy_rel i hi _ H
  have boundary (f : nerve P ⟶ K) (hf : nerveMap i.toFunctor ≫ f = SSet.const x) :
      ∀ y ∈ Set.range (map i (preservesChains_monotone i)), polyRealize f y =
        KanQuillen.realVertex x := by
    rintro y ⟨z,rfl⟩
    have hh := congrArg (fun F : C(PolyPoint B,SSet.toTop.obj K) => F z) (polyRealize_pre i f)
    rw [hf] at hh
    exact hh.symm.trans (polyRealize_const x z)
  obtain ⟨G'⟩ := cubical_relative_cancel n c.home _ c.boundary (realizeMap r) hr
    (KanQuillen.realVertex x) (polyRealize a) (polyRealize b) (boundary a ha) (boundary b hb)
    (by simpa only [polyRealize_post] using G)
  exact finite_cubical_realization_faithful P B i hi n c x a b ha hb G'
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma cubical_relative_surject {A : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (e : A ≃ₜ (Fin (n+1) → unitInterval)) (S : Set A)
    (hS : ∀ a, a ∈ S ↔ e a ∈ Cube.boundary (Fin (n+1)))
    (r : C(X,Y)) (hr : WeakHomotopy.Equivalence r) (x : X)
    (f : C(A,Y)) (hf : ∀ a ∈ S, f a = r x) :
    ∃ g : C(A,X), (∀ a ∈ S, g a = x) ∧ Nonempty ((r.comp g).HomotopyRel f S) := by
  let f' : GenLoop (Fin (n+1)) Y (r x) := ⟨f.comp ⟨e.symm,e.symm.continuous⟩,by
    intro a ha
    exact hf _ ((hS _).mpr (by simpa using ha))⟩
  obtain ⟨g,hg⟩ := (hr.2 n x).2 ⟦f'⟧
  obtain ⟨g,rfl⟩ := Quotient.mk_surjective g
  obtain ⟨G⟩ : GenLoop.Homotopic (WeakHomotopy.loopMap (Fin (n+1)) r x g) f' := Quotient.exact hg
  let g' := g.val.comp ⟨e,e.continuous⟩
  refine ⟨g',fun a ha => g.property _ ((hS a).mp ha),?_⟩
  have hh := top_homotopy_rel_pre G ⟨e,e.continuous⟩ S (fun a ha => (hS a).mp ha)
  refine ⟨hh.cast ?_ ?_⟩ <;> ext a <;> simp [g',f',WeakHomotopy.loopMap]

lemma poly_realize_boundary {P B : PartOrd.{u}} (i : B →o P) {K : SSet.{u}}
    (x : K _⦋0⦌) (a : nerve P ⟶ K) (ha : nerveMap i.toFunctor ≫ a = SSet.const x) :
    ∀ y ∈ Set.range (map i (preservesChains_monotone i)), polyRealize a y =
      KanQuillen.realVertex x := by
  rintro y ⟨z,rfl⟩
  have hh := congrArg (fun F : C(PolyPoint B,SSet.toTop.obj K) => F z) (polyRealize_pre i a)
  rw [ha] at hh
  exact hh.symm.trans (polyRealize_const x z)

lemma pointed_replacement_real_vertex {Q : Type u} [PartialOrder Q] (q : Q)
    {K : SSet.{u}} (r : nerve Q ⟶ K) (x : K _⦋0⦌)
    (hx : nerveMap (constantOrder Q q).toFunctor ≫ r = SSet.const x) :
    realizeMap r (polyToRealization (vertex q)) = KanQuillen.realVertex x := by
  have hh := congrArg (fun F : C(PolyPoint Q,SSet.toTop.obj K) => F (vertex q))
    (polyRealize_post (nerveMap (constantOrder Q q).toFunctor) r)
  rw [hx] at hh
  change polyRealize (SSet.const x) (vertex q) =
    realizeMap r (polyRealize (nerveMap (constantOrder Q q).toFunctor) (vertex q)) at hh
  rw [polyRealize_const,polyRealize_constant] at hh
  exact hh.symm

lemma last_barycentric_realization_rel (P : PartOrd.{u}) [Finite P] (B : Set P)
    (n : ℕ) {K : SSet.{u}} (x : K _⦋0⦌) (a : nerve P ⟶ K)
    (ha : nerveMap (inclusion B).toFunctor ≫ a = SSet.const x) :
    Nonempty ((polyRealize (nerveMap (last P n).toFunctor ≫ a)).HomotopyRel
      ((polyRealize a).comp ⟨levelHomeomorph P n,(levelHomeomorph P n).continuous⟩)
      (Set.range (map (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n)
        (preservesChains_monotone _)))) := by
  rw [polyRealize_pre]
  refine ⟨{ toHomotopy := (ContinuousMap.Homotopy.refl (polyRealize a)).comp (lastBarycentricHomotopy P n)
            prop' := ?_ }⟩
  rintro t y ⟨z,rfl⟩
  obtain ⟨v,hv⟩ := lastBarycentricHomotopy_pair P B n t z
  have hb := poly_realize_boundary (P := P) (B := PartOrd.of B) (inclusion B) x a ha
  change polyRealize a (lastBarycentricHomotopy P n (t,_)) =
    polyRealize a (map (last P n) (preservesChains_monotone _) _)
  rw [← hv,hb _ ⟨v,rfl⟩]
  symm
  apply hb
  refine ⟨map (last (PartOrd.of B) n) (preservesChains_monotone _) z,?_⟩
  have h₁ : map (inclusion B) (preservesChains_monotone _) (map (last (PartOrd.of B) n) (preservesChains_monotone _) z) =
      map ((inclusion B).comp (last (PartOrd.of B) n)) (preservesChains_monotone _) z :=
    PolyPoint.ext Finsupp.mapDomain_comp.symm
  have h₂ : map (last P n) (preservesChains_monotone _) (map (levelMap (inclusion B) n) (preservesChains_monotone _) z) =
      map ((last P n).comp (levelMap (inclusion B) n)) (preservesChains_monotone _) z :=
    PolyPoint.ext Finsupp.mapDomain_comp.symm
  rw [h₁,h₂,last_natural]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma full_pair_home_boundary (P : PartOrd.{u}) [Finite P] (B : Set P) (n : ℕ)
    (y : PolyPoint P) (hy : y ∈ Set.range (map (inclusion B) (preservesChains_monotone _))) :
    (levelHomeomorph P n).symm y ∈ Set.range
      (map (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) n) (preservesChains_monotone _)) := by
  obtain ⟨z,rfl⟩ := hy
  refine ⟨(levelHomeomorph (PartOrd.of B) n).symm z,?_⟩
  apply (levelHomeomorph P n).injective
  rw [(levelHomeomorph P n).apply_symm_apply,levelHomeomorph_natural _ Subtype.val_injective,
    (levelHomeomorph (PartOrd.of B) n).apply_symm_apply]

lemma finite_cubical_geometric_representative (P : PartOrd.{u}) [Finite P] (B : Set P)
    (n : ℕ) (c : CubicalPair P (PartOrd.of B) (inclusion B) n)
    {K : SSet.{u}} [SSet.KanComplex K] (x : K _⦋0⦌)
    (f : C(PolyPoint P,SSet.toTop.obj K))
    (hf : ∀ y ∈ Set.range (map (inclusion B) (preservesChains_monotone _)),
      f y = KanQuillen.realVertex x) :
    ∃ b : nerve P ⟶ K, nerveMap (inclusion B).toFunctor ≫ b = SSet.const x ∧
      Nonempty ((polyRealize b).HomotopyRel f
        (Set.range (map (inclusion B) (preservesChains_monotone _)))) := by
  obtain ⟨Q,q,r,hr,hw,hx⟩ := pointed_kan_poset_replacement K x
  have hv := pointed_replacement_real_vertex q r x (hx Q)
  obtain ⟨g,hg,⟨G⟩⟩ := cubical_relative_surject n c.home _ c.boundary (realizeMap r) hw
    (polyToRealization (vertex q)) f (by simpa only [hv] using hf)
  let g' : C(PolyPoint P,PolyPoint Q) := (realizationToPoly Q).hom.comp g
  have hg' (y : PolyPoint B) : g' (map (inclusion B) (preservesChains_monotone _) y) = vertex q := by
    change realizationToPoly Q (g _) = _
    rw [hg _ ⟨y,rfl⟩,realizationToPoly_polyToRealization]
  obtain ⟨m,a,H,ha,hH⟩ := pair_geometric_approximation P B q g' hg'
  have hab : nerveMap (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) m).toFunctor ≫
      nerveMap a.toFunctor ≫ r =
        nerveMap (last (PartOrd.of B) m).toFunctor ≫ SSet.const x := by
    rw [← Category.assoc,← nerveOrderMap_comp,ha]
    exact (hx _).trans (SSet.comp_const _ _).symm
  obtain ⟨b,D,hb,hD⟩ := descend_pair_approximation P B m K (SSet.const x)
    (nerveMap a.toFunctor ≫ r) hab
  have hD' : BasedHomotopy (nerveMap (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) m).toFunctor)
      (SSet.const x) (nerveMap (last P m).toFunctor ≫ b) (nerveMap a.toFunctor ≫ r) :=
    ⟨D,by simpa only [SSet.comp_const] using hD⟩
  obtain ⟨D'⟩ := poly_realization_homotopy_rel
    (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) m)
    (levelMap_injective _ Subtype.val_injective m) _ hD'
  obtain ⟨L⟩ := last_barycentric_realization_rel P B m x b hb
  let H' : (polyRealize (nerveMap a.toFunctor ≫ r)).HomotopyRel
      (((realizeMap r).comp g).comp ⟨levelHomeomorph P m,(levelHomeomorph P m).continuous⟩)
      (Set.range (map (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) m)
        (preservesChains_monotone _))) := by
    have he : ((realizeMap r).comp polyToRealizationHom.hom).comp
        (g'.comp ⟨levelHomeomorph P m,(levelHomeomorph P m).continuous⟩) =
        ((realizeMap r).comp g).comp ⟨levelHomeomorph P m,(levelHomeomorph P m).continuous⟩ := by
      ext y
      change realizeMap r (polyToRealization (realizationToPoly Q (g _))) = _
      rw [polyToRealization_realizationToPoly]
      rfl
    refine { toHomotopy := ((ContinuousMap.Homotopy.refl
      ((realizeMap r).comp polyToRealizationHom.hom)).comp H).cast ?_ he
             prop' := ?_ }
    · rw [polyRealize_post,polyRealize_order,ContinuousMap.comp_assoc]
    · rintro t y ⟨z,rfl⟩
      change realizeMap r (polyToRealization (H (t,_))) = polyRealize (nerveMap a.toFunctor ≫ r) _
      rw [hH]
      have hh := poly_realize_boundary
        (P := level P m) (B := level (PartOrd.of B) m)
        (levelMap (inclusion B) m) x (nerveMap a.toFunctor ≫ r)
        (by simpa only [SSet.comp_const] using hab)
      exact hv.trans (hh _ ⟨z,rfl⟩).symm
  let G' := top_homotopy_rel_pre G
    ⟨levelHomeomorph P m,(levelHomeomorph P m).continuous⟩
    (Set.range (map (levelMap (P := PartOrd.of B) (Q := P) (inclusion B) m)
      (preservesChains_monotone _))) (by
      rintro y ⟨z,rfl⟩
      exact ⟨levelHomeomorph (PartOrd.of B) m z, (levelHomeomorph_natural _ Subtype.val_injective m z).symm⟩)
  let F := ((L.symm.trans D').trans H').trans G'
  have F' := top_homotopy_rel_pre F
    ⟨(levelHomeomorph P m).symm,(levelHomeomorph P m).symm.continuous⟩ _
    (full_pair_home_boundary P B m)
  refine ⟨b,hb,⟨F'.cast ?_ ?_⟩⟩ <;> ext y <;>
    simp only [ContinuousMap.comp_apply,ContinuousMap.coe_mk,Homeomorph.apply_symm_apply]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma realVertex_natural {K L : SSet.{u}} (r : K ⟶ L) (x : K _⦋0⦌) :
    realizeMap r (KanQuillen.realVertex x) = KanQuillen.realVertex (r.app _ x) := by
  change SSet.toTop.map r (SSet.toTop.map (SSet.yonedaEquiv.symm x) default) = _
  rw [← TopCat.comp_app,← Functor.map_comp,SSet.yonedaEquiv_symm_comp]
  rfl

lemma weak_cubical_surjective (P : PartOrd.{u}) [Finite P] (B : Set P)
    (n : ℕ) (c : CubicalPair P (PartOrd.of B) (inclusion B) n)
    {K L : SSet.{u}} [SSet.KanComplex K] [SSet.KanComplex L]
    (r : K ⟶ L) (hr : simplicialWeakEquivalences r) (x : K _⦋0⦌)
    (a : nerve P ⟶ L) (ha : nerveMap (inclusion B).toFunctor ≫ a = SSet.const (r.app _ x)) :
    ∃ b : nerve P ⟶ K, nerveMap (inclusion B).toFunctor ≫ b = SSet.const x ∧
      BasedHomotopy (nerveMap (inclusion B).toFunctor) (SSet.const (r.app _ x)) (b ≫ r) a := by
  have hf := poly_realize_boundary (P := P) (B := PartOrd.of B) (inclusion B) (r.app _ x) a ha
  obtain ⟨g,hg,⟨G⟩⟩ := cubical_relative_surject n c.home _ c.boundary (realizeMap r) hr
    (KanQuillen.realVertex x) (polyRealize a) (by simpa only [realVertex_natural] using hf)
  obtain ⟨b,hb,⟨H⟩⟩ := finite_cubical_geometric_representative P B n c x g hg
  refine ⟨b,hb,finite_cubical_realization_faithful P (PartOrd.of B) (inclusion B)
    Subtype.val_injective n c (r.app _ x) (b ≫ r) a ?_ ha ?_⟩
  · rw [← Category.assoc,hb,SSet.const_comp]
  · have F := (H.compContinuousMap (realizeMap r)).trans G
    exact F.cast (polyRealize_post b r).symm rfl
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

abbrev cubePoset (n : ℕ) : PartOrd.{u} :=
  PartOrd.of (NonemptyFiniteChains (Finset (ULift.{u} (Fin (n+1)))))

abbrev cubeBoundary (n : ℕ) : Set (cubePoset.{u} n) :=
  Cubical.boundaryFaces (ULift.{u} (Fin (n+1)))

abbrev cubeBoundaryInclusion (n : ℕ) : PartOrd.of (cubeBoundary.{u} n) →o cubePoset.{u} n :=
  inclusion (cubeBoundary n)

def actualCubicalPair (n : ℕ) :
    CubicalPair (cubePoset.{u} n) (PartOrd.of (cubeBoundary n)) (cubeBoundaryInclusion n) n where
  home := Cubical.pairCubeHomeomorph.trans
    (Homeomorph.piCongrLeft (Y := fun _ : Fin (n+1) => unitInterval) Equiv.ulift)
  boundary := by
    intro a
    have he : (Cubical.pairCubeHomeomorph (I := ULift.{u} (Fin (n+1)))) a ∈
        Cube.boundary (ULift.{u} (Fin (n+1))) ↔
      (Homeomorph.piCongrLeft (Y := fun _ : Fin (n+1) => unitInterval) Equiv.ulift)
        (Cubical.pairCubeHomeomorph a) ∈ Cube.boundary (Fin (n+1)) := by
      constructor
      · rintro ⟨j,hj⟩
        exact ⟨j.down,hj⟩
      · rintro ⟨j,hj⟩
        exact ⟨ULift.up j,hj⟩
    change _ ↔ (Homeomorph.piCongrLeft (Y := fun _ : Fin (n+1) => unitInterval) Equiv.ulift)
      (Cubical.pairCubeHomeomorph a) ∈ Cube.boundary (Fin (n+1))
    rw [← he]
    constructor
    · rintro ⟨b,rfl⟩
      exact (Cubical.boundaryHomeomorph b).property
    · intro ha
      obtain ⟨b,hb⟩ := Cubical.boundaryHomeomorph.surjective ⟨_,ha⟩
      exact ⟨b,Cubical.pairCubeHomeomorph.injective (congrArg Subtype.val hb)⟩

abbrev CubeMap (n : ℕ) {K : SSet.{u}} (x : K _⦋0⦌) :=
  {a : nerve (cubePoset.{u} n) ⟶ K //
    nerveMap (cubeBoundaryInclusion n).toFunctor ≫ a = SSet.const x}

instance cubeBoundary_mono (n : ℕ) : Mono (nerveMap (cubeBoundaryInclusion.{u} n).toFunctor) :=
  nerveOrderMap_mono _ Subtype.val_injective

def cubeMapSetoid (n : ℕ) {K : SSet.{u}} [SSet.KanComplex K] (x : K _⦋0⦌) :
    Setoid (CubeMap n x) where
  r a b := BasedHomotopy (nerveMap (cubeBoundaryInclusion n).toFunctor) (SSet.const x) a.val b.val
  iseqv := {
    refl := fun a => based_homotopy_refl _ _ a.val a.property
    symm := fun h => based_homotopy_symm _ _ h
    trans := fun h h' => based_homotopy_trans _ _ h h' }

abbrev CubeClasses (n : ℕ) {K : SSet.{u}} [SSet.KanComplex K] (x : K _⦋0⦌) :=
  Quotient (cubeMapSetoid n x)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

def realizeCubeMap (n : ℕ) {K : SSet.{u}} (x : K _⦋0⦌) (a : CubeMap n x) :
    GenLoop (Fin (n+1)) (SSet.toTop.obj K) (KanQuillen.realVertex x) :=
  ⟨(polyRealize a.val).comp ⟨(actualCubicalPair n).home.symm,(actualCubicalPair n).home.symm.continuous⟩,by
    intro y hy
    exact poly_realize_boundary (P := cubePoset n) (B := PartOrd.of (cubeBoundary n))
      (cubeBoundaryInclusion n) x a.val a.property _
      ((actualCubicalPair n).boundary _ |>.mpr (by simpa using hy))⟩

lemma realizeCubeMap_homotopic (n : ℕ) {K : SSet.{u}} (x : K _⦋0⦌)
    {a b : CubeMap n x}
    (H : BasedHomotopy (nerveMap (cubeBoundaryInclusion n).toFunctor) (SSet.const x) a.val b.val) :
    GenLoop.Homotopic (realizeCubeMap n x a) (realizeCubeMap n x b) := by
  obtain ⟨G⟩ := poly_realization_homotopy_rel (cubeBoundaryInclusion n) Subtype.val_injective _ H
  exact ⟨top_homotopy_rel_pre G
    ⟨(actualCubicalPair n).home.symm,(actualCubicalPair n).home.symm.continuous⟩
    (Cube.boundary (Fin (n+1))) (fun y hy =>
      ((actualCubicalPair n).boundary _).mpr (by simpa using hy))⟩

def realizeCubeClasses (n : ℕ) {K : SSet.{u}} [SSet.KanComplex K] (x : K _⦋0⦌) :
    CubeClasses n x → HomotopyGroup (Fin (n+1)) (SSet.toTop.obj K) (KanQuillen.realVertex x) :=
  Quotient.map (realizeCubeMap n x) (fun _ _ h => realizeCubeMap_homotopic n x h)

theorem positive_realization_comparison (n : ℕ) {K : SSet.{u}} [SSet.KanComplex K]
    (x : K _⦋0⦌) : Function.Bijective (realizeCubeClasses n x) := by
  constructor
  · intro a b hab
    obtain ⟨a,rfl⟩ := Quotient.mk_surjective a
    obtain ⟨b,rfl⟩ := Quotient.mk_surjective b
    obtain ⟨H⟩ : GenLoop.Homotopic (realizeCubeMap n x a) (realizeCubeMap n x b) := Quotient.exact hab
    have G := top_homotopy_rel_pre H
      ⟨(actualCubicalPair n).home,(actualCubicalPair n).home.continuous⟩
      (Set.range (map (cubeBoundaryInclusion n) (preservesChains_monotone _)))
      (fun y hy => ((actualCubicalPair n).boundary y).mp hy)
    have G' : (polyRealize a.val).HomotopyRel (polyRealize b.val)
        (Set.range (map (cubeBoundaryInclusion n) (preservesChains_monotone _))) :=
      G.cast (by ext y; simp [realizeCubeMap]) (by ext y; simp [realizeCubeMap])
    exact Quotient.sound (finite_cubical_realization_faithful _ _ _ Subtype.val_injective
      n (actualCubicalPair n) x a.val b.val a.property b.property G')
  · intro a
    obtain ⟨a,rfl⟩ := Quotient.mk_surjective a
    let f := a.val.comp ⟨(actualCubicalPair n).home,(actualCubicalPair n).home.continuous⟩
    have hf : ∀ y ∈ Set.range (map (cubeBoundaryInclusion n) (preservesChains_monotone _)),
        f y = KanQuillen.realVertex x := fun y hy => a.property _ (((actualCubicalPair n).boundary y).mp hy)
    obtain ⟨b,hb,⟨H⟩⟩ := finite_cubical_geometric_representative (cubePoset n) (cubeBoundary n)
      n (actualCubicalPair n) x f hf
    refine ⟨⟦⟨b,hb⟩⟧,Quotient.sound ⟨?_⟩⟩
    have G := top_homotopy_rel_pre H
      ⟨(actualCubicalPair n).home.symm,(actualCubicalPair n).home.symm.continuous⟩
      (Cube.boundary (Fin (n+1))) (fun y hy =>
        ((actualCubicalPair n).boundary _).mpr (by simpa using hy))
    exact G.cast rfl (by ext y; simp [f])
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

def cubeMapPost (n : ℕ) {K L : SSet.{u}} (r : K ⟶ L) (x : K _⦋0⦌)
    (a : CubeMap n x) : CubeMap n (r.app _ x) :=
  ⟨a.val ≫ r,by rw [← Category.assoc,a.property,SSet.const_comp]⟩

def cubeClassesMap (n : ℕ) {K L : SSet.{u}} [SSet.KanComplex K] [SSet.KanComplex L]
    (r : K ⟶ L) (x : K _⦋0⦌) : CubeClasses n x → CubeClasses n (r.app _ x) :=
  Quotient.map (cubeMapPost n r x) (fun a b h => by
    change BasedHomotopy _ _ (a.val ≫ r) (b.val ≫ r)
    simpa only [SSet.const_comp] using based_homotopy_post _ _ h r)

theorem weak_positive_classes_bijective (n : ℕ) {K L : SSet.{u}}
    [SSet.KanComplex K] [SSet.KanComplex L] (r : K ⟶ L)
    (hr : simplicialWeakEquivalences r) (x : K _⦋0⦌) :
    Function.Bijective (cubeClassesMap n r x) := by
  constructor
  · intro a b hab
    obtain ⟨a,rfl⟩ := Quotient.mk_surjective a
    obtain ⟨b,rfl⟩ := Quotient.mk_surjective b
    have H : BasedHomotopy (nerveMap (cubeBoundaryInclusion n).toFunctor)
        (SSet.const (r.app _ x)) (a.val ≫ r) (b.val ≫ r) := Quotient.exact hab
    exact Quotient.sound (weak_cubical_injective _ _ _ Subtype.val_injective n
      (actualCubicalPair n) r hr x a.val b.val a.property b.property H)
  · intro a
    obtain ⟨a,rfl⟩ := Quotient.mk_surjective a
    obtain ⟨b,hb,H⟩ := weak_cubical_surjective (cubePoset n) (cubeBoundary n) n
      (actualCubicalPair n) r hr x a.val a.property
    exact ⟨⟦⟨b,hb⟩⟧,Quotient.sound H⟩
end Thomason.GeometricRecognition

end

end OAI
