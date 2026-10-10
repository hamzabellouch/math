import Mathlib
import OAI.CategoryTheory.Thomason.SubdivisionMaps

namespace OAI

/-! Subdivision Nerves. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

noncomputable def initialFlag (n : SimplexCategory) :
    SimplexCategory.toPartOrd.obj n →o
      NonemptyFiniteChains (SimplexCategory.toPartOrd.obj n) := by
  classical
  letI : Fintype (SimplexCategory.toPartOrd.obj n) :=
    inferInstanceAs (Fintype (ULift (Fin (n.len+1))))
  letI : LinearOrder (SimplexCategory.toPartOrd.obj n) :=
    inferInstanceAs (LinearOrder (ULift (Fin (n.len+1))))
  exact {
    toFun := fun i => {
      finset := Finset.univ.filter (· ≤ i)
      nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩⟩
      comparable := fun a b => le_total a.val b.val }
    monotone' := fun i j h k hk => by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans (Finset.mem_filter.mp hk).2 h⟩ }

lemma chainLast_initialFlag (n : SimplexCategory) (i : SimplexCategory.toPartOrd.obj n) :
    chainLast (initialFlag n i) = i := by
  classical
  let _ : Fintype (SimplexCategory.toPartOrd.obj n) :=
    inferInstanceAs (Fintype (ULift (Fin (n.len+1))))
  let _ : LinearOrder (SimplexCategory.toPartOrd.obj n) :=
    inferInstanceAs (LinearOrder (ULift (Fin (n.len+1))))
  apply le_antisymm
  · have h := chainGreatest_mem (initialFlag n i)
    exact (Finset.mem_filter.mp h).2
  · exact le_chainGreatest (initialFlag n i)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩)

noncomputable def simplexLastVertexSection (n : SimplexCategory) :
    SSet.stdSimplex.obj n ⟶ SimplexCategory.sd.obj n :=
  simplexNerveIso.hom.app n ≫ PartOrd.nerveFunctor.map (PartOrd.ofHom (initialFlag n))

lemma simplexLastVertexSection_comp (n : SimplexCategory) :
    simplexLastVertexSection n ≫ simplexLastVertex.app n = 𝟙 _ := by
  have h : PartOrd.ofHom (initialFlag n) ≫ chainLastNat.app (SimplexCategory.toPartOrd.obj n) =
      𝟙 _ := by
    apply PartOrd.hom_ext
    apply OrderHom.ext
    funext i
    exact chainLast_initialFlag n i
  change (simplexNerveIso.hom.app n ≫ PartOrd.nerveFunctor.map _) ≫
    (PartOrd.nerveFunctor.map _ ≫ simplexNerveIso.inv.app n) = _
  have hh := congrArg PartOrd.nerveFunctor.map h
  have hh' : PartOrd.nerveFunctor.map (PartOrd.ofHom (initialFlag n)) ≫
      PartOrd.nerveFunctor.map (chainLastNat.app (SimplexCategory.toPartOrd.obj n)) = 𝟙 _ := by
    exact (PartOrd.nerveFunctor.map_comp _ _).symm.trans
      (hh.trans (PartOrd.nerveFunctor.map_id _))
  calc
    _ = simplexNerveIso.hom.app n ≫
        (PartOrd.nerveFunctor.map (PartOrd.ofHom (initialFlag n)) ≫
        PartOrd.nerveFunctor.map (chainLastNat.app (SimplexCategory.toPartOrd.obj n))) ≫
        simplexNerveIso.inv.app n := by simp only [Category.assoc]; rfl
    _ = _ := by erw [hh', Category.id_comp]; exact simplexNerveIso.hom_inv_id_app n

noncomputable def lastVertexSection (n : SimplexCategory) :
    SSet.stdSimplex.obj n ⟶ SSet.sd.obj (SSet.stdSimplex.obj n) :=
  simplexLastVertexSection n ≫ (SSet.stdSimplex.sdIso.app n).inv

lemma lastVertexSection_comp (n : SimplexCategory) :
    lastVertexSection n ≫ lastVertex.app (SSet.stdSimplex.obj n) = 𝟙 _ := by
  rw [lastVertexSection, lastVertex_stdSimplex, Category.assoc,
    ← Category.assoc (SSet.stdSimplex.sdIso.app n).inv,
    Iso.inv_hom_id, Category.id_comp, simplexLastVertexSection_comp]

instance exComparison_mono (X : SSet.{u}) : Mono (exComparison.app X) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro k
  rw [CategoryTheory.mono_iff_injective]
  intro a b hab
  let f : SSet.stdSimplex.obj k.unop ⟶ X := SSet.yonedaEquiv.symm a
  let g : SSet.stdSimplex.obj k.unop ⟶ X := SSet.yonedaEquiv.symm b
  have he : f ≫ exComparison.app X = g ≫ exComparison.app X := by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, f, g, Equiv.apply_symm_apply] using hab
  have hm : lastVertex.app (SSet.stdSimplex.obj k.unop) ≫ f =
      lastVertex.app (SSet.stdSimplex.obj k.unop) ≫ g := by
    apply (SSet.sdExAdjunction.homEquiv _ X).injective
    rw [SSet.sdExAdjunction.homEquiv_naturality_right,
      SSet.sdExAdjunction.homEquiv_naturality_right]
    change exComparison.app (SSet.stdSimplex.obj k.unop) ≫ SSet.ex.map f =
      exComparison.app (SSet.stdSimplex.obj k.unop) ≫ SSet.ex.map g
    rw [← exComparison.naturality f, ← exComparison.naturality g]
    exact he
  have hfg : f = g := by
    have h := congrArg (fun t => lastVertexSection k.unop ≫ t) hm
    simpa only [← Category.assoc, lastVertexSection_comp, Category.id_comp] using h
  simpa only [f, g, Equiv.apply_symm_apply] using congrArg SSet.yonedaEquiv hfg

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

variable {E : Type u} [PartialOrder E]

noncomputable def simplexChain {n : ℕ} (s : (nerve E) _⦋n⦌) :
    NonemptyFiniteChains E := by
  classical
  exact {
    finset := Finset.univ.image s.obj
    nonempty := ⟨s.obj 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
    comparable := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
      rcases le_total i j with h | h
      · exact Or.inl (s.monotone h)
      · exact Or.inr (s.monotone h) }

lemma mem_simplexChain {n : ℕ} (s : (nerve E) _⦋n⦌) (x : E) :
    x ∈ (simplexChain s).finset ↔ ∃ i, s.obj i = x := by
  classical
  simp [simplexChain]

lemma simplexChain_le_iff (s t : (nerve E).N) :
    simplexChain s.simplex ≤ simplexChain t.simplex ↔ s ≤ t := by
  constructor
  · intro h
    have ht := (mem_nerve_nonDegenerate_iff_strictMono t.simplex).mp t.nonDegenerate
    have hs := (mem_nerve_nonDegenerate_iff_strictMono s.simplex).mp s.nonDegenerate
    have hex (i : Fin (s.dim+1)) : ∃ j, t.simplex.obj j = s.simplex.obj i :=
      (mem_simplexChain _ _).mp (h ((mem_simplexChain _ _).mpr ⟨i, rfl⟩))
    let f : Fin (s.dim+1) →o Fin (t.dim+1) := {
      toFun i := (hex i).choose
      monotone' := by
        intro i j hij
        apply ht.le_iff_le.mp
        rw [(hex i).choose_spec, (hex j).choose_spec]
        exact hs.monotone hij }
    let φ : ⦋s.dim⦌ ⟶ ⦋t.dim⦌ := SimplexCategory.mkHom f
    have hm : Mono φ := by
      apply SimplexCategory.mono_iff_injective.mpr
      intro i j hij
      apply hs.injective
      exact ((hex i).choose_spec).symm.trans
        ((congrArg t.simplex.obj hij).trans (hex j).choose_spec)
    apply SSet.N.le_iff_exists_mono.mpr
    refine ⟨φ, hm, ?_⟩
    apply nerve.ext_of_isThin
    funext i
    exact (hex i).choose_spec
  · intro h x hx
    obtain ⟨φ, _, he⟩ := SSet.N.le_iff_exists_mono.mp h
    obtain ⟨i, rfl⟩ := (mem_simplexChain _ _).mp hx
    apply (mem_simplexChain _ _).mpr
    refine ⟨φ i, ?_⟩
    exact congrArg (fun q => q.obj i) he

noncomputable def chainSimplex (s : NonemptyFiniteChains E) : (nerve E).N := by
  classical
  let _ : LinearOrder s.finset := Relation.linearOrderOfSymmGen s.comparable
  let n := s.finset.card - 1
  have hc : Fintype.card s.finset = n+1 := by
    rw [Fintype.card_coe]
    dsimp [n]
    exact (Nat.sub_add_cancel (Finset.card_pos.mpr s.nonempty)).symm
  let e : Fin (n+1) ≃o s.finset := Fintype.orderIsoFinOfCardEq s.finset hc
  let f : Fin (n+1) →o E := {
    toFun i := (e i).val
    monotone' := fun _ _ h => e.monotone h }
  exact SSet.N.mk f.monotone.functor
    ((mem_nerve_nonDegenerate_iff_strictMono _).mpr
      (fun _ _ h => e.strictMono h))

lemma simplexChain_chainSimplex (s : NonemptyFiniteChains E) :
    simplexChain (chainSimplex s).simplex = s := by
  classical
  let _ : LinearOrder s.finset := Relation.linearOrderOfSymmGen s.comparable
  apply NonemptyFiniteChains.ext
  ext x
  rw [mem_simplexChain]
  dsimp [chainSimplex]
  constructor
  · rintro ⟨i, rfl⟩
    exact (Fintype.orderIsoFinOfCardEq s.finset _ i).property
  · intro hx
    exact ⟨(Fintype.orderIsoFinOfCardEq s.finset _).symm ⟨x, hx⟩,
      congrArg Subtype.val ((Fintype.orderIsoFinOfCardEq s.finset _).apply_symm_apply _)⟩

noncomputable def nerveNondegenerateChains : (nerve E).N ≃o NonemptyFiniteChains E where
  toFun s := simplexChain s.simplex
  invFun := chainSimplex
  left_inv s := by
    apply le_antisymm
    · apply (simplexChain_le_iff _ _).mp
      rw [simplexChain_chainSimplex]
    · apply (simplexChain_le_iff _ _).mp
      rw [simplexChain_chainSimplex]
  right_inv := simplexChain_chainSimplex
  map_rel_iff' := simplexChain_le_iff _ _

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {E : Type u} [PartialOrder E]

lemma chains_map_injective {A : Type v} [PartialOrder A] (f : A →o E)
    (hf : Function.Injective f) : Function.Injective (NonemptyFiniteChains.orderHomMap f) := by
  classical
  intro s t h
  apply NonemptyFiniteChains.ext
  exact Finset.image_injective hf (congrArg NonemptyFiniteChains.finset h)

lemma chains_map_le_iff {A : Type v} [PartialOrder A] (f : A →o E)
    (hf : Function.Injective f) (s t : NonemptyFiniteChains A) :
    s.map f ≤ t.map f ↔ s ≤ t := by
  constructor
  · intro h a ha
    obtain ⟨b, hb, he⟩ := (NonemptyFiniteChains.mem_map_iff t f _).mp
      (h ((NonemptyFiniteChains.mem_map_iff s f _).mpr ⟨a, ha, rfl⟩))
    exact hf he ▸ hb
  · intro h; exact (NonemptyFiniteChains.orderHomMap f).monotone h

lemma chains_map_surjective_on {A : Type v} [PartialOrder A] (f : A ↪o E)
    (s : NonemptyFiniteChains E) (hs : ∀ x ∈ s.finset, ∃ a, f a = x) :
    ∃ t : NonemptyFiniteChains A, t.map f.toOrderHom = s := by
  classical
  let g (x : s.finset) : A := (hs x.val x.property).choose
  have hg (x : s.finset) : f (g x) = x := (hs x.val x.property).choose_spec
  let t : NonemptyFiniteChains A := {
    finset := s.finset.attach.image g
    nonempty := by
      obtain ⟨x, hx⟩ := s.nonempty
      exact ⟨g ⟨x,hx⟩, Finset.mem_image.mpr ⟨⟨x,hx⟩, Finset.mem_attach _ _, rfl⟩⟩
    comparable := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
      rcases s.comparable x y with h | h
      · left; apply f.le_iff_le.mp; simpa only [hg] using (show x.val ≤ y.val from h)
      · right; apply f.le_iff_le.mp; simpa only [hg] using (show y.val ≤ x.val from h) }
  refine ⟨t, NonemptyFiniteChains.ext ?_⟩
  ext x
  rw [NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp ha
    simpa only [OrderEmbedding.toOrderHom_coe, hg] using y.property
  · intro hx
    refine ⟨g ⟨x,hx⟩, Finset.mem_image.mpr ⟨⟨x,hx⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    exact hg ⟨x,hx⟩

def simplexVertices {n : ℕ} (s : (nerve E) _⦋n⦌) :
    SimplexCategory.toPartOrd.obj ⦋n⦌ →o E where
  toFun i := s.obj i.down
  monotone' _ _ h := s.monotone h

lemma simplexVertices_injective (s : (nerve E).N) :
    Function.Injective (simplexVertices s.simplex) := by
  intro i j h
  apply ULift.ext
  exact ((mem_nerve_nonDegenerate_iff_injective _).mp s.nonDegenerate) h

noncomputable def simplexVerticesEmbedding (s : (nerve E).N) :
    SimplexCategory.toPartOrd.obj ⦋s.dim⦌ ↪o E where
  toFun := simplexVertices s.simplex
  inj' := simplexVertices_injective s
  map_rel_iff' := by
    intro i j
    exact ((mem_nerve_nonDegenerate_iff_strictMono _).mp s.nonDegenerate).le_iff_le

noncomputable def sdNerveLeg (s : (nerve E).N) :
    SimplexCategory.sd.obj ⦋s.dim⦌ ⟶ nerve (NonemptyFiniteChains E) :=
  PartOrd.nerveFunctor.map (PartOrd.ofHom
    (NonemptyFiniteChains.orderHomMap (simplexVertices s.simplex)))

lemma sdNerveLeg_mono (s : (nerve E).N) : Mono (sdNerveLeg s) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro k
  rw [CategoryTheory.mono_iff_injective]
  intro x y h
  apply nerve.ext_of_isThin
  funext i
  exact chains_map_injective _ (simplexVertices_injective s)
    (congrArg (fun q => q.obj i) h)

lemma sdNerveLeg_naturality {s t : (nerve E).N} (h : s ≤ t) :
    SimplexCategory.sd.map (SSet.N.monoOfLE h) ≫ sdNerveLeg t = sdNerveLeg s := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply nerve.ext_of_isThin
  funext j
  apply NonemptyFiniteChains.ext
  classical
  change Finset.image _ (Finset.image _ _) = Finset.image _ _
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i hi
  exact congrArg (fun q => q.obj i.down) (SSet.N.map_monoOfLE h)

noncomputable def sdNerveCocone :
    Cocone ((nerve E).functorN' ⋙ SSet.sd) where
  pt := nerve (NonemptyFiniteChains E)
  ι.app s := (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom ≫ sdNerveLeg s
  ι.naturality s t f := by
    change SSet.sd.map (SSet.stdSimplex.map (SSet.N.monoOfLE (leOfHom f))) ≫
      ((SSet.stdSimplex.sdIso.app _).hom ≫ sdNerveLeg t) = _
    simp only [Functor.const_obj_map]
    erw [← Category.assoc, SSet.stdSimplex.sdIso.hom.naturality,
      Category.assoc, sdNerveLeg_naturality]
    exact (Category.comp_id _).symm

noncomputable def sdNerveMap :
    SSet.sd.obj (nerve E) ⟶ nerve (NonemptyFiniteChains E) :=
  (isColimitOfPreserves SSet.sd (nerve E).isColimitCoconeN').desc sdNerveCocone

lemma sdNerveMap_fac (s : (nerve E).N) :
    SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫ sdNerveMap =
      (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom ≫ sdNerveLeg s :=
  (isColimitOfPreserves SSet.sd (nerve E).isColimitCoconeN').fac sdNerveCocone s

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {E : Type u} [PartialOrder E]

noncomputable def sdNerveInjection (s : (nerve E).N) :
    SimplexCategory.sd.obj ⦋s.dim⦌ ⟶ SSet.sd.obj (nerve E) :=
  (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).inv ≫
    SSet.sd.map (SSet.yonedaEquiv.symm s.simplex)

lemma sdNerveInjection_comp (s : (nerve E).N) :
    sdNerveInjection s ≫ sdNerveMap = sdNerveLeg s := by
  rw [sdNerveInjection, Category.assoc, sdNerveMap_fac,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma sdNerveInjection_naturality {s t : (nerve E).N} (h : s ≤ t) :
    SimplexCategory.sd.map (SSet.N.monoOfLE h) ≫ sdNerveInjection t =
      sdNerveInjection s := by
  unfold sdNerveInjection
  erw [← Category.assoc, SSet.stdSimplex.sdIso.inv.naturality,
    Category.assoc, ← SSet.sd.map_comp,
    SSet.N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex]
  rfl

lemma sdNerveInjection_jointly_surjective (k : SimplexCategoryᵒᵖ)
    (z : (SSet.sd.obj (nerve E)).obj k) :
    ∃ (s : (nerve E).N) (x : (SimplexCategory.sd.obj ⦋s.dim⦌).obj k),
      (sdNerveInjection s).app k x = z := by
  have hc := isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj k)
    (isColimitOfPreserves SSet.sd (nerve E).isColimitCoconeN')
  obtain ⟨s, x, hx⟩ := Types.jointly_surjective_of_isColimit hc z
  refine ⟨s, (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom.app k x, ?_⟩
  change (SSet.sd.map (SSet.yonedaEquiv.symm s.simplex)).app k
    ((SSet.stdSimplex.sdIso.app ⦋s.dim⦌).inv.app k
      ((SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom.app k x)) = z
  have he := congrArg (fun f => f.app k x) (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom_inv_id
  change (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).inv.app k
      ((SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom.app k x) = x at he
  rw [he]
  exact hx

lemma sdNerveLeg_app_injective (s : (nerve E).N) (k : SimplexCategoryᵒᵖ) :
    Function.Injective ((sdNerveLeg s).app k) := by
  intro x y h
  apply nerve.ext_of_isThin
  funext i
  exact chains_map_injective _ (simplexVertices_injective s)
    (congrArg (fun q => q.obj i) h)

lemma sdNerveLeg_obj_le (s : (nerve E).N) (k : SimplexCategoryᵒᵖ)
    (x : (SimplexCategory.sd.obj ⦋s.dim⦌).obj k) (j : Fin (k.unop.len+1)) :
    ((sdNerveLeg s).app k x).obj j ≤ simplexChain s.simplex := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp ha
  exact (mem_simplexChain _ _).mpr ⟨i.down, rfl⟩

lemma sdNerveLeg_surjective_on (s : (nerve E).N) (k : SimplexCategoryᵒᵖ)
    (q : (nerve (NonemptyFiniteChains E)).obj k)
    (h : ∀ i, q.obj i ≤ simplexChain s.simplex) :
    ∃ p : (SimplexCategory.sd.obj ⦋s.dim⦌).obj k, (sdNerveLeg s).app k p = q := by
  have hex (i : Fin (k.unop.len+1)) :
      ∃ p : NonemptyFiniteChains (SimplexCategory.toPartOrd.obj ⦋s.dim⦌),
        p.map (simplexVertices s.simplex) = q.obj i := by
    apply chains_map_surjective_on (simplexVerticesEmbedding s)
    intro x hx
    obtain ⟨j, hj⟩ := (mem_simplexChain _ _).mp (h i hx)
    exact ⟨ULift.up j, hj⟩
  let f : Fin (k.unop.len+1) →o
      NonemptyFiniteChains (SimplexCategory.toPartOrd.obj ⦋s.dim⦌) := {
    toFun i := (hex i).choose
    monotone' := by
      intro i j hij
      apply (chains_map_le_iff (simplexVertices s.simplex) (simplexVertices_injective s) _ _).mp
      rw [(hex i).choose_spec, (hex j).choose_spec]
      exact q.monotone hij }
  refine ⟨f.monotone.functor, ?_⟩
  apply nerve.ext_of_isThin
  funext i
  exact (hex i).choose_spec

lemma sdNerveMap_app_surjective (k : SimplexCategoryᵒᵖ) :
    Function.Surjective ((sdNerveMap (E := E)).app k) := by
  intro q
  let s := chainSimplex (q.obj (Fin.last k.unop.len))
  have h (i) : q.obj i ≤ simplexChain s.simplex := by
    rw [simplexChain_chainSimplex]
    exact q.monotone (Fin.le_last i)
  obtain ⟨p, hp⟩ := sdNerveLeg_surjective_on s k q h
  refine ⟨(sdNerveInjection s).app k p, ?_⟩
  exact (congrArg (fun f => f.app k p) (sdNerveInjection_comp s)).trans hp

lemma sdNerveMap_app_injective (k : SimplexCategoryᵒᵖ) :
    Function.Injective ((sdNerveMap (E := E)).app k) := by
  intro x y hxy
  obtain ⟨s, p, rfl⟩ := sdNerveInjection_jointly_surjective k x
  obtain ⟨t, q, rfl⟩ := sdNerveInjection_jointly_surjective k y
  have hs := congrArg (fun f => f.app k p) (sdNerveInjection_comp s)
  have ht := congrArg (fun f => f.app k q) (sdNerveInjection_comp t)
  have he : (sdNerveLeg s).app k p = (sdNerveLeg t).app k q := hs.symm.trans (hxy.trans ht)
  let v := (sdNerveLeg s).app k p
  let a := chainSimplex (v.obj (Fin.last k.unop.len))
  have has : a ≤ s := by
    apply (simplexChain_le_iff _ _).mp
    rw [simplexChain_chainSimplex]
    exact sdNerveLeg_obj_le s k p _
  have hat : a ≤ t := by
    apply (simplexChain_le_iff _ _).mp
    rw [simplexChain_chainSimplex]
    dsimp only [v]
    rw [he]
    exact sdNerveLeg_obj_le t k q _
  obtain ⟨r, hr⟩ := sdNerveLeg_surjective_on a k v (fun i => by
    rw [simplexChain_chainSimplex]
    exact v.monotone (Fin.le_last i))
  have hps : (SimplexCategory.sd.map (SSet.N.monoOfLE has)).app k r = p := by
    apply sdNerveLeg_app_injective s k
    exact (congrArg (fun f => f.app k r) (sdNerveLeg_naturality has)).trans hr
  have hqt : (SimplexCategory.sd.map (SSet.N.monoOfLE hat)).app k r = q := by
    apply sdNerveLeg_app_injective t k
    exact (congrArg (fun f => f.app k r) (sdNerveLeg_naturality hat)).trans (hr.trans he)
  rw [← hps, ← hqt]
  exact (congrArg (fun f => f.app k r) (sdNerveInjection_naturality has)).trans
    (congrArg (fun f => f.app k r) (sdNerveInjection_naturality hat)).symm

instance sdNerveMap_isIso : IsIso (sdNerveMap (E := E)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro k
  exact (CategoryTheory.isIso_iff_bijective _).mpr
    ⟨sdNerveMap_app_injective k, sdNerveMap_app_surjective k⟩

noncomputable def sdNerveIso : SSet.sd.obj (nerve E) ≅ nerve (NonemptyFiniteChains E) :=
  asIso sdNerveMap

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {E : Type u} {F : Type u} [PartialOrder E] [PartialOrder F]

noncomputable def sdNerveSimplexLeg {n : ℕ} (s : (nerve E) _⦋n⦌) :
    SimplexCategory.sd.obj ⦋n⦌ ⟶ nerve (NonemptyFiniteChains E) :=
  PartOrd.nerveFunctor.map (PartOrd.ofHom
    (NonemptyFiniteChains.orderHomMap (simplexVertices s)))

lemma sdNerveSimplexLeg_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (s : (nerve E) _⦋m⦌) :
    SimplexCategory.sd.map f ≫ sdNerveSimplexLeg s =
      sdNerveSimplexLeg ((nerve E).map f.op s) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply nerve.ext_of_isThin
  funext j
  apply NonemptyFiniteChains.ext
  classical
  change Finset.image _ (Finset.image _ _) = Finset.image _ _
  rw [Finset.image_image]
  rfl

lemma sdNerveMap_fac_any {n : ℕ} (s : (nerve E) _⦋n⦌) :
    SSet.sd.map (SSet.yonedaEquiv.symm s) ≫ sdNerveMap =
      (SSet.stdSimplex.sdIso.app ⦋n⦌).hom ≫ sdNerveSimplexLeg s := by
  obtain ⟨m, φ, _, t, rfl⟩ := (nerve E).exists_nonDegenerate s
  rw [← SSet.yonedaEquiv_symm_naturality_left, SSet.sd.map_comp, Category.assoc]
  erw [sdNerveMap_fac (SSet.N.mk t.val t.property)]
  erw [← Category.assoc, SSet.stdSimplex.sdIso.hom.naturality, Category.assoc]
  change (SSet.stdSimplex.sdIso.app ⦋n⦌).hom ≫
      (SimplexCategory.sd.map φ ≫ sdNerveSimplexLeg t.val) = _
  rw [sdNerveSimplexLeg_naturality]

lemma sdNerveSimplexLeg_comp {n : ℕ} (s : (nerve E) _⦋n⦌) (f : E →o F) :
    sdNerveSimplexLeg s ≫ PartOrd.nerveFunctor.map
      (PartOrd.ofHom (NonemptyFiniteChains.orderHomMap f)) =
    sdNerveSimplexLeg ((nerveMap f.monotone.functor).app _ s) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply nerve.ext_of_isThin
  funext j
  apply NonemptyFiniteChains.ext
  classical
  change Finset.image _ (Finset.image _ _) = Finset.image _ _
  rw [Finset.image_image]
  rfl

lemma sdNerveMap_naturality (f : E →o F) :
    SSet.sd.map (nerveMap f.monotone.functor) ≫ sdNerveMap =
      sdNerveMap ≫ PartOrd.nerveFunctor.map
        (PartOrd.ofHom (NonemptyFiniteChains.orderHomMap f)) := by
  apply (isColimitOfPreserves SSet.sd (nerve E).isColimitCoconeN').hom_ext
  intro s
  change SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫
      (SSet.sd.map (nerveMap f.monotone.functor) ≫ sdNerveMap) =
    SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫ (sdNerveMap ≫ _)
  erw [← Category.assoc, ← SSet.sd.map_comp, SSet.yonedaEquiv_symm_comp,
    sdNerveMap_fac_any, ← Category.assoc, sdNerveMap_fac, Category.assoc]
  exact congrArg ((SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom ≫ ·)
    (sdNerveSimplexLeg_comp s.simplex f).symm

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {E : Type u} [PartialOrder E] (K : (nerve E).Subcomplex)

def subcomplexN (s : (K : SSet).N) : (nerve E).N :=
  SSet.N.mk s.simplex.val ((K.mem_nonDegenerate_iff _).mp s.nonDegenerate)

lemma subcomplexN_le_iff (s t : (K : SSet).N) : subcomplexN K s ≤ subcomplexN K t ↔ s ≤ t := by
  constructor
  · intro h
    obtain ⟨f, hf, he⟩ := SSet.N.le_iff_exists_mono.mp h
    exact SSet.N.le_iff_exists_mono.mpr ⟨f, hf, Subtype.ext he⟩
  · intro h
    obtain ⟨f, hf, he⟩ := SSet.N.le_iff_exists_mono.mp h
    exact SSet.N.le_iff_exists_mono.mpr ⟨f, hf, congrArg Subtype.val he⟩

lemma subcomplexN_injective : Function.Injective (subcomplexN K) := by
  intro s t h
  exact le_antisymm ((subcomplexN_le_iff K s t).mp h.le)
    ((subcomplexN_le_iff K t s).mp h.ge)

lemma subcomplexN_downward (s : (K : SSet).N) (t : (nerve E).N)
    (h : t ≤ subcomplexN K s) : ∃ a : (K : SSet).N, subcomplexN K a = t := by
  obtain ⟨f, _, he⟩ := SSet.N.le_iff_exists_mono.mp h
  have ht : t.simplex ∈ K.obj (op ⦋t.dim⦌) := he ▸ K.map f.op s.simplex.property
  let a : (K : SSet).N := SSet.N.mk ⟨t.simplex, ht⟩
    ((K.mem_nonDegenerate_iff _).mpr t.nonDegenerate)
  exact ⟨a, rfl⟩

def AllowedChains := {c : NonemptyFiniteChains E // ∃ s : (K : SSet).N,
  simplexChain (subcomplexN K s).simplex = c}

instance : PartialOrder (AllowedChains K) := inferInstanceAs (PartialOrder {_c // _})

def allowedChainInclusion : AllowedChains K →o NonemptyFiniteChains E :=
  OrderHom.Subtype.val _

noncomputable def subcomplexChain (s : (K : SSet).N) : AllowedChains K :=
  ⟨simplexChain (subcomplexN K s).simplex, s, rfl⟩

lemma allowedChains_downward {c d : NonemptyFiniteChains E} (h : c ≤ d)
    (hd : ∃ s : (K : SSet).N, simplexChain (subcomplexN K s).simplex = d) :
    ∃ s : (K : SSet).N, simplexChain (subcomplexN K s).simplex = c := by
  obtain ⟨s, rfl⟩ := hd
  obtain ⟨a, ha⟩ := subcomplexN_downward K s (chainSimplex c)
    ((simplexChain_le_iff _ _).mp (by rwa [simplexChain_chainSimplex]))
  exact ⟨a, by rw [ha, simplexChain_chainSimplex]⟩

noncomputable def allowedChainSimplex (c : AllowedChains K) : (K : SSet).N := c.property.choose

lemma subcomplexChain_allowedChainSimplex (c : AllowedChains K) :
    subcomplexChain K (allowedChainSimplex K c) = c :=
  Subtype.ext c.property.choose_spec

noncomputable def subcomplexNondegenerateChains : (K : SSet).N ≃o AllowedChains K where
  toFun := subcomplexChain K
  invFun := allowedChainSimplex K
  left_inv s := by
    apply subcomplexN_injective K
    apply nerveNondegenerateChains.injective
    exact congrArg Subtype.val (subcomplexChain_allowedChainSimplex K (subcomplexChain K s))
  right_inv := subcomplexChain_allowedChainSimplex K
  map_rel_iff' := fun {s t} => (simplexChain_le_iff _ _).trans (subcomplexN_le_iff K s t)

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {E : Type u} [PartialOrder E] (K : (nerve E).Subcomplex)

noncomputable def sdSubcomplexVertices (s : (K : SSet).N) :
    NonemptyFiniteChains (SimplexCategory.toPartOrd.obj ⦋s.dim⦌) →o AllowedChains K where
  toFun c := ⟨c.map (simplexVertices s.simplex.val), allowedChains_downward K (by
    intro a ha
    obtain ⟨i, _, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp ha
    exact (mem_simplexChain _ _).mpr ⟨i.down, rfl⟩) ⟨s, rfl⟩⟩
  monotone' _ _ h := (NonemptyFiniteChains.orderHomMap _).monotone h

noncomputable def sdSubcomplexLeg (s : (K : SSet).N) :
    SimplexCategory.sd.obj ⦋s.dim⦌ ⟶ nerve (AllowedChains K) :=
  nerveMap (sdSubcomplexVertices K s).monotone.functor

abbrev allowedChainsForget : nerve (AllowedChains K) ⟶ nerve (NonemptyFiniteChains E) :=
  nerveMap (allowedChainInclusion K).monotone.functor

lemma allowedChainsForget_app_injective (k : SimplexCategoryᵒᵖ) :
    Function.Injective ((allowedChainsForget K).app k) := by
  intro x y h
  apply nerve.ext_of_isThin
  funext i
  exact Subtype.ext (congrArg (fun q => q.obj i) h)

instance : Mono (allowedChainsForget K) := by
  rw [NatTrans.mono_iff_mono_app]
  intro k
  exact (CategoryTheory.mono_iff_injective _).mpr (allowedChainsForget_app_injective K k)

lemma sdSubcomplexLeg_forget (s : (K : SSet).N) :
    sdSubcomplexLeg K s ≫ allowedChainsForget K = sdNerveLeg (subcomplexN K s) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply nerve.ext_of_isThin
  rfl

lemma subcomplexN_monoOfLE {s t : (K : SSet).N} (h : s ≤ t) :
    SSet.N.monoOfLE ((subcomplexN_le_iff K s t).mpr h) = SSet.N.monoOfLE h := by
  apply SSet.Nonsingular.injective_map (subcomplexN K t).simplex (subcomplexN K t).nonDegenerate
  rw [SSet.N.map_monoOfLE]
  exact (congrArg Subtype.val (SSet.N.map_monoOfLE h)).symm

lemma sdSubcomplexLeg_naturality {s t : (K : SSet).N} (h : s ≤ t) :
    SimplexCategory.sd.map (SSet.N.monoOfLE h) ≫ sdSubcomplexLeg K t = sdSubcomplexLeg K s := by
  apply (cancel_mono (allowedChainsForget K)).mp
  rw [Category.assoc, sdSubcomplexLeg_forget, sdSubcomplexLeg_forget]
  rw [← subcomplexN_monoOfLE K h]
  exact sdNerveLeg_naturality _

noncomputable def sdSubcomplexCocone : Cocone ((K : SSet).functorN' ⋙ SSet.sd) where
  pt := nerve (AllowedChains K)
  ι.app s := (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom ≫ sdSubcomplexLeg K s
  ι.naturality s t f := by
    change SSet.sd.map (SSet.stdSimplex.map (SSet.N.monoOfLE (leOfHom f))) ≫
      ((SSet.stdSimplex.sdIso.app ⦋t.dim⦌).hom ≫ sdSubcomplexLeg K t) = _
    simp only [Functor.const_obj_map]
    erw [← Category.assoc, SSet.stdSimplex.sdIso.hom.naturality,
      Category.assoc, sdSubcomplexLeg_naturality]
    exact (Category.comp_id _).symm

noncomputable def sdSubcomplexMap : SSet.sd.obj (K : SSet) ⟶ nerve (AllowedChains K) :=
  (isColimitOfPreserves SSet.sd (K : SSet).isColimitCoconeN').desc (sdSubcomplexCocone K)

lemma sdSubcomplexMap_fac (s : (K : SSet).N) :
    SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫ sdSubcomplexMap K =
      (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom ≫ sdSubcomplexLeg K s :=
  (isColimitOfPreserves SSet.sd (K : SSet).isColimitCoconeN').fac (sdSubcomplexCocone K) s

noncomputable def sdSubcomplexInjection (s : (K : SSet).N) :
    SimplexCategory.sd.obj ⦋s.dim⦌ ⟶ SSet.sd.obj (K : SSet) :=
  (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).inv ≫
    SSet.sd.map (SSet.yonedaEquiv.symm s.simplex)

lemma sdSubcomplexInjection_comp (s : (K : SSet).N) :
    sdSubcomplexInjection K s ≫ sdSubcomplexMap K = sdSubcomplexLeg K s := by
  rw [sdSubcomplexInjection, Category.assoc, sdSubcomplexMap_fac,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma sdSubcomplexInjection_naturality {s t : (K : SSet).N} (h : s ≤ t) :
    SimplexCategory.sd.map (SSet.N.monoOfLE h) ≫ sdSubcomplexInjection K t =
      sdSubcomplexInjection K s := by
  unfold sdSubcomplexInjection
  erw [← Category.assoc, SSet.stdSimplex.sdIso.inv.naturality,
    Category.assoc, ← SSet.sd.map_comp,
    SSet.N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex]
  rfl

lemma sdSubcomplexInjection_jointly_surjective (k : SimplexCategoryᵒᵖ)
    (z : (SSet.sd.obj (K : SSet)).obj k) :
    ∃ (s : (K : SSet).N) (x : (SimplexCategory.sd.obj ⦋s.dim⦌).obj k),
      (sdSubcomplexInjection K s).app k x = z := by
  have hc := isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj k)
    (isColimitOfPreserves SSet.sd (K : SSet).isColimitCoconeN')
  obtain ⟨s, x, hx⟩ := Types.jointly_surjective_of_isColimit hc z
  refine ⟨s, (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom.app k x, ?_⟩
  change (SSet.sd.map (SSet.yonedaEquiv.symm s.simplex)).app k
    ((SSet.stdSimplex.sdIso.app ⦋s.dim⦌).inv.app k
      ((SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom.app k x)) = z
  have he := congrArg (fun f => f.app k x) (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom_inv_id
  change (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).inv.app k
      ((SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom.app k x) = x at he
  rw [he]
  exact hx

lemma sdSubcomplexLeg_app_injective (s : (K : SSet).N) (k : SimplexCategoryᵒᵖ) :
    Function.Injective ((sdSubcomplexLeg K s).app k) := by
  intro x y h
  exact sdNerveLeg_app_injective (subcomplexN K s) k
    (congrArg ((allowedChainsForget K).app k) h)

lemma sdSubcomplexLeg_obj_le (s : (K : SSet).N) (k : SimplexCategoryᵒᵖ)
    (x : (SimplexCategory.sd.obj ⦋s.dim⦌).obj k) (j : Fin (k.unop.len+1)) :
    ((sdSubcomplexLeg K s).app k x).obj j ≤ subcomplexChain K s :=
  sdNerveLeg_obj_le (subcomplexN K s) k x j

lemma sdSubcomplexLeg_surjective_on (s : (K : SSet).N) (k : SimplexCategoryᵒᵖ)
    (q : (nerve (AllowedChains K)).obj k) (h : ∀ i, q.obj i ≤ subcomplexChain K s) :
    ∃ p : (SimplexCategory.sd.obj ⦋s.dim⦌).obj k, (sdSubcomplexLeg K s).app k p = q := by
  obtain ⟨p, hp⟩ := sdNerveLeg_surjective_on (subcomplexN K s) k
    ((allowedChainsForget K).app k q) h
  exact ⟨p, allowedChainsForget_app_injective K k hp⟩

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {E : Type u} [PartialOrder E] (K : (nerve E).Subcomplex)

lemma sdSubcomplexMap_app_surjective (k : SimplexCategoryᵒᵖ) :
    Function.Surjective ((sdSubcomplexMap K).app k) := by
  intro q
  let s := allowedChainSimplex K (q.obj (Fin.last k.unop.len))
  have h (i) : q.obj i ≤ subcomplexChain K s := by
    rw [subcomplexChain_allowedChainSimplex]
    exact q.monotone (Fin.le_last i)
  obtain ⟨p, hp⟩ := sdSubcomplexLeg_surjective_on K s k q h
  refine ⟨(sdSubcomplexInjection K s).app k p, ?_⟩
  exact (congrArg (fun f => f.app k p) (sdSubcomplexInjection_comp K s)).trans hp

lemma sdSubcomplexMap_app_injective (k : SimplexCategoryᵒᵖ) :
    Function.Injective ((sdSubcomplexMap K).app k) := by
  intro x y hxy
  obtain ⟨s, p, rfl⟩ := sdSubcomplexInjection_jointly_surjective K k x
  obtain ⟨t, q, rfl⟩ := sdSubcomplexInjection_jointly_surjective K k y
  have hs := congrArg (fun f => f.app k p) (sdSubcomplexInjection_comp K s)
  have ht := congrArg (fun f => f.app k q) (sdSubcomplexInjection_comp K t)
  have he : (sdSubcomplexLeg K s).app k p = (sdSubcomplexLeg K t).app k q := hs.symm.trans (hxy.trans ht)
  let v := (sdSubcomplexLeg K s).app k p
  let a := allowedChainSimplex K (v.obj (Fin.last k.unop.len))
  have has : a ≤ s := by
    apply (subcomplexNondegenerateChains K).le_iff_le.mp
    change subcomplexChain K a ≤ subcomplexChain K s
    rw [subcomplexChain_allowedChainSimplex]
    exact sdSubcomplexLeg_obj_le K s k p _
  have hat : a ≤ t := by
    apply (subcomplexNondegenerateChains K).le_iff_le.mp
    change subcomplexChain K a ≤ subcomplexChain K t
    rw [subcomplexChain_allowedChainSimplex]
    dsimp only [v]
    rw [he]
    exact sdSubcomplexLeg_obj_le K t k q _
  obtain ⟨r, hr⟩ := sdSubcomplexLeg_surjective_on K a k v (fun i => by
    rw [subcomplexChain_allowedChainSimplex]
    exact v.monotone (Fin.le_last i))
  have hps : (SimplexCategory.sd.map (SSet.N.monoOfLE has)).app k r = p := by
    apply sdSubcomplexLeg_app_injective K s k
    exact (congrArg (fun f => f.app k r) (sdSubcomplexLeg_naturality K has)).trans hr
  have hqt : (SimplexCategory.sd.map (SSet.N.monoOfLE hat)).app k r = q := by
    apply sdSubcomplexLeg_app_injective K t k
    exact (congrArg (fun f => f.app k r) (sdSubcomplexLeg_naturality K hat)).trans (hr.trans he)
  rw [← hps, ← hqt]
  exact (congrArg (fun f => f.app k r) (sdSubcomplexInjection_naturality K has)).trans
    (congrArg (fun f => f.app k r) (sdSubcomplexInjection_naturality K hat)).symm

instance sdSubcomplexMap_isIso : IsIso (sdSubcomplexMap K) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro k
  exact (CategoryTheory.isIso_iff_bijective _).mpr
    ⟨sdSubcomplexMap_app_injective K k, sdSubcomplexMap_app_surjective K k⟩

noncomputable def sdSubcomplexIso : SSet.sd.obj (K : SSet) ≅ nerve (AllowedChains K) :=
  asIso (sdSubcomplexMap K)

lemma sdSubcomplexMap_naturality : SSet.sd.map K.ι ≫ sdNerveMap =
    sdSubcomplexMap K ≫ allowedChainsForget K := by
  apply (isColimitOfPreserves SSet.sd (K : SSet).isColimitCoconeN').hom_ext
  intro s
  change SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫
      (SSet.sd.map K.ι ≫ sdNerveMap) =
    SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫ (sdSubcomplexMap K ≫ _)
  erw [← Category.assoc, ← SSet.sd.map_comp, SSet.yonedaEquiv_symm_comp,
    sdNerveMap_fac (subcomplexN K s), ← Category.assoc, sdSubcomplexMap_fac, Category.assoc]
  rw [sdSubcomplexLeg_forget]
  rfl

end Thomason.Subdivision

end

end OAI
