import OAI.CategoryTheory.Globular.Tree

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model

noncomputable def smallWhiskerCell {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y)
    (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (k : ℕ) (x : (S.underlying.whisker n false).Cell k) : Y.obj.underlying.Cell k :=
  match x with
  | .base k x => (underlyingMap f.hom).app k (smallFreeGen hC q S k x)
  | .tip x => Y.obj.underlying.target n (e x)
  | .edge x => e x

theorem smallWhiskerCell_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (he : ∀ x, Y.obj.underlying.source n (e x) =
      (underlyingMap f.hom).app n (smallFreeGen hC q S n x))
    (k : ℕ) (x : (S.underlying.whisker n false).Cell (k+1)) :
    smallWhiskerCell hC q n f e k ((S.underlying.whisker n false).source k x) =
      Y.obj.underlying.source k (smallWhiskerCell hC q n f e (k+1) x) := by
  cases x with
  | base k x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.source k x)) = _
    rw [← smallFreeGen_source, (underlyingMap f.hom).source_app]
    rfl
  | tip x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.source k x)) = _
    rw [← smallFreeGen_source, (underlyingMap f.hom).source_app, ← he]
    exact Y.obj.underlying.source_source k _
  | edge x => exact (he x).symm

theorem smallWhiskerCell_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (he : ∀ x, Y.obj.underlying.source n (e x) =
      (underlyingMap f.hom).app n (smallFreeGen hC q S n x))
    (k : ℕ) (x : (S.underlying.whisker n false).Cell (k+1)) :
    smallWhiskerCell hC q n f e k ((S.underlying.whisker n false).target k x) =
      Y.obj.underlying.target k (smallWhiskerCell hC q n f e (k+1) x) := by
  cases x with
  | base k x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.target k x)) = _
    rw [← smallFreeGen_target, (underlyingMap f.hom).target_app]
    rfl
  | tip x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.target k x)) = _
    rw [← smallFreeGen_target, (underlyingMap f.hom).target_app, ← he]
    exact Y.obj.underlying.target_source k _
  | edge x => rfl

noncomputable def smallWhiskerDesc {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (he : ∀ x, Y.obj.underlying.source n (e x) =
      (underlyingMap f.hom).app n (smallFreeGen hC q S n x)) : whiskerFree hC q n S ⟶ Y :=
  smallFreeDescCells hC q (smallWhiskerCell hC q n f e)
    (fun k x => by
      have h := (S.underlying.whisker n false).presheafUnderlyingMap.source_app k x
      change (S.underlying.whisker n false).presheaf.underlying.source k x =
        (S.underlying.whisker n false).source k x at h
      exact (congrArg (smallWhiskerCell hC q n f e k) h).trans
        (smallWhiskerCell_source hC q n f e he k x))
    (fun k x => by
      have h := (S.underlying.whisker n false).presheafUnderlyingMap.target_app k x
      change (S.underlying.whisker n false).presheaf.underlying.target k x =
        (S.underlying.whisker n false).target k x at h
      exact (congrArg (smallWhiskerCell hC q n f e k) h).trans
        (smallWhiskerCell_target hC q n f e he k x))

@[simp] theorem smallWhiskerDesc_base {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e) (he) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (smallWhiskerDesc hC q n f e he).hom).app k (wBase hC q n S k x) =
      (underlyingMap f.hom).app k (smallFreeGen hC q S k x) :=
  smallFreeDescCells_gen hC q _ _ _ k _

@[simp] theorem smallWhiskerDesc_edge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e) (he) (x : S.underlying.Cell n) :
    (underlyingMap (smallWhiskerDesc hC q n f e he).hom).app (n+1) (wEdge hC q n S x) = e x :=
  smallFreeDescCells_gen hC q _ _ _ (n+1) _

noncomputable def whiskerIn {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) : (smallFree hC q).obj S ⟶ whiskerFree hC q n S :=
  (smallFree hC q).map ((GlobularPresheaf.whiskeringInclusion n false).app S)

@[simp] theorem whiskerIn_gen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (whiskerIn hC q n S).hom).app k (smallFreeGen hC q S k x) =
      wBase hC q n S k x := smallFreeGen_map hC q _ k x

theorem smallFree_low_bijective {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) (hrq : r ≤ q) {S T : GlobularPresheaf.{0}} (f : S ⟶ T)
    (hf : ∀ k, k ≤ r → Function.Bijective ((GlobularPresheaf.underlyingMap f).app k)) :
    ∀ k, k ≤ r → Function.Bijective ((underlyingMap ((smallFree hC q).map f).hom).app k) := by
  apply (coskeletalLocalMap_iff hC r _).mp
  intro Z hZ g
  let Z' : CutoffModels C q := ⟨Z, fun j hj => hZ j (lt_of_le_of_lt hrq hj)⟩
  let A := cutoffGlobularAdjunction hC q
  let g' : (smallFree hC q).obj S ⟶ Z' := ObjectProperty.homMk g
  let f' := GlobularPresheaf.liftSmall.map f
  have hf' : ∀ k, k ≤ r → Function.Bijective (f'.app (op (Globe.mk k))) := by
    intro k hk
    exact ULift.map_bijective.mpr (hf k hk)
  have hb := GlobularPresheaf.precomp_bijective_low f' r hf' hZ
  obtain ⟨b, hb'⟩ := hb.2 (A.homEquiv _ Z' g')
  let a := (A.homEquiv _ Z').symm b
  have ha : (smallFree hC q).map f ≫ a = g' := by
    apply (A.homEquiv _ Z').injective
    erw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hb'
  refine ⟨a.hom, congrArg (fun t => t.hom) ha, ?_⟩
  intro a' ha'
  let a'' : (smallFree hC q).obj T ⟶ Z' := ObjectProperty.homMk a'
  have hh : (smallFree hC q).map f ≫ a'' = g' := by
    apply ObjectProperty.hom_ext
    exact ha'
  have hh' : a'' = a := by
    apply (A.homEquiv _ Z').injective
    apply hb.1
    change f' ≫ A.homEquiv _ Z' a'' = f' ≫ A.homEquiv _ Z' a
    erw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left, hh, ha]
  exact congrArg (fun t => t.hom) hh'

theorem liftsBoundary_of_bijective {X Y : GlobularSet.{u}} (p : GlobularSet.Hom X Y)
    (k : ℕ) (hp : ∀ j, j ≤ k → Function.Bijective (p.app j)) :
    GlobularSet.LiftsBoundary p k := by
  intro bd y hy
  obtain ⟨x, hx⟩ := (hp k le_rfl).2 y
  refine ⟨x, ?_, hx⟩
  apply (p.boundaryMap_bijective_of_low k (fun j hj => hp j hj.le)).1
  rw [p.boundary_app, hx, hy]

theorem exists_upper_resolution {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (hnq : n ≤ q) {X Y : CutoffModels C q} (f : X ⟶ Y)
    (hY : Cofibrant hC q Y) (hXF : X.obj.underlying.HasFillers)
    (hYF : Y.obj.underlying.HasFillers)
    (hf : ∀ k, k ≤ n → Function.Bijective ((underlyingMap f.hom).app k)) :
    ∃ (M : CutoffModels C q) (i : X ⟶ M) (p : M ⟶ Y) (s : Y ⟶ M),
      i ≫ p = f ∧ s ≫ p = 𝟙 Y ∧ (boundaryClass hC q (n+1)).rlp.llp i ∧
      M.obj.underlying.HasFillers ∧
      ∀ k, k ≤ n → Function.Injective ((underlyingMap p.hom).app k) := by
  let := boundaryClass_smallObject hC q (n+1)
  let W := boundaryClass hC q (n+1)
  let F := MorphismProperty.factorizationData W.rlp.llp W.rlp f
  have hi k (hk : k ≤ n) := upper_cofibration_low_bijective hC q (n+1) k
    (hk.trans hnq) (by omega) F.i F.hi
  have hp k (hk : k ≤ n) : Function.Bijective ((underlyingMap F.p.hom).app k) := by
    have fac (x : X.obj.underlying.Cell k) :
        (underlyingMap F.p.hom).app k ((underlyingMap F.i.hom).app k x) =
        (underlyingMap f.hom).app k x :=
      congrFun (congrArg (fun z => (underlyingMap z.hom).app k) F.fac) x
    constructor
    · intro a b hab
      obtain ⟨a', rfl⟩ := (hi k hk).2 a
      obtain ⟨b', rfl⟩ := (hi k hk).2 b
      exact congrArg ((underlyingMap F.i.hom).app k)
        ((hf k hk).1 ((fac a').symm.trans (hab.trans (fac b'))))
    · intro y
      obtain ⟨x, hx⟩ := (hf k hk).2 y
      exact ⟨(underlyingMap F.i.hom).app k x, (fac x).trans hx⟩
  have hMF : F.Z.obj.underlying.HasFillers := by
    apply hXF.of_low_bijective (underlyingMap F.i.hom) n hi
    intro k hk bd
    obtain ⟨y, hy⟩ := hYF k ((underlyingMap F.p.hom).boundaryMap k bd)
    obtain ⟨x, hx, _⟩ := (hasLiftingProperty_I_iff k F.p.hom).1
      ((boundaryClass_rlp_iff hC q (n+1) F.p).1 F.hp k (by omega)) bd y hy
    exact ⟨x, hx⟩
  have hpI : (boundaryClass hC q 0).rlp F.p := by
    rw [boundaryClass_rlp_iff]
    intro k _
    by_cases hk : k ≤ n
    · rw [hasLiftingProperty_I_iff]
      exact liftsBoundary_of_bijective (underlyingMap F.p.hom) k
        (fun j hj => hp j (hj.trans hk))
    · exact (boundaryClass_rlp_iff hC q (n+1) F.p).1 F.hp k (by omega)
  obtain ⟨s, hs⟩ := hY F.p hpI (𝟙 Y)
  exact ⟨F.Z, F.i, F.p, s, F.fac, hs, F.hi, hMF, fun k hk => (hp k hk).1⟩

theorem whiskerFree_hom_ext {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    {f g : whiskerFree hC q n S ⟶ Y}
    (hb : ∀ k x, (underlyingMap f.hom).app k (wBase hC q n S k x) =
      (underlyingMap g.hom).app k (wBase hC q n S k x))
    (he : ∀ x, (underlyingMap f.hom).app (n+1) (wEdge hC q n S x) =
      (underlyingMap g.hom).app (n+1) (wEdge hC q n S x)) : f = g := by
  apply smallFree_hom_ext hC q
  intro k x
  cases x with
  | base k x => exact hb k x
  | edge x => exact he x
  | tip x =>
    rw [← wEdge_target hC q k S x, (underlyingMap f.hom).target_app,
      (underlyingMap g.hom).target_app, he]

noncomputable def whiskerFreeMap {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) :
    whiskerFree hC q n S ⟶ whiskerFree hC q n T :=
  (smallFree hC q).map ((GlobularPresheaf.whiskering n false).map f)

@[simp] theorem whiskerFreeMap_base {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (whiskerFreeMap hC q n f).hom).app k (wBase hC q n S k x) =
      wBase hC q n T k ((GlobularPresheaf.underlyingMap f).app k x) :=
  smallFreeGen_map hC q _ k _

@[simp] theorem whiskerFreeMap_edge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) (x : S.underlying.Cell n) :
    (underlyingMap (whiskerFreeMap hC q n f).hom).app (n+1) (wEdge hC q n S x) =
      wEdge hC q n T ((GlobularPresheaf.underlyingMap f).app n x) :=
  smallFreeGen_map hC q _ (n+1) _

@[reassoc] theorem whiskerIn_naturality {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) :
    whiskerIn hC q n S ≫ whiskerFreeMap hC q n f =
      (smallFree hC q).map f ≫ whiskerIn hC q n T := by
  unfold whiskerIn whiskerFreeMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (smallFree hC q).map ((GlobularPresheaf.whiskeringInclusion n false).naturality f).symm

theorem whiskerFree_hasFillers_of_spine {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    {S T : GlobularPresheaf.{0}} (f : S ⟶ T)
    (hf : ∀ k, k ≤ n → Function.Bijective ((GlobularPresheaf.underlyingMap f).app k))
    (hS : ((smallFree hC q).obj S).obj.underlying.HasFillers)
    (hT : ((smallFree hC q).obj T).obj.underlying.HasFillers)
    (hW : (whiskerFree hC q n S).obj.underlying.HasFillers) :
    (whiskerFree hC q n T).obj.underlying.HasFillers := by
  let := cutoff_hasColimits hC q
  let F := smallFree hC q
  obtain ⟨M,i,p,s,hip,hsp,hi,hM,hp⟩ := exists_upper_resolution hC q n hnq
    (F.map f) (smallFree_cofibrant hC q T) hS hT
    (smallFree_low_bijective hC q n hnq f hf)
  let a := whiskerIn hC q n S
  let Q := pushout a i
  let j : whiskerFree hC q n S ⟶ Q := pushout.inl a i
  let k : M ⟶ Q := pushout.inr a i
  have hQ : Q.obj.underlying.HasFillers := upper_pushout_hasFillers hC q (n+1) H
    (IsPushout.of_hasPushout a i) hi (smallFree_cofibrant hC q S) hS hM
    (smallFree_cofibrant hC q _) hW
  let wm := whiskerFreeMap hC q n f
  let r : Q ⟶ whiskerFree hC q n T := pushout.desc wm (p ≫ whiskerIn hC q n T) (by
    rw [← Category.assoc, hip]
    exact whiskerIn_naturality hC q n f)
  have hjr : j ≫ r = wm := pushout.inl_desc _ _ _
  have hkr : k ≫ r = p ≫ whiskerIn hC q n T := pushout.inr_desc _ _ _
  let E := Equiv.ofBijective ((GlobularPresheaf.underlyingMap f).app n) (hf n le_rfl)
  have hsgen (x : T.underlying.Cell n) :
      (underlyingMap s.hom).app n (smallFreeGen hC q T n x) =
      (underlyingMap i.hom).app n (smallFreeGen hC q S n (E.symm x)) := by
    apply hp n le_rfl
    have hs := congrFun (congrArg (fun z => (underlyingMap z.hom).app n) hsp)
      (smallFreeGen hC q T n x)
    have hi' := congrFun (congrArg (fun z => (underlyingMap z.hom).app n) hip)
      (smallFreeGen hC q S n (E.symm x))
    exact hs.trans (((smallFreeGen_map hC q f n (E.symm x)).trans
      (congrArg (smallFreeGen hC q T n) (E.apply_symm_apply x))).symm.trans hi'.symm)
  let e (x : T.underlying.Cell n) := (underlyingMap j.hom).app (n+1) (wEdge hC q n S (E.symm x))
  have he (x : T.underlying.Cell n) : Q.obj.underlying.source n (e x) =
      (underlyingMap (s ≫ k).hom).app n (smallFreeGen hC q T n x) := by
    change Q.obj.underlying.source n ((underlyingMap j.hom).app (n+1) _) =
      (underlyingMap k.hom).app n ((underlyingMap s.hom).app n _)
    rw [← (underlyingMap j.hom).source_app, wEdge_source, hsgen]
    have hh := congrFun (congrArg (fun z => (underlyingMap z.hom).app n)
      (pushout.condition (f := a) (g := i))) (smallFreeGen hC q S n (E.symm x))
    exact (congrArg ((underlyingMap j.hom).app n)
      (whiskerIn_gen hC q n S n (E.symm x))).symm.trans hh
  let t := smallWhiskerDesc hC q n (s ≫ k) e he
  have htr : t ≫ r = 𝟙 _ := by
    apply whiskerFree_hom_ext hC q n
    · intro l x
      change (underlyingMap r.hom).app l ((underlyingMap t.hom).app l _) = wBase hC q n T l x
      have ht := smallWhiskerDesc_base hC q n (s ≫ k) e he l x
      apply (congrArg ((underlyingMap r.hom).app l) ht).trans
      have hcomp : (s ≫ k) ≫ r = whiskerIn hC q n T := by
        rw [Category.assoc, hkr, ← Category.assoc, hsp, Category.id_comp]
      exact (congrFun (congrArg (fun z => (underlyingMap z.hom).app l) hcomp)
        (smallFreeGen hC q T l x)).trans (whiskerIn_gen hC q n T l x)
    · intro x
      change (underlyingMap r.hom).app (n+1) ((underlyingMap t.hom).app (n+1) _) = wEdge hC q n T x
      have ht := smallWhiskerDesc_edge hC q n (s ≫ k) e he x
      apply (congrArg ((underlyingMap r.hom).app (n+1)) ht).trans
      have hh := congrFun (congrArg (fun z => (underlyingMap z.hom).app (n+1)) hjr)
        (wEdge hC q n S (E.symm x))
      exact hh.trans ((whiskerFreeMap_edge hC q n f (E.symm x)).trans
        (congrArg (wEdge hC q n T) (E.apply_symm_apply x)))
  exact hQ.retract (underlyingMap t.hom) (underlyingMap r.hom)
    (congrArg (fun z : whiskerFree hC q n T ⟶ whiskerFree hC q n T => underlyingMap z.hom) htr)

theorem whiskerFree_hasFillers {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1)) (S : Shape) :
    (whiskerFree hC q n S.realize).obj.underlying.HasFillers := by
  let P := S.2.spine n
  exact whiskerFree_hasFillers_of_spine hC q n hnq H P.map P.low_bijective
    (smallShape_hasFillers hC q P.S) (smallShape_hasFillers hC q S)
    (whiskerFree_bounded_hasFillers hC q n H P.S P.height_le)

end GlobularTheory.Model
end Grothendieck

end OAI
