import OAI.CategoryTheory.Globular.SpineWhisker

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model

noncomputable abbrev reverseWhiskerFree {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) :=
  (smallFree hC q).obj ((GlobularPresheaf.whiskering n true).obj S)

noncomputable def rwBase {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell k) :
    (reverseWhiskerFree hC q n S).obj.underlying.Cell k :=
  smallFreeGen hC q ((GlobularPresheaf.whiskering n true).obj S) k (.base k x)

noncomputable def rwEdge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (reverseWhiskerFree hC q n S).obj.underlying.Cell (n+1) :=
  smallFreeGen hC q ((GlobularPresheaf.whiskering n true).obj S) (n+1) (.edge x)

@[simp] theorem rwBase_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    (reverseWhiskerFree hC q n S).obj.underlying.source k (rwBase hC q n S (k+1) x) =
      rwBase hC q n S k (S.underlying.source k x) := by
  unfold rwBase
  erw [smallFreeGen_source]
  congr 1
  exact (S.underlying.whisker n true).presheafUnderlyingMap.source_app _ _

@[simp] theorem rwBase_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    (reverseWhiskerFree hC q n S).obj.underlying.target k (rwBase hC q n S (k+1) x) =
      rwBase hC q n S k (S.underlying.target k x) := by
  unfold rwBase
  erw [smallFreeGen_target]
  congr 1
  exact (S.underlying.whisker n true).presheafUnderlyingMap.target_app _ _

@[simp] theorem rwEdge_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (reverseWhiskerFree hC q n S).obj.underlying.target n (rwEdge hC q n S x) = rwBase hC q n S n x := by
  unfold rwEdge rwBase
  erw [smallFreeGen_target]
  congr 1
  exact (S.underlying.whisker n true).presheafUnderlyingMap.target_app _ _

noncomputable def smallReverseWhiskerCell {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y)
    (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (k : ℕ) (x : (S.underlying.whisker n true).Cell k) : Y.obj.underlying.Cell k :=
  match x with
  | .base k x => (underlyingMap f.hom).app k (smallFreeGen hC q S k x)
  | .tip x => Y.obj.underlying.source n (e x)
  | .edge x => e x

theorem smallReverseWhiskerCell_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (he : ∀ x, Y.obj.underlying.target n (e x) =
      (underlyingMap f.hom).app n (smallFreeGen hC q S n x))
    (k : ℕ) (x : (S.underlying.whisker n true).Cell (k+1)) :
    smallReverseWhiskerCell hC q n f e k ((S.underlying.whisker n true).source k x) =
      Y.obj.underlying.source k (smallReverseWhiskerCell hC q n f e (k+1) x) := by
  cases x with
  | base k x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.source k x)) = _
    rw [← smallFreeGen_source, (underlyingMap f.hom).source_app]
    rfl
  | tip x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.source k x)) = _
    rw [← smallFreeGen_source, (underlyingMap f.hom).source_app, ← he]
    exact (Y.obj.underlying.source_source k _).symm
  | edge x => rfl

theorem smallReverseWhiskerCell_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (he : ∀ x, Y.obj.underlying.target n (e x) =
      (underlyingMap f.hom).app n (smallFreeGen hC q S n x))
    (k : ℕ) (x : (S.underlying.whisker n true).Cell (k+1)) :
    smallReverseWhiskerCell hC q n f e k ((S.underlying.whisker n true).target k x) =
      Y.obj.underlying.target k (smallReverseWhiskerCell hC q n f e (k+1) x) := by
  cases x with
  | base k x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.target k x)) = _
    rw [← smallFreeGen_target, (underlyingMap f.hom).target_app]
    rfl
  | tip x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.target k x)) = _
    rw [← smallFreeGen_target, (underlyingMap f.hom).target_app, ← he]
    exact (Y.obj.underlying.target_source k _).symm
  | edge x => exact (he x).symm

noncomputable def smallReverseWhiskerDesc {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (he : ∀ x, Y.obj.underlying.target n (e x) =
      (underlyingMap f.hom).app n (smallFreeGen hC q S n x)) : reverseWhiskerFree hC q n S ⟶ Y :=
  smallFreeDescCells hC q (smallReverseWhiskerCell hC q n f e)
    (fun k x => by
      have h := (S.underlying.whisker n true).presheafUnderlyingMap.source_app k x
      change (S.underlying.whisker n true).presheaf.underlying.source k x =
        (S.underlying.whisker n true).source k x at h
      exact (congrArg (smallReverseWhiskerCell hC q n f e k) h).trans
        (smallReverseWhiskerCell_source hC q n f e he k x))
    (fun k x => by
      have h := (S.underlying.whisker n true).presheafUnderlyingMap.target_app k x
      change (S.underlying.whisker n true).presheaf.underlying.target k x =
        (S.underlying.whisker n true).target k x at h
      exact (congrArg (smallReverseWhiskerCell hC q n f e k) h).trans
        (smallReverseWhiskerCell_target hC q n f e he k x))

@[simp] theorem smallReverseWhiskerDesc_base {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e) (he) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (smallReverseWhiskerDesc hC q n f e he).hom).app k (rwBase hC q n S k x) =
      (underlyingMap f.hom).app k (smallFreeGen hC q S k x) :=
  smallFreeDescCells_gen hC q _ _ _ k _

@[simp] theorem smallReverseWhiskerDesc_edge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e) (he) (x : S.underlying.Cell n) :
    (underlyingMap (smallReverseWhiskerDesc hC q n f e he).hom).app (n+1) (rwEdge hC q n S x) = e x :=
  smallFreeDescCells_gen hC q _ _ _ (n+1) _

noncomputable def reverseWhiskerIn {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) : (smallFree hC q).obj S ⟶ reverseWhiskerFree hC q n S :=
  (smallFree hC q).map ((GlobularPresheaf.whiskeringInclusion n true).app S)

@[simp] theorem reverseWhiskerIn_gen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (reverseWhiskerIn hC q n S).hom).app k (smallFreeGen hC q S k x) =
      rwBase hC q n S k x := smallFreeGen_map hC q _ k x

theorem inverseCell_inverse {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a : X.underlying.Cell (n+1)) :
    X.underlying.Joined (n+1) (X.inverseCell hC n (X.inverseCell hC n a)) a := by
  let D := disk C (n+1)
  let c := topCell C (n+1)
  let f : D ⟶ X := X.tupleMap (Shape.globe (n+1)) a
  have hf : (underlyingMap f).app (n+1) c = a := X.tupleMap_topCell (n+1) a
  let u := D.inverseCell hC n (D.inverseCell hC n c)
  have hp : D.underlying.Parallel (n+1) u c := by
    constructor <;> dsimp [u] <;> simp only [inverseCell_source, inverseCell_target]
  have h := (underlyingMap f).map_joined
    (freeShape_joined C hC (Shape.globe (n+1)) (n+1) u c hp)
  simpa only [u, map_inverseCell f, hf] using h

@[simp] theorem rwEdge_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (reverseWhiskerFree hC q n S).obj.underlying.source n (rwEdge hC q n S x) =
      smallFreeGen hC q ((GlobularPresheaf.whiskering n true).obj S) n (.tip x) := by
  unfold rwEdge
  erw [smallFreeGen_source]
  congr 1
  exact (S.underlying.whisker n true).presheafUnderlyingMap.source_app _ _

noncomputable def reverseWhiskerToWhisker {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) :
    reverseWhiskerFree hC q n S ⟶ whiskerFree hC q n S :=
  smallReverseWhiskerDesc hC q n (whiskerIn hC q n S)
    (fun x => (whiskerFree hC q n S).obj.inverseCell hC n (wEdge hC q n S x))
    (fun x => by rw [inverseCell_target, wEdge_source, whiskerIn_gen])

noncomputable def whiskerToReverseWhisker {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) :
    whiskerFree hC q n S ⟶ reverseWhiskerFree hC q n S :=
  smallWhiskerDesc hC q n (reverseWhiskerIn hC q n S)
    (fun x => (reverseWhiskerFree hC q n S).obj.inverseCell hC n (rwEdge hC q n S x))
    (fun x => by rw [inverseCell_source, rwEdge_target, reverseWhiskerIn_gen])

@[simp] theorem reverseWhiskerRound_base {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap ((reverseWhiskerToWhisker hC q n S) ≫
      (whiskerToReverseWhisker hC q n S)).hom).app k (rwBase hC q n S k x) =
      rwBase hC q n S k x := by
  change (underlyingMap (whiskerToReverseWhisker hC q n S).hom).app k
    ((underlyingMap (reverseWhiskerToWhisker hC q n S).hom).app k _) = _
  unfold reverseWhiskerToWhisker
  rw [smallReverseWhiskerDesc_base, whiskerIn_gen]
  unfold whiskerToReverseWhisker
  rw [smallWhiskerDesc_base, reverseWhiskerIn_gen]

@[simp] theorem reverseWhiskerRound_edge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (underlyingMap ((reverseWhiskerToWhisker hC q n S) ≫
      (whiskerToReverseWhisker hC q n S)).hom).app (n+1) (rwEdge hC q n S x) =
      (reverseWhiskerFree hC q n S).obj.inverseCell hC n
        ((reverseWhiskerFree hC q n S).obj.inverseCell hC n (rwEdge hC q n S x)) := by
  change (underlyingMap (whiskerToReverseWhisker hC q n S).hom).app (n+1)
    ((underlyingMap (reverseWhiskerToWhisker hC q n S).hom).app (n+1) _) = _
  unfold reverseWhiskerToWhisker
  rw [smallReverseWhiskerDesc_edge, map_inverseCell]
  unfold whiskerToReverseWhisker
  rw [smallWhiskerDesc_edge]

theorem reverseWhiskerRound_low {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (hk : k ≤ n)
    (x : (S.underlying.whisker n true).Cell k) :
    (underlyingMap ((reverseWhiskerToWhisker hC q n S) ≫
      (whiskerToReverseWhisker hC q n S)).hom).app k
        (smallFreeGen hC q ((GlobularPresheaf.whiskering n true).obj S) k x) =
      smallFreeGen hC q ((GlobularPresheaf.whiskering n true).obj S) k x := by
  cases x with
  | base k x => exact reverseWhiskerRound_base hC q n S k x
  | edge x => omega
  | tip x =>
    rw [← rwEdge_source, (underlyingMap _).source_app, reverseWhiskerRound_edge,
      inverseCell_source, inverseCell_target, rwEdge_source]

theorem reverseWhiskerRound_top {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0})
    (x : (S.underlying.whisker n true).Cell (n+1)) :
    (reverseWhiskerFree hC q n S).obj.underlying.Joined (n+1)
      ((underlyingMap ((reverseWhiskerToWhisker hC q n S) ≫
        (whiskerToReverseWhisker hC q n S)).hom).app (n+1)
          (smallFreeGen hC q ((GlobularPresheaf.whiskering n true).obj S) (n+1) x))
      (smallFreeGen hC q ((GlobularPresheaf.whiskering n true).obj S) (n+1) x) := by
  cases x with
  | base k x =>
    change (reverseWhiskerFree hC q n S).obj.underlying.Joined (n+1)
      ((underlyingMap ((reverseWhiskerToWhisker hC q n S) ≫
        (whiskerToReverseWhisker hC q n S)).hom).app (n+1) (rwBase hC q n S (n+1) x)) _
    rw [reverseWhiskerRound_base]
    exact (reverseWhiskerFree hC q n S).obj.joined_refl hC _ _
  | edge x =>
    change (reverseWhiskerFree hC q n S).obj.underlying.Joined (n+1)
      ((underlyingMap ((reverseWhiskerToWhisker hC q n S) ≫
        (whiskerToReverseWhisker hC q n S)).hom).app (n+1) (rwEdge hC q n S x)) _
    rw [reverseWhiskerRound_edge]
    exact inverseCell_inverse _ hC n _

theorem reverseWhiskerFree_bounded_hasFillers {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (H : ExpansionContraction hC q (n+1)) (S : Shape) (hS : S.height ≤ n+1) :
    (reverseWhiskerFree hC q n S.realize).obj.underlying.HasFillers := by
  have hb (k : ℕ) (hk : n+1 < k) : IsEmpty (S.realize.underlying.Cell k) :=
    S.2.bounded k (lt_of_le_of_lt hS hk)
  apply free_hasFillers_of_top_homotopy hC q n H
    (GlobularPresheaf.liftSmall.obj ((GlobularPresheaf.whiskering n true).obj S.realize))
    (fun k hk => ⟨fun x => (S.realize.underlying.whisker_bounded n true hb k hk).false x.down⟩)
    (whiskerFree hC q n S.realize) (smallFree_cofibrant hC q _)
    (whiskerFree_bounded_hasFillers hC q n H S hS)
    (reverseWhiskerToWhisker hC q n S.realize) (whiskerToReverseWhisker hC q n S.realize)
  · intro k hk x
    exact reverseWhiskerRound_low hC q n S.realize k hk x.down
  · intro x
    exact reverseWhiskerRound_top hC q n S.realize x.down

theorem reverseWhiskerFree_hom_ext {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    {f g : reverseWhiskerFree hC q n S ⟶ Y}
    (hb : ∀ k x, (underlyingMap f.hom).app k (rwBase hC q n S k x) =
      (underlyingMap g.hom).app k (rwBase hC q n S k x))
    (he : ∀ x, (underlyingMap f.hom).app (n+1) (rwEdge hC q n S x) =
      (underlyingMap g.hom).app (n+1) (rwEdge hC q n S x)) : f = g := by
  apply smallFree_hom_ext hC q
  intro k x
  cases x with
  | base k x => exact hb k x
  | edge x => exact he x
  | tip x =>
    rw [← rwEdge_source hC q k S x, (underlyingMap f.hom).source_app,
      (underlyingMap g.hom).source_app, he]

noncomputable def reverseWhiskerFreeMap {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) :
    reverseWhiskerFree hC q n S ⟶ reverseWhiskerFree hC q n T :=
  (smallFree hC q).map ((GlobularPresheaf.whiskering n true).map f)

@[simp] theorem reverseWhiskerFreeMap_base {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (reverseWhiskerFreeMap hC q n f).hom).app k (rwBase hC q n S k x) =
      rwBase hC q n T k ((GlobularPresheaf.underlyingMap f).app k x) :=
  smallFreeGen_map hC q _ k _

@[simp] theorem reverseWhiskerFreeMap_edge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) (x : S.underlying.Cell n) :
    (underlyingMap (reverseWhiskerFreeMap hC q n f).hom).app (n+1) (rwEdge hC q n S x) =
      rwEdge hC q n T ((GlobularPresheaf.underlyingMap f).app n x) :=
  smallFreeGen_map hC q _ (n+1) _

@[reassoc] theorem reverseWhiskerIn_naturality {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) :
    reverseWhiskerIn hC q n S ≫ reverseWhiskerFreeMap hC q n f =
      (smallFree hC q).map f ≫ reverseWhiskerIn hC q n T := by
  unfold reverseWhiskerIn reverseWhiskerFreeMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (smallFree hC q).map ((GlobularPresheaf.whiskeringInclusion n true).naturality f).symm

theorem reverseWhiskerFree_hasFillers_of_spine {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    {S T : GlobularPresheaf.{0}} (f : S ⟶ T)
    (hf : ∀ k, k ≤ n → Function.Bijective ((GlobularPresheaf.underlyingMap f).app k))
    (hS : ((smallFree hC q).obj S).obj.underlying.HasFillers)
    (hT : ((smallFree hC q).obj T).obj.underlying.HasFillers)
    (hW : (reverseWhiskerFree hC q n S).obj.underlying.HasFillers) :
    (reverseWhiskerFree hC q n T).obj.underlying.HasFillers := by
  let := cutoff_hasColimits hC q
  let F := smallFree hC q
  obtain ⟨M,i,p,s,hip,hsp,hi,hM,hp⟩ := exists_upper_resolution hC q n hnq
    (F.map f) (smallFree_cofibrant hC q T) hS hT
    (smallFree_low_bijective hC q n hnq f hf)
  let a := reverseWhiskerIn hC q n S
  let Q := pushout a i
  let j : reverseWhiskerFree hC q n S ⟶ Q := pushout.inl a i
  let k : M ⟶ Q := pushout.inr a i
  have hQ : Q.obj.underlying.HasFillers := upper_pushout_hasFillers hC q (n+1) H
    (IsPushout.of_hasPushout a i) hi (smallFree_cofibrant hC q S) hS hM
    (smallFree_cofibrant hC q _) hW
  let wm := reverseWhiskerFreeMap hC q n f
  let r : Q ⟶ reverseWhiskerFree hC q n T := pushout.desc wm (p ≫ reverseWhiskerIn hC q n T) (by
    rw [← Category.assoc, hip]
    exact reverseWhiskerIn_naturality hC q n f)
  have hjr : j ≫ r = wm := pushout.inl_desc _ _ _
  have hkr : k ≫ r = p ≫ reverseWhiskerIn hC q n T := pushout.inr_desc _ _ _
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
  let e (x : T.underlying.Cell n) := (underlyingMap j.hom).app (n+1) (rwEdge hC q n S (E.symm x))
  have he (x : T.underlying.Cell n) : Q.obj.underlying.target n (e x) =
      (underlyingMap (s ≫ k).hom).app n (smallFreeGen hC q T n x) := by
    change Q.obj.underlying.target n ((underlyingMap j.hom).app (n+1) _) =
      (underlyingMap k.hom).app n ((underlyingMap s.hom).app n _)
    rw [← (underlyingMap j.hom).target_app, rwEdge_target, hsgen]
    have hh := congrFun (congrArg (fun z => (underlyingMap z.hom).app n)
      (pushout.condition (f := a) (g := i))) (smallFreeGen hC q S n (E.symm x))
    exact (congrArg ((underlyingMap j.hom).app n)
      (reverseWhiskerIn_gen hC q n S n (E.symm x))).symm.trans hh
  let t := smallReverseWhiskerDesc hC q n (s ≫ k) e he
  have htr : t ≫ r = 𝟙 _ := by
    apply reverseWhiskerFree_hom_ext hC q n
    · intro l x
      change (underlyingMap r.hom).app l ((underlyingMap t.hom).app l _) = rwBase hC q n T l x
      have ht := smallReverseWhiskerDesc_base hC q n (s ≫ k) e he l x
      apply (congrArg ((underlyingMap r.hom).app l) ht).trans
      have hcomp : (s ≫ k) ≫ r = reverseWhiskerIn hC q n T := by
        rw [Category.assoc, hkr, ← Category.assoc, hsp, Category.id_comp]
      exact (congrFun (congrArg (fun z => (underlyingMap z.hom).app l) hcomp)
        (smallFreeGen hC q T l x)).trans (reverseWhiskerIn_gen hC q n T l x)
    · intro x
      change (underlyingMap r.hom).app (n+1) ((underlyingMap t.hom).app (n+1) _) = rwEdge hC q n T x
      have ht := smallReverseWhiskerDesc_edge hC q n (s ≫ k) e he x
      apply (congrArg ((underlyingMap r.hom).app (n+1)) ht).trans
      have hh := congrFun (congrArg (fun z => (underlyingMap z.hom).app (n+1)) hjr)
        (rwEdge hC q n S (E.symm x))
      exact hh.trans ((reverseWhiskerFreeMap_edge hC q n f (E.symm x)).trans
        (congrArg (rwEdge hC q n T) (E.apply_symm_apply x)))
  exact hQ.retract (underlyingMap t.hom) (underlyingMap r.hom)
    (congrArg (fun z : reverseWhiskerFree hC q n T ⟶ reverseWhiskerFree hC q n T => underlyingMap z.hom) htr)

theorem reverseWhiskerFree_hasFillers {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1)) (S : Shape) :
    (reverseWhiskerFree hC q n S.realize).obj.underlying.HasFillers := by
  let P := S.2.spine n
  exact reverseWhiskerFree_hasFillers_of_spine hC q n hnq H P.map P.low_bijective
    (smallShape_hasFillers hC q P.S) (smallShape_hasFillers hC q S)
    (reverseWhiskerFree_bounded_hasFillers hC q n H P.S P.height_le)

end GlobularTheory.Model
end Grothendieck

end OAI
