import OAI.CategoryTheory.Globular.DiskComparison

namespace OAI

universe u v w

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace Table

structure SpineData {n : ℕ} (T : Table n) (q : ℕ) where
  S : Shape
  last_eq : S.1 = min n (q+1)
  height_le : S.height ≤ q+1
  map : S.realize ⟶ T.realize
  low_bijective : ∀ k, k ≤ q → Function.Bijective (map.app (op (Globe.mk k)))
  last_low : ∀ k, k ≤ q →
    (S.last ≫ map).app (op (Globe.mk k)) =
      (GlobularPresheaf.faceLE (show S.1 ≤ n by rw [last_eq]; exact min_le_left _ _) false ≫
        T.lastInclusion).app (op (Globe.mk k))

namespace SpineData

noncomputable def globe (q n : ℕ) : (Table.globe n).SpineData q where
  S := Shape.globe (min n (q+1))
  last_eq := rfl
  height_le := min_le_right _ _
  map := GlobularPresheaf.faceLE (min_le_left n (q+1)) false
  low_bijective _ hk := GlobularPresheaf.faceLE_cap_bijective rfl _ hk
  last_low _ _ := rfl

noncomputable def attachHigh {n : ℕ} {T : Table n} {q : ℕ}
    (P : T.SpineData q) (b h : ℕ) (hl : b < n) (hr : b < h) (hb : q < b) :
    (Table.attach T b h hl hr).SpineData q := by
  have hdim : P.S.1 = q+1 := by rw [P.last_eq]; omega
  have hn : P.S.1 ≤ n := by omega
  have hh : P.S.1 ≤ h := by omega
  have hsb : P.S.1 ≤ b := by omega
  let i : T.realize ⟶ (Table.attach T b h hl hr).realize := Shape.inl ⟨n,T⟩ b h hl hr
  let j : GlobularPresheaf.disk h ⟶ (Table.attach T b h hl hr).realize :=
    Shape.inr ⟨n,T⟩ b h hl hr
  have sq : IsPushout (GlobularPresheaf.face hl true ≫ T.lastInclusion)
      (GlobularPresheaf.face hr false) i j := IsPushout.of_hasPushout _ _
  refine ⟨P.S, ?_, P.height_le, P.map ≫ i, ?_, ?_⟩
  · rw [hdim]
    omega
  · intro k hk
    let E := (evaluation Globeᵒᵖ (Type 0)).obj (op (Globe.mk k))
    have hg : IsIso (E.map (GlobularPresheaf.face hr false)) :=
      (isIso_iff_bijective _).2 (GlobularPresheaf.face_low_bijective hr (by omega) false)
    have hi : IsIso (E.map i) := (sq.map E).isIso_inl_of_isIso hg
    exact ((isIso_iff_bijective _).1 hi).comp (P.low_bijective k hk)
  · intro k hk
    let c := op (Globe.mk k)
    let bridge := GlobularPresheaf.faceLE hsb false
    have e1 : (GlobularPresheaf.faceLE hn false).app c =
        (bridge ≫ GlobularPresheaf.face hl true).app c := by
      change (uliftYoneda.map (Globe.faceLE hn false)).app c =
        (uliftYoneda.map (Globe.faceLE hsb false) ≫ uliftYoneda.map (Globe.face hl true)).app c
      rw [← uliftYoneda.map_comp]
      exact GlobularPresheaf.globeMap_low_equal _ _ (by omega)
    have e2 : (bridge ≫ GlobularPresheaf.face hr false).app c =
        (GlobularPresheaf.faceLE hh false).app c := by
      change (uliftYoneda.map (Globe.faceLE hsb false) ≫ uliftYoneda.map (Globe.face hr false)).app c =
        (uliftYoneda.map (Globe.faceLE hh false)).app c
      rw [← uliftYoneda.map_comp]
      exact GlobularPresheaf.globeMap_low_equal _ _ (by omega)
    have hp := P.last_low k hk
    have hw := congrArg (fun a => a.app c) sq.w
    simp only [NatTrans.comp_app] at hp hw e1 e2
    change P.S.last.app c ≫ (P.map.app c ≫ i.app c) =
      (GlobularPresheaf.faceLE hh false).app c ≫ j.app c
    rw [← Category.assoc, hp, e1]
    calc
      ((bridge.app c ≫ (GlobularPresheaf.face hl true).app c) ≫ T.lastInclusion.app c) ≫ i.app c =
          bridge.app c ≫ (((GlobularPresheaf.face hl true).app c ≫ T.lastInclusion.app c) ≫ i.app c) := by simp only [Category.assoc]
      _ = bridge.app c ≫ ((GlobularPresheaf.face hr false).app c ≫ j.app c) := by rw [hw]
      _ = (GlobularPresheaf.faceLE hh false).app c ≫ j.app c := by rw [← Category.assoc, e2]

end SpineData
end Table

namespace Table.SpineData

noncomputable def attachLow {n : ℕ} {T : Table n} {q : ℕ}
    (P : T.SpineData q) (b h : ℕ) (hl : b < n) (hr : b < h) (hb : b ≤ q) :
    (Table.attach T b h hl hr).SpineData q := by
  have hn : P.S.1 ≤ n := by rw [P.last_eq]; exact min_le_left _ _
  have hbl : b < P.S.1 := by rw [P.last_eq]; omega
  have hbr : b < min h (q+1) := by omega
  let N : Shape := P.S.attach b (min h (q+1)) hbl hbr
  let il : P.S.realize ⟶ N.realize := Shape.inl P.S b (min h (q+1)) hbl hbr
  let ir : GlobularPresheaf.disk (min h (q+1)) ⟶ N.realize :=
    Shape.inr P.S b (min h (q+1)) hbl hbr
  let cap := GlobularPresheaf.faceLE (min_le_left h (q+1)) false
  let il' : T.realize ⟶ (Table.attach T b h hl hr).realize := Shape.inl ⟨n,T⟩ b h hl hr
  let ir' : GlobularPresheaf.disk h ⟶ (Table.attach T b h hl hr).realize :=
    Shape.inr ⟨n,T⟩ b h hl hr
  have sl : GlobularPresheaf.face hbl true ≫ P.S.last ≫ P.map =
      GlobularPresheaf.face hl true ≫ T.lastInclusion := by
    rw [GlobularPresheaf.face_comp_eq_of_app_eq hbl true _ _ (P.last_low b hb)]
    rw [← Category.assoc,
      GlobularPresheaf.face_comp_faceLE hbl hn true false]
  have sr : GlobularPresheaf.face hbr false ≫ cap = GlobularPresheaf.face hr false :=
    GlobularPresheaf.face_comp_faceLE hbr _ false false
  have sq : IsPushout (GlobularPresheaf.face hbl true ≫ P.S.last)
      (GlobularPresheaf.face hbr false) il ir := IsPushout.of_hasPushout _ _
  have sq' : IsPushout (GlobularPresheaf.face hl true ≫ T.lastInclusion)
      (GlobularPresheaf.face hr false) il' ir' := IsPushout.of_hasPushout _ _
  let f : N.realize ⟶ (Table.attach T b h hl hr).realize :=
    sq.desc (P.map ≫ il') (cap ≫ ir') (by
      calc
        (GlobularPresheaf.face hbl true ≫ P.S.last) ≫ (P.map ≫ il') =
            (GlobularPresheaf.face hbl true ≫ P.S.last ≫ P.map) ≫ il' := by simp only [Category.assoc]
        _ = (GlobularPresheaf.face hl true ≫ T.lastInclusion) ≫ il' := congrArg (fun a => a ≫ il') sl
        _ = GlobularPresheaf.face hr false ≫ ir' := sq'.w
        _ = GlobularPresheaf.face hbr false ≫ (cap ≫ ir') := by rw [← Category.assoc, sr])
  have fi : il ≫ f = P.map ≫ il' := sq.inl_desc _ _ _
  have fj : ir ≫ f = cap ≫ ir' := sq.inr_desc _ _ _
  refine ⟨N, rfl, ?_, f, ?_, ?_⟩
  · exact max_le P.height_le (min_le_right _ _)
  · intro k hk
    let E := (evaluation Globeᵒᵖ (Type 0)).obj (op (Globe.mk k))
    have : IsIso (E.map P.map) := (isIso_iff_bijective _).2 (P.low_bijective k hk)
    have : IsIso (E.map cap) := (isIso_iff_bijective _).2
      (GlobularPresheaf.faceLE_cap_bijective rfl _ hk)
    apply (isIso_iff_bijective _).1
    apply GlobularPresheaf.pushout_comparison_isIso (sq.map E) (sq'.map E)
      (𝟙 _) (E.map P.map) (E.map cap) (E.map f)
    · simpa only [Category.id_comp, ← E.map_comp, Category.assoc] using congrArg E.map sl
    · simpa only [Category.id_comp, ← E.map_comp] using congrArg E.map sr
    · simpa only [← E.map_comp] using congrArg E.map fi
    · simpa only [← E.map_comp] using congrArg E.map fj
  · intro k hk
    exact congrArg (fun a => a.app (op (Globe.mk k))) fj

end Table.SpineData

namespace Table

noncomputable def spine (q : ℕ) : {n : ℕ} → (T : Table n) → T.SpineData q
  | _, .globe n => SpineData.globe q n
  | _, .attach T b h hl hr =>
    if hb : b ≤ q then (spine q T).attachLow b h hl hr hb
    else (spine q T).attachHigh b h hl hr (by omega)

end Table

namespace GlobularPresheaf

theorem underlyingMap_injective {X Y : GlobularPresheaf.{u}} :
    Function.Injective (fun f : X ⟶ Y => underlyingMap f) := by
  intro f g h
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  exact congrArg (fun a => a.app k.unop.dim x) h

theorem existsUnique_factor_low_bijective {X R Y : GlobularPresheaf.{u}}
    (η : X ⟶ R) (f : X ⟶ Y) (q : ℕ)
    (hη : ∀ k, k ≤ q → Function.Bijective (η.app (op (Globe.mk k))))
    (hY : ∀ j, q < j → Function.Bijective (Y.underlying.boundary j)) :
    ∃! g : R ⟶ Y, η ≫ g = f := by
  obtain ⟨g, hg, hu⟩ := GlobularSet.existsUnique_factor_low_bijective
    (underlyingMap η) (underlyingMap f) q hη hY
  let l : R ⟶ Y := R.underlyingPresheafIso.inv ≫ g.presheafMap ≫ Y.underlyingPresheafIso.hom
  have hl : underlyingMap l = g := by ext n x; rfl
  have hf : η ≫ l = f := by
    apply underlyingMap_injective
    change (underlyingMap η).comp (underlyingMap l) = underlyingMap f
    rw [hl, hg]
  refine ⟨l, hf, ?_⟩
  intro l' hl'
  apply underlyingMap_injective
  apply Eq.trans _ hl.symm
  apply hu
  exact congrArg (fun a : X ⟶ Y => underlyingMap a) hl'

theorem precomp_bijective_low {X R Y : GlobularPresheaf.{u}}
    (η : X ⟶ R) (q : ℕ)
    (hη : ∀ k, k ≤ q → Function.Bijective (η.app (op (Globe.mk k))))
    (hY : ∀ j, q < j → Function.Bijective (Y.underlying.boundary j)) :
    Function.Bijective (fun g : R ⟶ Y => η ≫ g) := by
  constructor
  · intro a b hab
    obtain ⟨_, _, hu⟩ := existsUnique_factor_low_bijective η (η ≫ b) q hη hY
    exact (hu a hab).trans (hu b rfl).symm
  · intro f
    obtain ⟨g, hg, _⟩ := existsUnique_factor_low_bijective η f q hη hY
    exact ⟨g, hg⟩

end GlobularPresheaf

namespace TupleSystem

theorem map_bijective_of_low {T : TupleSystem.{v}} {S R : Shape} (f : S ⟶ R)
    (q : ℕ) (hf : ∀ k, k ≤ q → Function.Bijective (f.app (op (Globe.mk k))))
    (hT : ∀ j, q < j → Function.Bijective (T.underlying.boundary j)) :
    Function.Bijective (T.presheaf.map f.op) := by
  have hg : ∀ k, k ≤ q → Function.Bijective
      ((Shape.liftedRealization.{v}.map f).app (op (Globe.mk k))) := by
    intro k hk
    exact ULift.map_bijective.mpr (hf k hk)
  have hb := GlobularPresheaf.precomp_bijective_low
    (Y := T.globularPresheaf) (Shape.liftedRealization.map f) q hg hT
  have hn (x : T.presheaf.obj (op R)) :
      T.evaluation.app (op S) (T.presheaf.map f.op x) =
        Shape.liftedRealization.map f ≫ T.evaluation.app (op R) x :=
    ConcreteCategory.congr_hom (T.evaluation.naturality f.op) x
  constructor
  · intro x y h
    apply (T.evaluation_bijective R).1
    apply hb.1
    exact (hn x).symm.trans ((congrArg (T.evaluation.app (op S)) h).trans (hn y))
  · intro y
    obtain ⟨g, hg⟩ := hb.2 (T.evaluation.app (op S) y)
    obtain ⟨x, hx⟩ := (T.evaluation_bijective R).2 g
    refine ⟨x, (T.evaluation_bijective S).1 ?_⟩
    exact (hn x).trans ((congrArg (fun g => Shape.liftedRealization.map f ≫ g) hx).trans hg)

end TupleSystem

end Grothendieck

end OAI
