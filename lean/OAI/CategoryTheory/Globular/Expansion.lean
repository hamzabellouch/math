import OAI.CategoryTheory.Globular.SmallObject

namespace OAI

universe u v w

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits Opposite

def ExpansionContraction {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) : Prop :=
  ∀ {X Y : CutoffModels C q} (i : X ⟶ Y),
    (sourceClass hC q r).rlp.llp i → Cofibrant hC q X →
      X.obj.underlying.HasFillers → Y.obj.underlying.HasFillers

theorem boundary_rlp_of_source_rlp {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) {X Y : CutoffModels C q} (p : X ⟶ Y)
    (hX : X.obj.underlying.HasFillers) (hY : Y.obj.underlying.HasFillers)
    (hp : (sourceClass hC q r).rlp p) : (boundaryClass hC q r).rlp p := by
  rw [boundaryClass_rlp_iff]
  intro n hn
  rw [hasLiftingProperty_I_iff]
  apply GlobularSet.liftsBoundary_of_contractible (underlyingMap p.hom) hX hY
  exact (hasLiftingProperty_J_iff n p.hom).1
    ((sourceClass_rlp_iff hC q r p).1 hp n hn)

theorem upper_boundary_is_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) (H : ExpansionContraction hC q r)
    {X Y : CutoffModels C q} (i : X ⟶ Y)
    (hi : (boundaryClass hC q r).rlp.llp i) (hX : Cofibrant hC q X)
    (hXF : X.obj.underlying.HasFillers) (hYF : Y.obj.underlying.HasFillers) :
    (sourceClass hC q r).rlp.llp i := by
  let := sourceClass_smallObject hC q r
  let W := sourceClass hC q r
  let F := MorphismProperty.factorizationData W.rlp.llp W.rlp i
  have hZF := H F.i F.hi hX hXF
  have hFp := boundary_rlp_of_source_rlp hC q r F.p hZF hYF F.hp
  let := hi F.p hFp
  have sq : CommSq F.i i F.p (𝟙 Y) := ⟨by rw [Category.comp_id, F.fac]⟩
  let s := sq.lift
  have hs : i ≫ s = F.i := sq.fac_left
  have hsp : s ≫ F.p = 𝟙 Y := sq.fac_right
  intro P Q p hp
  constructor
  intro a b ab
  let := F.hi p hp
  have sq' : CommSq a F.i p (F.p ≫ b) := by
    constructor
    rw [← Category.assoc, F.fac, ab.w]
  refine CommSq.HasLift.mk' ⟨s ≫ sq'.lift, ?_, ?_⟩
  · rw [← Category.assoc, hs, sq'.fac_left]
  · rw [Category.assoc, sq'.fac_right, ← Category.assoc, hsp, Category.id_comp]

theorem upper_pushout_hasFillers {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) (H : ExpansionContraction hC q r)
    {X Y X' Y' : CutoffModels C q} {i : X ⟶ Y} {a : X ⟶ X'}
    {i' : X' ⟶ Y'} {b : Y ⟶ Y'} (sq : IsPushout a i i' b)
    (hi : (boundaryClass hC q r).rlp.llp i) (hX : Cofibrant hC q X)
    (hXF : X.obj.underlying.HasFillers) (hYF : Y.obj.underlying.HasFillers)
    (hX' : Cofibrant hC q X') (hX'F : X'.obj.underlying.HasFillers) :
    Y'.obj.underlying.HasFillers := by
  apply H i' _ hX' hX'F
  exact MorphismProperty.of_isPushout sq
    (upper_boundary_is_source hC q r H i hi hX hXF hYF)

theorem hasLiftingProperty_I_of_unique {C : GlobularTheory.{v}} {X Y : C.Model}
    (p : X ⟶ Y) (n : ℕ) (hX : Function.Bijective (X.underlying.boundary n))
    (hY : Function.Bijective (Y.underlying.boundary n)) :
    HasLiftingProperty (I C n) p := by
  rw [hasLiftingProperty_I_iff]
  intro b y hy
  obtain ⟨x, hx⟩ := hX.2 b
  refine ⟨x, hx, hY.1 ?_⟩
  rw [← (underlyingMap p).boundary_app, hx, hy]

theorem upper_cofibration_low_bijective {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r k : ℕ) (hkq : k ≤ q) (hkr : k < r)
    {X Y : CutoffModels C q} (i : X ⟶ Y)
    (hi : (boundaryClass hC q r).rlp.llp i) :
    Function.Bijective ((underlyingMap i.hom).app k) := by
  let X' : CutoffModels C q := ⟨chosenCutoff hC k X.obj,
    fun j hj => chosenCutoff_coskeletal hC k X.obj j (by omega)⟩
  let Y' : CutoffModels C q := ⟨chosenCutoff hC k Y.obj,
    fun j hj => chosenCutoff_coskeletal hC k Y.obj j (by omega)⟩
  let p : X' ⟶ Y' := ObjectProperty.homMk (((cutoffFunctor hC k).map i.hom).hom)
  let a : X ⟶ X' := ObjectProperty.homMk (cutoffUnit hC k X.obj)
  let b : Y ⟶ Y' := ObjectProperty.homMk (cutoffUnit hC k Y.obj)
  have hp : (boundaryClass hC q r).rlp p := by
    rw [boundaryClass_rlp_iff]
    intro j hj
    exact hasLiftingProperty_I_of_unique p.hom j
      (chosenCutoff_coskeletal hC k X.obj j (by omega))
      (chosenCutoff_coskeletal hC k Y.obj j (by omega))
  let := hi p hp
  have sq : CommSq a i p b := by
    constructor
    apply ObjectProperty.hom_ext
    exact ((cutoffAdjunction hC k).unit.naturality i.hom).symm
  let l := sq.lift
  have ha : Function.Bijective ((underlyingMap a.hom).app k) :=
    cutoffUnit_low_bijective hC k X.obj k le_rfl
  have hb : Function.Bijective ((underlyingMap b.hom).app k) :=
    cutoffUnit_low_bijective hC k Y.obj k le_rfl
  have hil (x : X.obj.underlying.Cell k) :
      (underlyingMap l.hom).app k ((underlyingMap i.hom).app k x) =
        (underlyingMap a.hom).app k x :=
    congrFun (congrArg (fun f => (underlyingMap f.hom).app k) sq.fac_left) x
  have hlp (y : Y.obj.underlying.Cell k) :
      (underlyingMap p.hom).app k ((underlyingMap l.hom).app k y) =
        (underlyingMap b.hom).app k y :=
    congrFun (congrArg (fun f => (underlyingMap f.hom).app k) sq.fac_right) y
  constructor
  · intro x y hxy
    apply ha.1
    rw [← hil, ← hil, hxy]
  · intro y
    obtain ⟨x, hx⟩ := ha.2 ((underlyingMap l.hom).app k y)
    refine ⟨x, hb.1 ?_⟩
    rw [← hlp, hil, hx, hlp]

theorem expansionContraction_top {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : ExpansionContraction hC q q := by
  intro X Y i hi _ hX
  have hib := sourceClass_cofibration_le hC q q i hi
  intro j b
  by_cases hj : q < j
  · exact (Y.property j hj).2 b
  · obtain ⟨b', hb'⟩ := ((underlyingMap i.hom).boundaryMap_bijective_of_low j
      (fun k hk => upper_cofibration_low_bijective hC q q k (by omega) (by omega) i hib)).2 b
    obtain ⟨x, hx⟩ := hX j b'
    exact ⟨(underlyingMap i.hom).app j x, by
      rw [← (underlyingMap i.hom).boundary_app, hx, hb']⟩

end Grothendieck.GlobularTheory.Model

namespace Grothendieck.GlobularSet

structure LiftStage {A X Y : GlobularSet.{v}} (p : Hom X Y) (f : Hom A Y) (n : ℕ) where
  app : ∀ k, k ≤ n → A.Cell k → X.Cell k
  source_app : ∀ k (h : k+1 ≤ n) x,
    app k (by omega) (A.source k x) = X.source k (app (k+1) h x)
  target_app : ∀ k (h : k+1 ≤ n) x,
    app k (by omega) (A.target k x) = X.target k (app (k+1) h x)
  fac : ∀ k (h : k ≤ n) x, p.app k (app k h x) = f.app k x

namespace LiftStage
variable {A X Y : GlobularSet.{v}} {p : Hom X Y} {f : Hom A Y}

noncomputable def zero (hp : LiftsBoundaries p) : LiftStage p f 0 := by
  have h x := hp 0 PUnit.unit (f.app 0 x) rfl
  choose z _ hz using h
  exact
    { app := fun k hk x => by
        have e : k = 0 := by omega
        subst k
        exact z x
      source_app := fun k hk => by omega
      target_app := fun k hk => by omega
      fac := fun k hk x => by
        have e : k = 0 := by omega
        subst k
        exact hz x }

def nextBoundary {n : ℕ} (a : LiftStage p f n) (x : A.Cell (n+1)) : X.Boundary (n+1) :=
  ⟨(a.app n le_rfl (A.source n x), a.app n le_rfl (A.target n x)), by
    cases n with
    | zero => trivial
    | succ n =>
      constructor
      · rw [← a.source_app n le_rfl, ← a.source_app n le_rfl, A.source_source]
      · rw [← a.target_app n le_rfl, ← a.target_app n le_rfl, A.target_source]⟩

noncomputable def succ {n : ℕ} (a : LiftStage p f n) (hp : LiftsBoundaries p) :
    LiftStage p f (n+1) := by
  have h x : ∃ z, X.boundary (n+1) z = a.nextBoundary x ∧
      p.app (n+1) z = f.app (n+1) x := by
    apply hp
    apply Subtype.ext
    exact Prod.ext ((f.source_app n x).symm.trans (a.fac n le_rfl _).symm)
      ((f.target_app n x).symm.trans (a.fac n le_rfl _).symm)
  choose z hz hzp using h
  have hs x := (congrArg (fun b => b.1.1) (hz x)).symm
  have ht x := (congrArg (fun b => b.1.2) (hz x)).symm
  exact
    { app := fun k hk x => if h : k ≤ n then a.app k h x else by
        have e : k = n+1 := by omega
        subst k
        exact z x
      source_app := fun k hk x => by
        dsimp only
        split_ifs with h h'
        · exact a.source_app k h' x
        · have e : k = n := by omega
          subst k
          exact hs x
        · omega
        · omega
      target_app := fun k hk x => by
        dsimp only
        split_ifs with h h'
        · exact a.target_app k h' x
        · have e : k = n := by omega
          subst k
          exact ht x
        · omega
        · omega
      fac := fun k hk x => by
        dsimp only
        split_ifs with h
        · exact a.fac k h x
        · have e : k = n+1 := by omega
          subst k
          exact hzp x }

@[simp] theorem succ_old {n : ℕ} (a : LiftStage p f n) (hp : LiftsBoundaries p)
    (k : ℕ) (hk : k ≤ n) (x : A.Cell k) :
    (a.succ hp).app k (by omega) x = a.app k hk x := by
  simp only [succ, dite_eq_left hk]

noncomputable def tower (hp : LiftsBoundaries p) : ∀ n, LiftStage p f n
  | 0 => zero hp
  | n+1 => (tower hp n).succ hp

end LiftStage

theorem LiftsBoundaries.lift {A X Y : GlobularSet.{v}} {p : Hom X Y}
    (hp : LiftsBoundaries p) (f : Hom A Y) : ∃ g : Hom A X, g.comp p = f := by
  let a (n : ℕ) := LiftStage.tower (f := f) hp n
  let g : Hom A X :=
    { app := fun n => (a n).app n le_rfl
      source_app := fun n x => by
        exact (LiftStage.succ_old (a n) hp n le_rfl _).symm.trans
          ((a (n+1)).source_app n le_rfl x)
      target_app := fun n x => by
        exact (LiftStage.succ_old (a n) hp n le_rfl _).symm.trans
          ((a (n+1)).target_app n le_rfl x) }
  exact ⟨g, by ext n x; exact (a n).fac n le_rfl x⟩

end Grothendieck.GlobularSet

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits Opposite

theorem isCellular_cutoff_cofibrant {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {X : C.Model} (hX : X.IsCellular) :
    Cofibrant hC q ((cutoffFunctor hC q).obj X) := by
  intro P Q p hp f
  have hp' : GlobularSet.LiftsBoundaries (underlyingMap p.hom) := by
    intro n
    exact (hasLiftingProperty_I_iff n p.hom).1
      ((boundaryClass_rlp_iff hC q 0 p).1 hp n (Nat.zero_le n))
  obtain ⟨A⟩ := hX
  let := A.linearOrder
  let := A.orderBot
  let := A.succOrder
  let := A.wellFoundedLT
  have : A.chain.F.IsWellOrderContinuous := A.chain.isWellOrderContinuous
  have : HasLiftingProperty (A.chain.incl.app ⊥) p.hom :=
    HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
      (hc := A.chain.isColimit)
      (fun j hj => (A.attachment j hj).hasLiftingProperty p.hom hp')
  let a : X ⟶ Q.obj := (cutoffAdjunction hC q).homEquiv X Q f
  let b : A.chain.F.obj ⊥ ⟶ P.obj := A.chain.isoBot.hom ≫ A.isInitial.to P.obj
  have sq : CommSq b (A.chain.incl.app ⊥) p.hom a := by
    constructor
    dsimp [b]
    rw [Category.assoc]
    rw [A.isInitial.hom_ext (A.isInitial.to P.obj ≫ p.hom) (A.start ≫ a)]
    rw [← Category.assoc]
    have w : A.chain.isoBot.hom ≫ A.start = A.chain.incl.app ⊥ := by
      exact (congrArg (A.chain.isoBot.hom ≫ ·) A.chain.fac.symm).trans
        (by simp only [Iso.hom_inv_id_assoc])
    rw [w]
  refine ⟨((cutoffAdjunction hC q).homEquiv X P).symm sq.lift, ?_⟩
  apply ((cutoffAdjunction hC q).homEquiv X Q).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact sq.fac_right

end Grothendieck.GlobularTheory.Model

namespace Grothendieck.GlobularPresheaf
open CategoryTheory Opposite

theorem liftsBoundaries_lift {A X Y : GlobularPresheaf.{v}} {p : X ⟶ Y}
    (hp : GlobularSet.LiftsBoundaries (underlyingMap p)) (f : A ⟶ Y) :
    ∃ g : A ⟶ X, g ≫ p = f := by
  obtain ⟨g, hg⟩ := hp.lift (underlyingMap f)
  let l : A ⟶ X := A.underlyingPresheafIso.inv ≫ g.presheafMap ≫ X.underlyingPresheafIso.hom
  refine ⟨l, ?_⟩
  apply underlyingMap_injective
  exact hg

end Grothendieck.GlobularPresheaf

end OAI
