import OAI.CategoryTheory.Globular.Groupoid

namespace OAI

universe u v w

namespace Grothendieck.GlobularSet

def LiftsBoundary {X Y : GlobularSet.{v}} (p : Hom X Y) (k : ℕ) : Prop :=
  ∀ (bd : X.Boundary k) (y : Y.Cell k), Y.boundary k y = p.boundaryMap k bd →
    ∃ x : X.Cell k, X.boundary k x = bd ∧ p.app k x = y

structure RelativeLiftStage {A B X Y : GlobularSet.{v}}
    (i : Hom A B) (a : Hom A X) (p : Hom X Y) (b : Hom B Y) (n : ℕ)
    extends LiftStage p b n where
  on_domain : ∀ k (hk : k ≤ n) x, app k hk (i.app k x) = a.app k x

namespace RelativeLiftStage
variable {A B X Y : GlobularSet.{v}} {i : Hom A B} {a : Hom A X}
  {p : Hom X Y} {b : Hom B Y}

theorem exists_cell (r k : ℕ)
    (hi : Function.Injective (i.app k))
    (hlo : k < r → Function.Surjective (i.app k))
    (hp : r ≤ k → LiftsBoundary p k)
    (sq : a.comp p = i.comp b)
    (bd : B.Cell k → X.Boundary k)
    (hbd : ∀ x, X.boundary k (a.app k x) = bd (i.app k x))
    (hbp : ∀ y, Y.boundary k (b.app k y) = p.boundaryMap k (bd y)) :
    ∃ z : B.Cell k → X.Cell k,
      (∀ y, X.boundary k (z y) = bd y) ∧
      (∀ y, p.app k (z y) = b.app k y) ∧
      (∀ x, z (i.app k x) = a.app k x) := by
  classical
  have e x : p.app k (a.app k x) = b.app k (i.app k x) :=
    congrFun (congrArg (fun t => t.app k) sq) x
  have hz y : ∃ z : X.Cell k, X.boundary k z = bd y ∧ p.app k z = b.app k y ∧
      ∀ x, i.app k x = y → z = a.app k x := by
    by_cases hy : ∃ x, i.app k x = y
    · obtain ⟨x, rfl⟩ := hy
      exact ⟨a.app k x, hbd x, e x, fun x' hx' => congrArg (a.app k) (hi hx').symm⟩
    · have hk : r ≤ k := by
        by_contra hk
        exact hy (hlo (by omega) y)
      obtain ⟨z, hz, hzp⟩ := hp hk (bd y) (b.app k y) (hbp y)
      exact ⟨z, hz, hzp, fun x hx => (hy ⟨x,hx⟩).elim⟩
  choose z hb hf ho using hz
  exact ⟨z, hb, hf, fun x => ho _ x rfl⟩

noncomputable def zero (r : ℕ)
    (hi : ∀ k, Function.Injective (i.app k))
    (hlo : ∀ k, k < r → Function.Surjective (i.app k))
    (hp : ∀ k, r ≤ k → LiftsBoundary p k) (sq : a.comp p = i.comp b) :
    RelativeLiftStage i a p b 0 := by
  choose z _hb hf ho using exists_cell r 0 (hi 0) (hlo 0) (hp 0) sq
    (fun _ => PUnit.unit) (fun _ => rfl) (fun _ => rfl)
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
        exact hf x
      on_domain := fun k hk x => by
        have e : k = 0 := by omega
        subst k
        exact ho x }

noncomputable def succ (r : ℕ)
    (hi : ∀ k, Function.Injective (i.app k))
    (hlo : ∀ k, k < r → Function.Surjective (i.app k))
    (hp : ∀ k, r ≤ k → LiftsBoundary p k) (sq : a.comp p = i.comp b)
    {n : ℕ} (s : RelativeLiftStage i a p b n) : RelativeLiftStage i a p b (n+1) := by
  let bd := s.toLiftStage.nextBoundary
  have hbd x : X.boundary (n+1) (a.app (n+1) x) = bd (i.app (n+1) x) := by
    apply Subtype.ext
    apply Prod.ext
    · change X.source n (a.app (n+1) x) = s.app n le_rfl (B.source n (i.app (n+1) x))
      rw [← a.source_app, ← i.source_app, s.on_domain]
    · change X.target n (a.app (n+1) x) = s.app n le_rfl (B.target n (i.app (n+1) x))
      rw [← a.target_app, ← i.target_app, s.on_domain]
  have hbp y : Y.boundary (n+1) (b.app (n+1) y) = p.boundaryMap (n+1) (bd y) := by
    apply Subtype.ext
    apply Prod.ext
    · exact (b.source_app n y).symm.trans (s.fac n le_rfl _).symm
    · exact (b.target_app n y).symm.trans (s.fac n le_rfl _).symm
  choose z hb hf ho using exists_cell r (n+1) (hi _) (hlo _) (hp _) sq bd hbd hbp
  let t := s.toLiftStage.extendTop z
    (fun y => congrArg (fun c => c.1.1) (hb y))
    (fun y => congrArg (fun c => c.1.2) (hb y)) hf
  refine { toLiftStage := t, on_domain := ?_ }
  intro k hk x
  dsimp only [t, LiftStage.extendTop]
  split_ifs with h
  · exact s.on_domain k h x
  · have e : k = n+1 := by omega
    subst k
    exact ho x

theorem succ_old (r : ℕ)
    (hi : ∀ k, Function.Injective (i.app k))
    (hlo : ∀ k, k < r → Function.Surjective (i.app k))
    (hp : ∀ k, r ≤ k → LiftsBoundary p k) (sq : a.comp p = i.comp b)
    {n : ℕ} (s : RelativeLiftStage i a p b n) (k : ℕ) (hk : k ≤ n) (x : B.Cell k) :
    (s.succ r hi hlo hp sq).app k (by omega) x = s.app k hk x := by
  dsimp only [succ, LiftStage.extendTop]
  simp only [dite_eq_left hk]

end RelativeLiftStage

theorem relative_lift {A B X Y : GlobularSet.{v}} (i : Hom A B) (a : Hom A X)
    (p : Hom X Y) (b : Hom B Y) (r : ℕ)
    (hi : ∀ k, Function.Injective (i.app k))
    (hlo : ∀ k, k < r → Function.Surjective (i.app k))
    (hp : ∀ k, r ≤ k → LiftsBoundary p k) (sq : a.comp p = i.comp b) :
    ∃ l : Hom B X, i.comp l = a ∧ l.comp p = b := by
  let s : (n : ℕ) → RelativeLiftStage i a p b n :=
    Nat.rec (RelativeLiftStage.zero r hi hlo hp sq) (fun _ s => s.succ r hi hlo hp sq)
  let l : Hom B X :=
    { app := fun n => (s n).app n le_rfl
      source_app := fun n x =>
        ((s n).succ_old r hi hlo hp sq n le_rfl _).symm.trans
          ((s (n+1)).source_app n le_rfl x)
      target_app := fun n x =>
        ((s n).succ_old r hi hlo hp sq n le_rfl _).symm.trans
          ((s (n+1)).target_app n le_rfl x) }
  refine ⟨l, ?_, ?_⟩
  · ext n x
    exact (s n).on_domain n le_rfl x
  · ext n x
    exact (s n).fac n le_rfl x

end Grothendieck.GlobularSet

namespace Grothendieck.GlobularPresheaf
open CategoryTheory Opposite

theorem relative_lift {A B X Y : GlobularPresheaf.{v}}
    (i : A ⟶ B) (a : A ⟶ X) (p : X ⟶ Y) (b : B ⟶ Y) (r : ℕ)
    (hi : ∀ k, Function.Injective ((underlyingMap i).app k))
    (hlo : ∀ k, k < r → Function.Surjective ((underlyingMap i).app k))
    (hp : ∀ k, r ≤ k → GlobularSet.LiftsBoundary (underlyingMap p) k)
    (sq : a ≫ p = i ≫ b) : ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  obtain ⟨g, hg₀, hg₁⟩ := GlobularSet.relative_lift (underlyingMap i)
    (underlyingMap a) (underlyingMap p) (underlyingMap b) r hi hlo hp
      (congrArg underlyingMap sq)
  let l : B ⟶ X := B.underlyingPresheafIso.inv ≫ g.presheafMap ≫ X.underlyingPresheafIso.hom
  exact ⟨l, underlyingMap_injective hg₀, underlyingMap_injective hg₁⟩

end Grothendieck.GlobularPresheaf

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits Opposite

theorem cutoffFreeGlobular_map_cofibration {C : GlobularTheory.{v}}
    (hC : C.IsCoherator) (q r : ℕ) {S T : GlobularPresheaf.{v}} (i : S ⟶ T)
    (hi : ∀ k, Function.Injective ((GlobularPresheaf.underlyingMap i).app k))
    (hlo : ∀ k, k < r → Function.Surjective ((GlobularPresheaf.underlyingMap i).app k)) :
    (boundaryClass hC q r).rlp.llp ((cutoffFreeGlobular hC q).map i) := by
  intro P Q p hp
  constructor
  intro a b sq
  let A := cutoffGlobularAdjunction hC q
  let U := cutoffForgetGlobular C q
  let a' := A.homEquiv S P a
  let b' := A.homEquiv T Q b
  have hs : a' ≫ U.map p = i ≫ b' := by
    rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
    exact congrArg (A.homEquiv S Q) sq.w
  have hp' : ∀ k, r ≤ k → GlobularSet.LiftsBoundary
      (GlobularPresheaf.underlyingMap (U.map p)) k := by
    intro k hk
    exact (hasLiftingProperty_I_iff k p.hom).1
      ((boundaryClass_rlp_iff hC q r p).1 hp k hk)
  obtain ⟨l, hl₀, hl₁⟩ := GlobularPresheaf.relative_lift i a' (U.map p) b' r hi hlo hp' hs
  refine CommSq.HasLift.mk' ⟨(A.homEquiv T P).symm l, ?_, ?_⟩
  · apply (A.homEquiv S P).injective
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hl₀
  · apply (A.homEquiv T Q).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    exact hl₁

theorem cutoff_hasLimits {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : HasLimitsOfSize.{v,v} (CutoffModels C q) := by
  let := cutoffReflective hC q
  exact hasLimits_of_reflective (ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q))

theorem cutoff_hasFillers_iff {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : CutoffModels C q) :
    X.obj.underlying.HasFillers ↔ ∀ n (f : cutoffBoundary hC q n ⟶ X),
      ∃ g : cutoffDisk hC q n ⟶ X, cutoffI hC q n ≫ g = f := by
  rw [hasFillers_iff]
  let A := cutoffAdjunction hC q
  constructor
  · intro h n f
    obtain ⟨g, hg⟩ := h n (A.homEquiv _ X f)
    refine ⟨(A.homEquiv _ X).symm g, (A.homEquiv _ X).injective ?_⟩
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hg
  · intro h n f
    obtain ⟨g, hg⟩ := h n ((A.homEquiv _ X).symm f)
    refine ⟨A.homEquiv _ X g, ?_⟩
    have e := congrArg (A.homEquiv _ X) hg
    simpa only [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply] using e

end Grothendieck.GlobularTheory.Model

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits

theorem lifting_terminal_iff {K : Type u} [Category.{v} K] [HasTerminal K]
    {A B : K} (j : A ⟶ B) (X : K) :
    HasLiftingProperty j (terminal.from X) ↔ ∀ a : A ⟶ X, ∃ b : B ⟶ X, j ≫ b = a := by
  constructor
  · intro h a
    let := h
    have sq : CommSq a j (terminal.from X) (terminal.from B) := ⟨terminal.hom_ext _ _⟩
    exact ⟨sq.lift, sq.fac_left⟩
  · intro h
    constructor
    intro a b _sq
    obtain ⟨l, hl⟩ := h a
    exact CommSq.HasLift.mk' ⟨l, hl, terminal.hom_ext _ _⟩

namespace GlobularTheory.Model

structure CutoffPathData {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) (Y : CutoffModels C q) where
  P : CutoffModels C q
  p₀ : P ⟶ Y
  p₁ : P ⟶ Y
  lifts₀ : (boundaryClass hC q 0).rlp p₀
  lifts₁ : (boundaryClass hC q 0).rlp p₁
  joint : ∀ k, r ≤ k → ∀ (t : cutoffDisk hC q k ⟶ P)
    (u₀ u₁ : cutoffDisk hC q (k+1) ⟶ Y),
    t ≫ p₀ = cutoffJ hC q k ≫ u₀ → t ≫ p₁ = cutoffJ hC q k ≫ u₁ →
    ∃ l : cutoffDisk hC q (k+1) ⟶ P,
      cutoffJ hC q k ≫ l = t ∧ l ≫ p₀ = u₀ ∧ l ≫ p₁ = u₁

theorem CutoffPathData.joint_rlp {C : GlobularTheory.{v}} {hC : C.IsCoherator}
    {q r : ℕ} {Y : CutoffModels C q} (D : CutoffPathData hC q r Y)
    [HasBinaryProduct Y Y] : (sourceClass hC q r).rlp (prod.lift D.p₀ D.p₁) := by
  rintro _ _ j ⟨⟨k,hk⟩⟩
  constructor
  intro a b sq
  have hf : a ≫ D.p₀ = cutoffJ hC q k ≫ (b ≫ prod.fst) := by
    have e := congrArg (· ≫ prod.fst) sq.w
    simpa only [Category.assoc, prod.lift_fst] using e
  have hg : a ≫ D.p₁ = cutoffJ hC q k ≫ (b ≫ prod.snd) := by
    have e := congrArg (· ≫ prod.snd) sq.w
    simpa only [Category.assoc, prod.lift_snd] using e
  obtain ⟨l, hl, hl₀, hl₁⟩ := D.joint k hk a (b ≫ prod.fst) (b ≫ prod.snd) hf hg
  refine CommSq.HasLift.mk' ⟨l, hl, ?_⟩
  apply prod.hom_ext
  · simpa only [Category.assoc, prod.lift_fst] using hl₀
  · simpa only [Category.assoc, prod.lift_snd] using hl₁

theorem expansionContraction_of_paths {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) (D : ∀ Y, Nonempty (CutoffPathData hC q r Y)) :
    ExpansionContraction hC q r := by
  let := cutoff_hasLimits hC q
  intro X Y i hi hX hXF
  have hiI : (boundaryClass hC q 0).rlp.llp i :=
    boundaryClass_cofibration_le hC q 0 r (Nat.zero_le r) i
      (sourceClass_cofibration_le hC q r i hi)
  have ht : (boundaryClass hC q 0).rlp (terminal.from X) := by
    rintro A B j ⟨⟨k,_⟩⟩
    rw [lifting_terminal_iff]
    exact (cutoff_hasFillers_iff hC q _).1 hXF k
  let := hiI (terminal.from X) ht
  have retractSq : CommSq (𝟙 X) i (terminal.from X) (terminal.from Y) :=
    ⟨terminal.hom_ext _ _⟩
  let z : Y ⟶ X := retractSq.lift
  have hz : i ≫ z = 𝟙 X := retractSq.fac_left
  obtain ⟨P⟩ := D Y
  obtain ⟨a, ha⟩ := hX P.p₀ P.lifts₀ i
  let u : X ⟶ Y := a ≫ P.p₁
  let := hi (prod.lift P.p₀ P.p₁) P.joint_rlp
  have sq : CommSq a i (prod.lift P.p₀ P.p₁) (prod.lift (𝟙 Y) (z ≫ u)) := by
    constructor
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst, Category.comp_id] using ha
    · simp only [Category.assoc, prod.lift_snd]
      rw [← Category.assoc i, hz, Category.id_comp]
  have hf₀ : sq.lift ≫ P.p₀ = 𝟙 Y := by
    have e := congrArg (· ≫ prod.fst) sq.fac_right
    simpa only [Category.assoc, prod.lift_fst] using e
  have hf₁ : sq.lift ≫ P.p₁ = z ≫ u := by
    have e := congrArg (· ≫ prod.snd) sq.fac_right
    simpa only [Category.assoc, prod.lift_snd] using e
  refine GlobularSet.hasFillers_of_endpoint_factorization hXF
    (underlyingMap u.hom) (underlyingMap z.hom) (underlyingMap sq.lift.hom)
    (underlyingMap P.p₀.hom) (underlyingMap P.p₁.hom)
    (congrArg (fun t : Y ⟶ Y => underlyingMap t.hom) hf₀)
    (congrArg (fun t : Y ⟶ Y => underlyingMap t.hom) hf₁) ?_
  intro k
  exact (hasLiftingProperty_I_iff k P.p₁.hom).1
    ((boundaryClass_rlp_iff hC q 0 P.p₁).1 P.lifts₁ k (Nat.zero_le k))

end GlobularTheory.Model
end Grothendieck

namespace Grothendieck.GlobularSet

theorem ExactBoundaryTest.of_retract_factor {X Y : GlobularSet.{u}}
    (i : Hom X Y) (r : Hom Y X) (u : Hom X Y) (hir : i.comp r = Hom.id X)
    (hv : ExactBoundaryTest (r.comp u)) (units : ∀ k x, Y.Joined k x x) :
    ExactBoundaryTest i := by
  intro k bd y hy
  have hx : X.boundary k (r.app k y) = bd := by
    rw [← r.boundary_app, hy, ← Hom.boundaryMap_comp, hir, Hom.boundaryMap_id]
  refine ⟨r.app k y, hx, hv.reflects_joined ?_ ?_⟩
  · rw [parallel_iff_boundary_eq, ← i.boundary_app, hx, hy]
  · have e : r.app k (i.app k (r.app k y)) = r.app k y :=
      congrFun (congrArg (fun t => t.app k) hir) (r.app k y)
    change Y.Joined k (u.app k (r.app k (i.app k (r.app k y)))) (u.app k (r.app k y))
    rw [e]
    exact units k _

end Grothendieck.GlobularSet

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits

theorem weakEquivalence_of_cutoff_path {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) {X Y : CutoffModels C q} (i : X ⟶ Y)
    (hi : (sourceClass hC q r).rlp.llp i) (hX : Cofibrant hC q X)
    (z : Y ⟶ X) (hz : i ≫ z = 𝟙 X) (P : CutoffPathData hC q r Y) :
    WeakEquivalence hC i.hom := by
  let := cutoff_hasLimits hC q
  obtain ⟨a, ha⟩ := hX P.p₀ P.lifts₀ i
  let u : X ⟶ Y := a ≫ P.p₁
  let := hi (prod.lift P.p₀ P.p₁) P.joint_rlp
  have sq : CommSq a i (prod.lift P.p₀ P.p₁) (prod.lift (𝟙 Y) (z ≫ u)) := by
    constructor
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst, Category.comp_id] using ha
    · simp only [Category.assoc, prod.lift_snd]
      rw [← Category.assoc i, hz, Category.id_comp]
  have hf₀ : sq.lift ≫ P.p₀ = 𝟙 Y := by
    have e := congrArg (· ≫ prod.fst) sq.fac_right
    simpa only [Category.assoc, prod.lift_fst] using e
  have hf₁ : sq.lift ≫ P.p₁ = z ≫ u := by
    have e := congrArg (· ≫ prod.snd) sq.fac_right
    simpa only [Category.assoc, prod.lift_snd] using e
  have hp₀ : GlobularSet.LiftsBoundaries (underlyingMap P.p₀.hom) := by
    intro k
    exact (hasLiftingProperty_I_iff k P.p₀.hom).1
      ((boundaryClass_rlp_iff hC q 0 P.p₀).1 P.lifts₀ k (Nat.zero_le k))
  have hp₁ : GlobularSet.LiftsBoundaries (underlyingMap P.p₁.hom) := by
    intro k
    exact (hasLiftingProperty_I_iff k P.p₁.hom).1
      ((boundaryClass_rlp_iff hC q 0 P.p₁).1 P.lifts₁ k (Nat.zero_le k))
  apply weakEquivalence_of_exactBoundaryTest hC
  apply GlobularSet.ExactBoundaryTest.of_retract_factor
    (underlyingMap i.hom) (underlyingMap z.hom) (underlyingMap u.hom)
    (congrArg (fun t : X ⟶ X => underlyingMap t.hom) hz) _ (Y.obj.joined_refl hC)
  have hv := GlobularSet.exactBoundaryTest_endpoint_section
    (underlyingMap P.p₀.hom) (underlyingMap P.p₁.hom) (underlyingMap sq.lift.hom)
    hp₀ hp₁
    (fun k x => congrFun (congrArg (fun t => (underlyingMap t.hom).app k) hf₀) x)
    (Y.obj.joined_refl hC)
  have e := congrArg (fun t : Y ⟶ Y => underlyingMap t.hom) hf₁
  change GlobularSet.ExactBoundaryTest (underlyingMap (sq.lift ≫ P.p₁).hom) at hv
  rw [e] at hv
  exact hv

end Grothendieck.GlobularTheory.Model

end OAI
