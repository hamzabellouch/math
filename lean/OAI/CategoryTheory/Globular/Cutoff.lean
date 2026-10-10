import OAI.CategoryTheory.Globular.Homotopy

namespace OAI

universe u v w

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularTheory.Model

theorem components_eq_iff {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (x y : X.underlying.Cell 0) :
    Quot.mk (X.underlying.Joined 0) x = Quot.mk (X.underlying.Joined 0) y ↔
      X.underlying.Joined 0 x y :=
  ⟨fun h => (X.joined_equivalence hC 0).eqvGen_iff.mp (Quot.eqvGen_exact h), Quot.sound⟩

theorem loops_joined_equivalence {C : GlobularTheory.{v}} (X : C.Model)
    (hC : C.IsCoherator) (x : X.underlying.Cell 0) (n : ℕ) :
    Equivalence (fun a b : X.Loops hC x n => X.underlying.Joined (n+1) a.1 b.1) :=
  ⟨fun a => X.joined_refl hC (n+1) a.1, fun h => X.joined_symm hC h,
    fun h k => X.joined_trans hC h k⟩

theorem weakEquivalence_of_exactBoundaryTest {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X Y : C.Model} (f : X ⟶ Y) (hf : GlobularSet.ExactBoundaryTest (underlyingMap f)) :
    WeakEquivalence hC f := by
  constructor
  · constructor
    · intro a b hab
      induction a using Quot.inductionOn with | h a =>
        induction b using Quot.inductionOn with | h b =>
          apply Quot.sound
          apply hf.reflects_joined (n := 0) trivial
          exact (Y.components_eq_iff hC _ _).mp hab
    · intro b
      induction b using Quot.inductionOn with | h b =>
        obtain ⟨a, _, ha⟩ := hf 0 PUnit.unit b rfl
        exact ⟨Quot.mk _ a, Quot.sound ha⟩
  · intro x n
    constructor
    · intro a b hab
      induction a using Quot.inductionOn with | h a =>
        induction b using Quot.inductionOn with | h b =>
          apply Quot.sound
          apply hf.reflects_joined
          · exact ⟨a.2.1.trans b.2.1.symm, a.2.2.trans b.2.2.symm⟩
          · exact (Y.loops_joined_equivalence hC _ n).eqvGen_iff.mp
              (Quot.eqvGen_exact hab)
    · intro b
      induction b using Quot.inductionOn with | h b =>
        let c := X.baseCell hC x n
        let bd : X.underlying.Boundary (n+1) :=
          ⟨(c, c), by cases n <;> simp [GlobularSet.Parallel]⟩
        have hb : Y.underlying.boundary (n+1) b.1 =
            (underlyingMap f).boundaryMap (n+1) bd := by
          apply Subtype.ext
          exact Prod.ext (b.2.1.trans (map_baseCell f hC x n).symm)
            (b.2.2.trans (map_baseCell f hC x n).symm)
        obtain ⟨a, ha, hab⟩ := hf (n+1) bd b.1 hb
        have ha' := congrArg Subtype.val ha
        let a' : X.Loops hC x n :=
          ⟨a, congrArg Prod.fst ha', congrArg Prod.snd ha'⟩
        exact ⟨Quot.mk _ a', Quot.sound hab⟩

end GlobularTheory.Model

namespace GlobularSet

def cutoffCell (X : GlobularSet.{u}) (q n : ℕ) : Type u :=
  if n ≤ q then X.Cell n else X.Boundary (q+1)

def cutoffFace (X : GlobularSet.{u}) (q n : ℕ) (side : Bool) :
    X.cutoffCell q (n+1) → X.cutoffCell q n := by
  by_cases h : n+1 ≤ q
  · have hn : n ≤ q := Nat.le_trans (Nat.le_succ n) h
    simpa only [cutoffCell, ite_eq_left h, ite_eq_left hn] using
      (if side then X.target n else X.source n)
  · by_cases hn : n = q
    · subst n
      simpa only [cutoffCell, ite_eq_right h, ite_eq_left (Nat.le_refl q)] using
        (fun b : X.Boundary (q+1) => if side then b.1.2 else b.1.1)
    · have hnq : ¬ n ≤ q := by omega
      simpa only [cutoffCell, ite_eq_right h, ite_eq_right hnq] using
        (_root_.id : X.Boundary (q+1) → X.Boundary (q+1))

theorem cutoffCell_low (X : GlobularSet.{u}) {q n : ℕ} (h : n ≤ q) :
    X.cutoffCell q n = X.Cell n := ite_eq_left h

theorem cutoffCell_high (X : GlobularSet.{u}) {q n : ℕ} (h : ¬ n ≤ q) :
    X.cutoffCell q n = X.Boundary (q+1) := ite_eq_right h

theorem cutoffFace_low (X : GlobularSet.{u}) {q n : ℕ} (h : n+1 ≤ q) (side) :
    HEq (X.cutoffFace q n side) (if side then X.target n else X.source n) := by
  simp only [cutoffFace, dite_eq_left h]
  exact cast_heq _ _

theorem cutoffFace_seam (X : GlobularSet.{u}) (q : ℕ) (side) :
    HEq (X.cutoffFace q q side)
      (fun b : X.Boundary (q+1) => if side then b.1.2 else b.1.1) := by
  simp only [cutoffFace, dite_eq_right (Nat.not_succ_le_self q)]
  exact cast_heq _ _

private theorem comp_eq_of_heq {A B C A' B' C' : Type u}
    (ha : A = A') (hb : B = B') (hc : C = C')
    {s t : A → B} {s' t' : A' → B'} {l : B → C} {l' : B' → C'}
    (hs : HEq s s') (ht : HEq t t') (hl : HEq l l')
    (w : ∀ x, l' (s' x) = l' (t' x)) : ∀ x, l (s x) = l (t x) := by
  cases ha; cases hb; cases hc
  cases eq_of_heq hs; cases eq_of_heq ht; cases eq_of_heq hl
  exact w

def cutoff (X : GlobularSet.{u}) (q : ℕ) : GlobularSet.{u} where
  Cell := X.cutoffCell q
  source n := X.cutoffFace q n false
  target n := X.cutoffFace q n true
  source_source n x := by
    by_cases h : n+1+1 ≤ q
    · have h₁ : n+1 ≤ q := by omega
      have h₀ : n ≤ q := by omega
      exact comp_eq_of_heq (X.cutoffCell_low h) (X.cutoffCell_low h₁)
        (X.cutoffCell_low h₀) (X.cutoffFace_low h false) (X.cutoffFace_low h true)
        (X.cutoffFace_low h₁ false) (X.source_source n) x
    · by_cases h₁ : n+1 = q
      · subst q
        exact comp_eq_of_heq (X.cutoffCell_high (Nat.not_succ_le_self (n+1)))
          (X.cutoffCell_low le_rfl) (X.cutoffCell_low (Nat.le_succ n))
          (X.cutoffFace_seam (n+1) false) (X.cutoffFace_seam (n+1) true)
          (X.cutoffFace_low le_rfl false) (fun x => x.2.1) x
      · by_cases h₀ : n = q
        · subst q
          simp [cutoffFace]
        · have h₁' : ¬ n+1 ≤ q := by omega
          simp [cutoffFace, h, h₁, h₀, h₁']
  target_source n x := by
    by_cases h : n+1+1 ≤ q
    · have h₁ : n+1 ≤ q := by omega
      have h₀ : n ≤ q := by omega
      exact comp_eq_of_heq (X.cutoffCell_low h) (X.cutoffCell_low h₁)
        (X.cutoffCell_low h₀) (X.cutoffFace_low h false) (X.cutoffFace_low h true)
        (X.cutoffFace_low h₁ true) (X.target_source n) x
    · by_cases h₁ : n+1 = q
      · subst q
        exact comp_eq_of_heq (X.cutoffCell_high (Nat.not_succ_le_self (n+1)))
          (X.cutoffCell_low le_rfl) (X.cutoffCell_low (Nat.le_succ n))
          (X.cutoffFace_seam (n+1) false) (X.cutoffFace_seam (n+1) true)
          (X.cutoffFace_low le_rfl true) (fun x => x.2.2) x
      · by_cases h₀ : n = q
        · subst q
          simp [cutoffFace]
        · have h₁' : ¬ n+1 ≤ q := by omega
          simp [cutoffFace, h, h₁, h₀, h₁']

end GlobularSet

namespace GlobularTheory.Model

@[simp]
theorem underlyingMap_id {C : GlobularTheory.{v}} (X : C.Model) :
    underlyingMap (𝟙 X) = GlobularSet.Hom.id X.underlying := rfl

@[simp]
theorem underlyingMap_comp {C : GlobularTheory.{v}} {X Y Z : C.Model}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    underlyingMap (f ≫ g) = (underlyingMap f).comp (underlyingMap g) := rfl

theorem BoundaryAttachment.hasLiftingProperty {C : GlobularTheory.{v}}
    {X Y P Q : C.Model} {i : X ⟶ Y} (A : BoundaryAttachment i) (p : P ⟶ Q)
    (hp : GlobularSet.LiftsBoundaries (underlyingMap p)) : HasLiftingProperty i p := by
  classical
  constructor
  intro f g sq
  have liftcell : ∀ k, ∃ z : P.underlying.Cell (A.dimension k),
      P.underlying.boundary _ z = (underlyingMap f).boundaryMap _ (A.boundary k) ∧
      (underlyingMap p).app _ z = (underlyingMap g).app _ (A.cell k) := by
    intro k
    apply hp
    rw [← (underlyingMap g).boundary_app, A.cell_boundary]
    have eq := congrArg (fun e => (underlyingMap e).boundaryMap _ (A.boundary k)) sq.w
    simpa only [underlyingMap_comp, GlobularSet.Hom.boundaryMap_comp] using eq.symm
  choose z hz hzp using liftcell
  obtain ⟨l, hl, huniq⟩ := A.universal P f z hz
  have hcomp : l ≫ p = g := by
    obtain ⟨_, _, unique⟩ := A.universal Q (i ≫ g)
      (fun k => (underlyingMap g).app _ (A.cell k))
      (fun k => by rw [← (underlyingMap g).boundary_app, A.cell_boundary,
        underlyingMap_comp, GlobularSet.Hom.boundaryMap_comp])
    apply (unique (l ≫ p) ?_).trans (unique g ?_).symm
    · constructor
      · rw [← Category.assoc, hl.1, sq.w]
      · intro k
        change (underlyingMap p).app _ ((underlyingMap l).app _ (A.cell k)) = _
        rw [hl.2, hzp]
    · exact ⟨rfl, fun _ => rfl⟩
  exact CommSq.HasLift.mk' ⟨l, hl.1, hcomp⟩

theorem section_of_isCellular {C : GlobularTheory.{v}} {X P : C.Model}
    (hX : X.IsCellular) (p : P ⟶ X)
    (hp : GlobularSet.LiftsBoundaries (underlyingMap p)) : ∃ s : X ⟶ P, s ≫ p = 𝟙 X := by
  obtain ⟨A⟩ := hX
  let := A.linearOrder
  let := A.orderBot
  let := A.succOrder
  let := A.wellFoundedLT
  have : A.chain.F.IsWellOrderContinuous := A.chain.isWellOrderContinuous
  have : HasLiftingProperty (A.chain.incl.app ⊥) p :=
    HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
      (hc := A.chain.isColimit)
      (fun j hj => (A.attachment j hj).hasLiftingProperty p hp)
  let f : A.chain.F.obj ⊥ ⟶ P := A.chain.isoBot.hom ≫ A.isInitial.to P
  have sq : CommSq f (A.chain.incl.app ⊥) p (𝟙 X) := by
    constructor
    dsimp [f]
    rw [Category.comp_id, Category.assoc]
    have eq : A.isInitial.to P ≫ p = A.start := A.isInitial.hom_ext _ _
    rw [eq]
    exact (congrArg (A.chain.isoBot.hom ≫ ·) A.chain.fac.symm).trans
      (by simp only [Iso.hom_inv_id_assoc])
  exact ⟨sq.lift, sq.fac_right⟩


noncomputable def unitMap (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    disk C (n+1) ⟶ disk C n :=
  show (disk C (n+1)).presheaf ⟶ (disk C n).presheaf from
    yoneda.map (show (⟨Shape.globe (n+1)⟩ : C.Obj) ⟶ ⟨Shape.globe n⟩ from C.unit hC n)

@[simp]
theorem J_comp_unitMap (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    J C n ≫ unitMap C hC n = 𝟙 (disk C n) := by
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  intro f
  change C.Hom S.unop.shape (Shape.globe n) at f
  change C.comp (C.comp f (C.base (Shape.source n))) (C.unit hC n) = f
  rw [C.assoc, C.unit_source, C.comp_id]

theorem elementary_pushout_retraction {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X Y : C.Model} (n : ℕ) (a : disk C n ⟶ X) (i : X ⟶ Y)
    (b : disk C (n+1) ⟶ Y) (sq : IsPushout a (J C n) i b) :
    ∃ r : Y ⟶ X, i ≫ r = 𝟙 X := by
  have w : a ≫ 𝟙 X = J C n ≫ (unitMap C hC n ≫ a) := by
    rw [← Category.assoc, J_comp_unitMap, Category.id_comp, Category.comp_id]
  exact ⟨sq.desc (𝟙 X) (unitMap C hC n ≫ a) w, sq.inl_desc _ _ w⟩

theorem weakEquivalence_of_partialPath_data {C : GlobularTheory.{v}}
    (hC : C.IsCoherator) {X Y : C.Model} (hX : X.IsCellular)
    (n : ℕ) (a : disk C n ⟶ X) (i : X ⟶ Y) (b : disk C (n+1) ⟶ Y)
    (sq : IsPushout a (J C n) i b)
    (PX PY : C.Model) (pX₀ pX₁ : PX ⟶ X) (pY₀ pY₁ : PY ⟶ Y)
    (Pi : PX ⟶ PY) (nat₀ : Pi ≫ pY₀ = pX₀ ≫ i) (nat₁ : Pi ≫ pY₁ = pX₁ ≫ i)
    (hpX₀ : GlobularSet.LiftsBoundaries (underlyingMap pX₀))
    (hpX₁ : GlobularSet.LiftsBoundaries (underlyingMap pX₁))
    (hpY₀ : GlobularSet.LiftsBoundaries (underlyingMap pY₀))
    (hpY₁ : GlobularSet.LiftsBoundaries (underlyingMap pY₁))
    (joint : ∀ (t : disk C n ⟶ PY) (u₀ u₁ : disk C (n+1) ⟶ Y),
      t ≫ pY₀ = J C n ≫ u₀ → t ≫ pY₁ = J C n ≫ u₁ →
      ∃ l : disk C (n+1) ⟶ PY,
        J C n ≫ l = t ∧ l ≫ pY₀ = u₀ ∧ l ≫ pY₁ = u₁) :
    WeakEquivalence hC i := by
  obtain ⟨r, hr⟩ := elementary_pushout_retraction hC n a i b sq
  obtain ⟨h, hh⟩ := section_of_isCellular hX pX₀ hpX₀
  let u : X ⟶ X := h ≫ pX₁
  let ru : Y ⟶ X := r ≫ u
  have diu : i ≫ ru = u := by simp only [ru, ← Category.assoc, hr, Category.id_comp]
  have w₀ : (a ≫ h ≫ Pi) ≫ pY₀ = J C n ≫ b := by
    simp only [Category.assoc, nat₀]
    rw [← Category.assoc h, hh, Category.id_comp, ← sq.w]
  have w₁ : (a ≫ h ≫ Pi) ≫ pY₁ = J C n ≫ (b ≫ ru ≫ i) := by
    simp only [Category.assoc, nat₁]
    rw [← Category.assoc h]
    change a ≫ (u ≫ i) = _
    rw [← diu]
    simp only [← Category.assoc]
    rw [sq.w]
  obtain ⟨l, hl, hl₀, hl₁⟩ := joint (a ≫ h ≫ Pi) b (b ≫ ru ≫ i) w₀ w₁
  let f : Y ⟶ PY := sq.desc (h ≫ Pi) l hl.symm
  have hf₀ : f ≫ pY₀ = 𝟙 Y := by
    apply sq.hom_ext
    · dsimp [f]
      rw [← Category.assoc, sq.inl_desc, Category.assoc, nat₀,
        ← Category.assoc, hh, Category.id_comp, Category.comp_id]
    · dsimp [f]
      rw [← Category.assoc, sq.inr_desc, hl₀, Category.comp_id]
  have hf₁ : f ≫ pY₁ = ru ≫ i := by
    apply sq.hom_ext
    · dsimp [f]
      rw [← Category.assoc, sq.inl_desc, Category.assoc, nat₁]
      rw [← Category.assoc i, diu]
      rfl
    · dsimp [f]
      rw [← Category.assoc, sq.inr_desc, hl₁]
  apply weakEquivalence_of_exactBoundaryTest hC
  apply GlobularSet.ExactBoundaryTest.of_mutual_composites (underlyingMap i) (underlyingMap ru)
  · have test := GlobularSet.exactBoundaryTest_endpoint_section
      (underlyingMap pX₀) (underlyingMap pX₁) (underlyingMap h) hpX₀ hpX₁
      (fun k x => congrFun (congrArg (fun e => (underlyingMap e).app k) hh) x)
      (X.joined_refl hC)
    rw [← underlyingMap_comp, diu]
    exact test
  · have test := GlobularSet.exactBoundaryTest_endpoint_section
      (underlyingMap pY₀) (underlyingMap pY₁) (underlyingMap f) hpY₀ hpY₁
      (fun k x => congrFun (congrArg (fun e => (underlyingMap e).app k) hf₀) x)
      (Y.joined_refl hC)
    rw [← underlyingMap_comp]
    rw [← underlyingMap_comp, hf₁] at test
    exact test

end GlobularTheory.Model

namespace GlobularSet

def faceMap (X : GlobularSet.{u}) {m n : ℕ} (h : m < n) (side : Bool) :
    X.Cell n → X.Cell m :=
  Nat.leRecOn (C := fun k => X.Cell k → X.Cell m) h
    (fun {k} f x => f (X.source k x)) (if side then X.target m else X.source m)

@[simp]
theorem faceMap_succ (X : GlobularSet.{u}) (m : ℕ) (side : Bool) :
    X.faceMap (Nat.lt_succ_self m) side = (if side then X.target m else X.source m) :=
  Nat.leRecOn_self _

theorem faceMap_source (X : GlobularSet.{u}) {m n : ℕ} (h : m < n) (side : Bool)
    (x : X.Cell (n+1)) :
    X.faceMap (Nat.lt_succ_of_lt h) side x = X.faceMap h side (X.source n x) := by
  unfold faceMap
  rw [Nat.leRecOn_succ h]

theorem faceMap_target (X : GlobularSet.{u}) {m n : ℕ} (h : m < n) (side : Bool)
    (x : X.Cell (n+1)) :
    X.faceMap h side (X.source n x) = X.faceMap h side (X.target n x) := by
  induction n, h using Nat.le_induction with
  | base =>
    simp only [faceMap_succ]
    cases side
    · exact X.source_source m x
    · exact X.target_source m x
  | succ n h _ =>
    rw [faceMap_source X h, faceMap_source X h, X.source_source]

theorem faceMap_comp (X : GlobularSet.{u}) {m n k : ℕ}
    (h : m < n) (h' : n < k) (side side' : Bool) (x : X.Cell k) :
    X.faceMap (h.trans h') side x =
      X.faceMap h side (X.faceMap h' side' x) := by
  induction k, h' using Nat.le_induction with
  | base =>
    rw [faceMap_source X h, faceMap_succ]
    cases side'
    · rfl
    · exact X.faceMap_target h side x
  | succ k h' ih =>
    rw [faceMap_source X (h.trans h'), faceMap_source X h']
    exact ih (X.source k x)

def evalFace (X : GlobularSet.{u}) {m n : ℕ} : Globe.Face m n → (X.Cell n → X.Cell m)
  | .id _ => _root_.id
  | .face h side => X.faceMap h side

theorem evalFace_comp (X : GlobularSet.{u}) {m n k : ℕ} (f : Globe.Face m n)
    (g : Globe.Face n k) (x : X.Cell k) :
    X.evalFace (f.comp g) x = X.evalFace f (X.evalFace g x) := by
  cases f with
  | id => rfl
  | face h side =>
    cases g with
    | id => rfl
    | face h' side' => exact X.faceMap_comp h h' side side' x

def presheaf (X : GlobularSet.{u}) : GlobularPresheaf.{u} where
  obj n := X.Cell n.unop.dim
  map f := TypeCat.ofHom (X.evalFace f.unop)
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact X.evalFace_comp g.unop f.unop x

end GlobularSet

end Grothendieck

end OAI
