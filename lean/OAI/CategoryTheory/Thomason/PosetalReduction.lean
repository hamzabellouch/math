import Mathlib
import OAI.CategoryTheory.Thomason.PosetalColimits

namespace OAI

/-! Posetal Reduction. -/

noncomputable section
universe u v w z
open CategoryTheory Limits
local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace Thomason.GeometricRecognition.PosetAttachment
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
variable (A : Set P) (f : A →o Q)

inductive Obj (A : Set P) (f : A →o Q)
  | inl (x : Q) : Obj A f
  | inr (b : {b : P // b ∉ A}) : Obj A f

@[reducible] def Rel : Obj A f → Obj A f → Prop
  | .inl x, .inl y => x ≤ y
  | .inl x, .inr b => ∃ a : A, a.val ≤ b.val ∧ x ≤ f a
  | .inr _, .inl _ => False
  | .inr b, .inr c => b.val ≤ c.val

instance partialOrder : PartialOrder (Obj A f) where
  le := Rel A f
  le_refl x := by cases x <;> exact le_rfl
  le_trans x y z hxy hyz := by
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        cases z with
        | inl z => exact le_trans hxy hyz
        | inr z => obtain ⟨a,ha,hy⟩ := hyz; exact ⟨a,ha,hxy.trans hy⟩
      | inr y =>
        cases z with
        | inl z => exact hyz.elim
        | inr z => obtain ⟨a,ha,hx⟩ := hxy; exact ⟨a,ha.trans hyz,hx⟩
    | inr x =>
      cases y with
      | inl y => exact hxy.elim
      | inr y =>
        cases z with
        | inl z => exact hyz.elim
        | inr z => exact le_trans hxy hyz
  le_antisymm x y hxy hyx := by
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Obj.inl (le_antisymm hxy hyx)
      | inr y => exact hyx.elim
    | inr x =>
      cases y with
      | inl y => exact hxy.elim
      | inr y => exact congrArg Obj.inr (Subtype.ext (le_antisymm hxy hyx))

def left : Q →o Obj A f where
  toFun := Obj.inl
  monotone' := fun _ _ h => h

def right (hA : IsLowerSet A) : P →o Obj A f where
  toFun b := if h : b ∈ A then Obj.inl (f ⟨b,h⟩) else Obj.inr ⟨b,h⟩
  monotone' := by
    intro b c hbc
    by_cases hb : b ∈ A <;> by_cases hc : c ∈ A
    · simp only [dite_eq_left hb,dite_eq_left hc]
      exact f.monotone (show (⟨b,hb⟩ : A) ≤ ⟨c,hc⟩ from hbc)
    · simp only [dite_eq_left hb,dite_eq_right hc]
      exact ⟨⟨b,hb⟩,hbc,le_rfl⟩
    · exact (hb (hA hbc hc)).elim
    · simp only [dite_eq_right hb,dite_eq_right hc]
      exact hbc

variable (r : {b : P // ∃ a ∈ A, a ≤ b} →o A)
variable (hadj : ∀ (a : A) (b : {b : P // ∃ a ∈ A, a ≤ b}),
  a.val ≤ b.val ↔ a ≤ r b)
variable {T : Type v} [Category T] (L : Q ⥤ T) (R : P ⥤ T)
variable (h : f.toFunctor ⋙ L = (OrderEmbedding.subtype A).toOrderHom.toFunctor ⋙ R)

include h in
theorem agree (a : A) : L.obj (f a) = R.obj a.val := CategoryTheory.Functor.congr_obj h a

lemma agree_natural {a b : A} (hab : a ≤ b) :
    L.map (homOfLE (f.monotone hab)) ≫ eqToHom (agree A f L R h b) =
      eqToHom (agree A f L R h a) ≫ R.map (homOfLE hab) := by
  have hh := (eqToHom h).naturality (homOfLE hab)
  simp only [eqToHom_app,CategoryTheory.Functor.comp_map] at hh
  convert hh using 1 <;> congr 2

@[reducible] def obj : Obj A f → T
  | .inl x => L.obj x
  | .inr b => R.obj b.val

def bridge (x : Q) (b : {b : P // b ∉ A})
    (hx : ∃ a : A, a.val ≤ b.val ∧ x ≤ f a) : L.obj x ⟶ R.obj b.val := by
  let z : {b : P // ∃ a ∈ A, a ≤ b} := ⟨b.val,by
    obtain ⟨a,ha,_⟩ := hx
    exact ⟨a.val,a.property,ha⟩⟩
  have hxr : x ≤ f (r z) := by
    obtain ⟨a,ha,hx⟩ := hx
    exact hx.trans (f.monotone ((hadj a z).mp ha))
  exact L.map (homOfLE hxr) ≫ eqToHom (agree A f L R h (r z)) ≫
    R.map (homOfLE ((hadj (r z) z).mpr le_rfl))

lemma bridge_eq (x : Q) (b : {b : P // b ∉ A})
    (hx : ∃ a : A, a.val ≤ b.val ∧ x ≤ f a)
    (a : A) (ha : a.val ≤ b.val) (hxa : x ≤ f a) :
    bridge A f r hadj L R h x b hx =
      L.map (homOfLE hxa) ≫ eqToHom (agree A f L R h a) ≫ R.map (homOfLE ha) := by
  dsimp only [bridge]
  let z : {b : P // ∃ a ∈ A, a ≤ b} := ⟨b.val,⟨a.val,a.property,ha⟩⟩
  have har : a ≤ r z := (hadj a z).mp ha
  have hrb : (r z).val ≤ b.val := (hadj (r z) z).mpr le_rfl
  change L.map (homOfLE (hxa.trans (f.monotone har))) ≫
    eqToHom (agree A f L R h (r z)) ≫ R.map (homOfLE hrb) = _
  rw [show homOfLE (hxa.trans (f.monotone har)) =
    homOfLE hxa ≫ homOfLE (f.monotone har) from rfl, L.map_comp]
  rw [Category.assoc, ← Category.assoc (L.map (homOfLE (f.monotone har))),
    agree_natural A f L R h har, Category.assoc, ← R.map_comp]
  rfl

def arrow : {x y : Obj A f} → (x ≤ y) → (obj A f L R x ⟶ obj A f L R y)
  | .inl _, .inl _, hxy => L.map (homOfLE hxy)
  | .inl x, .inr y, hxy => bridge A f r hadj L R h x y hxy
  | .inr _, .inl _, hxy => hxy.elim
  | .inr _, .inr _, hxy => R.map (homOfLE hxy)

lemma arrow_trans {x y z : Obj A f} (hxy : x ≤ y) (hyz : y ≤ z) :
    arrow A f r hadj L R h (hxy.trans hyz) =
      arrow A f r hadj L R h hxy ≫ arrow A f r hadj L R h hyz := by
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases z with
      | inl z => exact L.map_comp _ _
      | inr z =>
        change x ≤ y at hxy
        obtain ⟨a,ha,hy⟩ := hyz
        dsimp only [arrow]
        rw [bridge_eq A f r hadj L R h x z _ a ha (hxy.trans hy),
          bridge_eq A f r hadj L R h y z _ a ha hy]
        rw [show homOfLE (hxy.trans hy) = homOfLE hxy ≫ homOfLE hy from rfl,
          L.map_comp, Category.assoc]
    | inr y =>
      cases z with
      | inl z => exact hyz.elim
      | inr z =>
        obtain ⟨a,ha,hx⟩ := hxy
        dsimp only [arrow]
        rw [bridge_eq A f r hadj L R h x z _ a (ha.trans hyz) hx,
          bridge_eq A f r hadj L R h x y _ a ha hx]
        rw [show homOfLE (ha.trans hyz) = homOfLE ha ≫ homOfLE hyz from rfl,
          R.map_comp, Category.assoc, Category.assoc]
  | inr x =>
    cases y with
    | inl y => exact hxy.elim
    | inr y =>
      cases z with
      | inl z => exact hyz.elim
      | inr z => exact R.map_comp _ _

def desc : Obj A f ⥤ T where
  obj := obj A f L R
  map g := arrow A f r hadj L R h (leOfHom g)
  map_id x := by cases x <;> dsimp only [arrow] <;> simp [obj]
  map_comp g k := arrow_trans A f r hadj L R h (leOfHom g) (leOfHom k)

lemma left_desc : (left A f).toFunctor ⋙ desc A f r hadj L R h = L := by
  apply CategoryTheory.Functor.hext (fun _ => rfl)
  intro x y g
  rfl

lemma right_obj_desc (hA : IsLowerSet A) (b : P) :
    (desc A f r hadj L R h).obj (right A f hA b) = R.obj b := by
  change obj A f L R (if hb : b ∈ A then Obj.inl (f ⟨b,hb⟩) else Obj.inr ⟨b,hb⟩) = R.obj b
  split
  · exact agree A f L R h _
  · rfl

lemma right_mem (hA : IsLowerSet A) (b : P) (hb : b ∈ A) :
    right A f hA b = Obj.inl (f ⟨b,hb⟩) := dite_eq_left hb

lemma right_not_mem (hA : IsLowerSet A) (b : P) (hb : b ∉ A) :
    right A f hA b = Obj.inr ⟨b,hb⟩ := dite_eq_right hb

lemma arrow_heq {x y x' y' : Obj A f} (p : x ≤ y) (p' : x' ≤ y')
    (hx : x = x') (hy : y = y') :
    HEq (arrow A f r hadj L R h p) (arrow A f r hadj L R h p') := by
  subst x'; subst y'; rfl

lemma right_desc (hA : IsLowerSet A) :
    (right A f hA).toFunctor ⋙ desc A f r hadj L R h = R := by
  apply CategoryTheory.Functor.hext (right_obj_desc A f r hadj L R h hA)
  intro b c g
  have hbc : b ≤ c := leOfHom g
  have hg : g = homOfLE hbc := Subsingleton.elim _ _
  subst g
  change HEq (arrow A f r hadj L R h ((right A f hA).monotone hbc))
    (R.map (homOfLE hbc))
  by_cases hb : b ∈ A <;> by_cases hc : c ∈ A
  · let p : (Obj.inl (f ⟨b,hb⟩) : Obj A f) ≤ Obj.inl (f ⟨c,hc⟩) :=
      f.monotone (show (⟨b,hb⟩ : A) ≤ ⟨c,hc⟩ from hbc)
    apply (arrow_heq A f r hadj L R h _ p
      (right_mem A f hA b hb) (right_mem A f hA c hc)).trans
    exact CategoryTheory.Functor.hcongr_hom h
      (homOfLE (show (⟨b,hb⟩ : A) ≤ ⟨c,hc⟩ from hbc))
  · let p : (Obj.inl (f ⟨b,hb⟩) : Obj A f) ≤ Obj.inr ⟨c,hc⟩ :=
      ⟨⟨b,hb⟩,hbc,le_rfl⟩
    apply (arrow_heq A f r hadj L R h _ p
      (right_mem A f hA b hb) (right_not_mem A f hA c hc)).trans
    change HEq (bridge A f r hadj L R h (f ⟨b,hb⟩) ⟨c,hc⟩ p) _
    rw [bridge_eq A f r hadj L R h (f ⟨b,hb⟩) ⟨c,hc⟩ _ ⟨b,hb⟩ hbc le_rfl]
    simp
  · exact (hb (hA hbc hc)).elim
  · let p : (Obj.inr ⟨b,hb⟩ : Obj A f) ≤ Obj.inr ⟨c,hc⟩ := hbc
    exact arrow_heq A f r hadj L R h _ p
      (right_not_mem A f hA b hb) (right_not_mem A f hA c hc)

lemma square (hA : IsLowerSet A) : f.toFunctor ⋙ (left A f).toFunctor =
    (OrderEmbedding.subtype A).toOrderHom.toFunctor ⋙ (right A f hA).toFunctor := by
  refine CategoryTheory.Functor.ext (fun a => (right_mem A f hA a.val a.property).symm) ?_
  intro a b g
  exact Subsingleton.elim _ _

lemma joint_ext (hA : IsLowerSet A) {F G : Obj A f ⥤ T}
    (hl : (left A f).toFunctor ⋙ F = (left A f).toFunctor ⋙ G)
    (hr : (right A f hA).toFunctor ⋙ F = (right A f hA).toFunctor ⋙ G) : F = G := by
  have ho (x : Obj A f) : F.obj x = G.obj x := by
    cases x with
    | inl x => exact CategoryTheory.Functor.congr_obj hl x
    | inr b =>
      have hh := CategoryTheory.Functor.congr_obj hr b.val
      change F.obj (right A f hA b.val) = G.obj (right A f hA b.val) at hh
      simpa only [right_not_mem A f hA b.val b.property] using hh
  apply CategoryTheory.Functor.hext ho
  intro x y g
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have hg : g = (left A f).toFunctor.map (homOfLE (show x ≤ y from leOfHom g)) :=
        Subsingleton.elim _ _
      rw [hg]
      exact CategoryTheory.Functor.hcongr_hom hl _
    | inr b =>
      obtain ⟨a,ha,hxa⟩ := leOfHom g
      let k : (Obj.inl x : Obj A f) ⟶ Obj.inl (f a) := homOfLE hxa
      let t : (Obj.inl (f a) : Obj A f) ⟶ Obj.inr b :=
        eqToHom (right_mem A f hA a.val a.property).symm ≫
          (right A f hA).toFunctor.map (homOfLE ha) ≫
          eqToHom (right_not_mem A f hA b.val b.property)
      have hg : g = k ≫ t := Subsingleton.elim _ _
      rw [hg]
      apply CategoryTheory.Functor.map_comp_heq (ho _) (ho _) (ho _)
      · exact CategoryTheory.Functor.hcongr_hom hl (homOfLE hxa)
      · dsimp only [t]
        simp only [CategoryTheory.Functor.map_comp,eqToHom_map,
          eqToHom_comp_heq_iff,heq_eqToHom_comp_iff,
          comp_eqToHom_heq_iff,heq_comp_eqToHom_iff]
        exact CategoryTheory.Functor.hcongr_hom hr (homOfLE ha)
  | inr b =>
    cases y with
    | inl y => exact (leOfHom g).elim
    | inr c =>
      have hbc : b.val ≤ c.val := leOfHom g
      let t : (Obj.inr b : Obj A f) ⟶ Obj.inr c :=
        eqToHom (right_not_mem A f hA b.val b.property).symm ≫
          (right A f hA).toFunctor.map (homOfLE hbc) ≫
          eqToHom (right_not_mem A f hA c.val c.property)
      have hg : g = t := Subsingleton.elim _ _
      rw [hg]
      dsimp only [t]
      simp only [CategoryTheory.Functor.map_comp,eqToHom_map,
        eqToHom_comp_heq_iff,heq_eqToHom_comp_iff,
        comp_eqToHom_heq_iff,heq_comp_eqToHom_iff]
      exact CategoryTheory.Functor.hcongr_hom hr (homOfLE hbc)

include r hadj in

theorem isPushout (hA : IsLowerSet A) :
    IsPushout f.toFunctor.toCatHom
      (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom
      (left A f).toFunctor.toCatHom (right A f hA).toFunctor.toCatHom := by
  have hs : f.toFunctor.toCatHom ≫ (left A f).toFunctor.toCatHom =
      (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom ≫
        (right A f hA).toFunctor.toCatHom := Cat.Hom.ext (square A f hA)
  apply IsPushout.of_isColimit (c := PushoutCocone.mk
    (left A f).toFunctor.toCatHom (right A f hA).toFunctor.toCatHom hs)
  refine PushoutCocone.IsColimit.mk hs
    (fun s => (desc A f r hadj s.inl.toFunctor s.inr.toFunctor
      (congrArg Cat.Hom.toFunctor s.condition)).toCatHom) ?_ ?_ ?_
  · intro s
    exact Cat.Hom.ext (left_desc A f r hadj s.inl.toFunctor s.inr.toFunctor _)
  · intro s
    exact Cat.Hom.ext (right_desc A f r hadj s.inl.toFunctor s.inr.toFunctor _ hA)
  · intro s m hl hr
    apply Cat.Hom.ext
    apply joint_ext A f hA
    · exact (congrArg Cat.Hom.toFunctor hl).trans (left_desc A f r hadj
        s.inl.toFunctor s.inr.toFunctor _).symm
    · exact (congrArg Cat.Hom.toFunctor hr).trans (right_desc A f r hadj
        s.inl.toFunctor s.inr.toFunctor _ hA).symm
end Thomason.GeometricRecognition.PosetAttachment

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder Opposite

namespace Thomason.GeometricRecognition.Posetal
open OmegaCategory AttachmentComparison HornAttachments SubdividedUnit

lemma pushout_posetal {P : Type u} [PartialOrder P] (A : Set P) (hA : IsLowerSet A)
    (r : upward A →o A) (hadj : ∀ (a : A) (b : upward A), a.val ≤ b.val ↔ a ≤ r b)
    {X Y : Cat.{u,u}} (a : Cat.of A ⟶ X) (j : X ⟶ Y) (v : Cat.of P ⟶ Y)
    (sc : IsPushout a (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom j v)
    (hX : IsPosetal X) : IsPosetal Y := by
  obtain ⟨Q,⟨e⟩⟩ := hX
  let f : A →o Q := {
    toFun := fun x : A => (a ≫ e.hom).toFunctor.obj x
    monotone' := fun x y h => @leOfHom Q inferInstance _ _
      ((a ≫ e.hom).toFunctor.map (@homOfLE A inferInstance x y h)) }
  have hf : a ≫ e.hom = f.toFunctor.toCatHom := by
    apply Cat.Hom.ext
    exact CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)
  have sq : IsPushout f.toFunctor.toCatHom
      (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom (e.inv ≫ j) v := by
    apply sc.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · simpa only [Iso.refl_hom,Category.id_comp] using hf
    · simp
    · simp
    · simp
  let ht := PosetAttachment.isPushout A f r hadj hA
  exact ⟨PartOrd.of (PosetAttachment.Obj A f),
    ⟨sq.isColimit.coconePointUniqueUpToIso ht.isColimit⟩⟩

abbrev CC : SSet.{u} ⥤ Cat.{u,u} := C ⋙ oneSkeletonCatFunctor

lemma initial_posetal {X : SSet.{u}} (hX : IsInitial X) : IsPosetal (CC.obj X) := by
  let P := ULift.{u} Empty
  let : PartialOrder P := inferInstance
  have hP : IsInitial (nerve P) := SSet.isInitialOfNotNonempty (by
    rintro ⟨s⟩
    exact (s.obj 0).down.elim)
  exact ⟨PartOrd.of P, ⟨CC.mapIso (hX.uniqueUpToIso hP) ≪≫
    (OneCat.categorificationCatIso (Cat.of P)).symm⟩⟩

lemma boundary_posetal_successor (I : Type u) (d : ℕ) {X Y : SSet.{u}}
    (a : (∐ fun _ : I => (∂Δ[d] : SSet)) ⟶ X) (j : X ⟶ Y)
    (v : (∐ fun _ : I => Δ[d]) ⟶ Y)
    (sc : IsPushout a (Limits.Sigma.map (fun _ : I => ∂Δ[d].ι)) j v)
    (hX : IsPosetal (CC.obj (D.obj X))) : IsPosetal (CC.obj (D.obj Y)) := by
  let A := PosetCoproduct.old I (BoundaryFlags d)
  let rA := PosetCoproduct.oldRetraction I (BoundaryFlags d)
    (flagRetraction (simplexFaces (SSet.boundary d)))
  have hA : IsLowerSet A := PosetCoproduct.old_lower I _ (oldSet_lower _)
  have hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ rA z :=
    PosetCoproduct.oldRetraction_adjunction I _ _ (flagRetraction_adjunction _)
  let a' := (boundaryCoprodIso I d).inv ≫ D.map a
  let v' := (simplexCoprodIso I d).inv ≫ D.map v
  let i : nerve A ⟶ nerve (PosetCoproduct.Piece I (Flags d)) :=
    nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor
  have sq : IsPushout a' i (D.map j) v' := by
    apply (sc.map D).of_iso (boundaryCoprodIso I d) (Iso.refl _)
      (simplexCoprodIso I d) (Iso.refl _)
    · simp [a']
    · exact boundaryCoprodIso_naturality I d
    · simp
    · simp [v']
  let eA : Cat.of A ≅ CC.obj (nerve A) := OneCat.categorificationCatIso (Cat.of A)
  let eP : Cat.of (PosetCoproduct.Piece I (Flags d)) ≅
      CC.obj (nerve (PosetCoproduct.Piece I (Flags d))) :=
    OneCat.categorificationCatIso (Cat.of (PosetCoproduct.Piece I (Flags d)))
  have sqC : IsPushout (eA.hom ≫ CC.map a')
      (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom
      (CC.map (D.map j)) (eP.hom ≫ CC.map v') := by
    apply (sq.map CC).of_iso eA.symm (Iso.refl _) eP.symm (Iso.refl _)
    · simp
    · have hn := OneCat.categorificationCatIso_natural
        ((OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom :
          Cat.of A ⟶ Cat.of (PosetCoproduct.Piece I (Flags d)))
      change _ ≫ eP.hom = eA.hom ≫ CC.map i at hn
      have hh := congrArg (fun f => eA.inv ≫ f ≫ eP.inv) hn
      simp only [Category.assoc,Iso.hom_inv_id,Iso.inv_hom_id_assoc,Category.comp_id] at hh
      exact hh.symm
    · simp
    · simp
  exact pushout_posetal A hA rA hadj _ _ _ sqC hX

lemma skeleton_posetal (K : SSet.{u}) (d : ℕ) :
    IsPosetal (CC.obj (D.obj ((SSet.relativeCellComplex K).F.obj d))) := by
  induction d with
  | zero =>
    apply initial_posetal
    apply IsInitial.isInitialObj
    have h₀ : IsInitial (⊥ : K.Subcomplex).toSSet :=
      SSet.isInitialOfNotNonempty (by rintro ⟨s⟩; exact s.property)
    exact h₀.ofIso (SSet.relativeCellComplex K).isoBot.symm
  | succ d ih =>
    exact boundary_posetal_successor
      (SSet.relativeCellComplexOfMono.Cell (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) d) d
      (SSet.relativeCellComplexOfMono.t _ d) (SSet.relativeCellComplexOfMono.r _ d)
      (SSet.relativeCellComplexOfMono.b _ d) (SSet.relativeCellComplexOfMono.isPushout _ d) ih

theorem categorification_sdTwice_posetal (K : SSet.{u}) : IsPosetal (CC.obj (D.obj K)) := by
  let c := SSet.relativeCellComplex K
  let F := c.F ⋙ D ⋙ C ⋙ N
  let : PreservesFilteredColimitsOfSize.{0,0} N :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits N
  have hc : IsColimit ((D ⋙ C ⋙ N).mapCocone { pt := K, ι := c.incl }) :=
    isColimitOfPreserves (D ⋙ C ⋙ N) c.isColimit
  have hstage (d : ℕ) := property_of_isPosetal (skeleton_posetal K d)
  let nerveIso (simplicialSet : SSet.{u}) :
      N.obj (C.obj simplicialSet) ≅ nerve (CC.obj simplicialSet) :=
    oneNerveIso (C.obj simplicialSet).property
  have ht : ∀ d, EdgeThin (F.obj d) := fun d =>
    edgeThin_of_mono (nerveIso (D.obj (c.F.obj d))).hom
      (nerve_edgeThin _ (hstage d))
  have ha : ∀ d, EdgeAntisym (F.obj d) := fun d =>
    edgeAntisym_of_mono (nerveIso (D.obj (c.F.obj d))).hom
      (nerve_edgeAntisym _ (hstage d))
  apply isPosetal_of_property
  apply property_of_nerve_edges
  · exact edgeThin_of_mono (nerveIso (D.obj K)).inv
      (edgeThin_colimit hc ht)
  · exact edgeAntisym_of_mono (nerveIso (D.obj K)).inv
      (edgeAntisym_colimit hc ha)
end Thomason.GeometricRecognition.Posetal

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.KanLocal
open LastVertexProof

def transpose {A B K : SSet.{u}} (f : A ⟶ (ihom B).obj K) : B ⟶ (ihom A).obj K :=
  curry ((β_ A B).hom ≫ uncurry f)

lemma transpose_transpose {A B K : SSet.{u}} (f : A ⟶ (ihom B).obj K) :
    transpose (transpose f) = f := by
  dsimp only [transpose]
  rw [uncurry_curry, ← Category.assoc]
  have h := SymmetricCategory.symmetry B A
  rw [h,Category.id_comp,curry_uncurry]

lemma transpose_homotopic {A B K : SSet.{u}} {f g : A ⟶ (ihom B).obj K}
    (H : Homotopic f g) : Homotopic (transpose f) (transpose g) :=
  homotopic_curry (homotopic_pre _ (homotopic_uncurry H))

lemma transpose_pre {A B C K : SSet.{u}} (f : A ⟶ (ihom B).obj K) (i : C ⟶ A) :
    transpose (i ≫ f) = transpose f ≫ (pre i).app K := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  simp only [transpose,uncurry_curry,uncurry_natural_left]
  rw [← Category.assoc,← BraidedCategory.braiding_naturality_left,Category.assoc]

lemma transpose_post {A B C K : SSet.{u}} (f : A ⟶ (ihom B).obj K) (i : C ⟶ B) :
    transpose (f ≫ (pre i).app K) = i ≫ transpose f := by
  have he := transpose_pre (transpose f) i
  have hh := congrArg (@transpose A C K) he
  simpa only [transpose_transpose] using hh.symm

lemma local_of_homotopy_classes {A B : SSet.{u}} (f : A ⟶ B)
    (hs : ∀ (K : SSet.{u}) [SSet.KanComplex K] (a : A ⟶ K),
      ∃ b : B ⟶ K, Homotopic (f ≫ b) a)
    (hi : ∀ (K : SSet.{u}) [SSet.KanComplex K] (a b : B ⟶ K),
      Homotopic (f ≫ a) (f ≫ b) → Homotopic a b) : Local f := by
  intro K hK
  let U := (ihom B).obj K
  let V := (ihom A).obj K
  let m : U ⟶ V := (pre f).app K
  obtain ⟨b,hb⟩ := hs ((ihom V).obj K) (transpose (𝟙 V))
  let g : V ⟶ U := transpose b
  have hg : Homotopic (g ≫ m) (𝟙 V) := by
    have h := transpose_homotopic hb
    simpa only [transpose_pre,transpose_transpose] using h
  have hmg : Homotopic (f ≫ transpose (m ≫ g)) (f ≫ transpose (𝟙 U)) := by
    have h := transpose_homotopic (homotopic_pre m hg)
    simpa only [← transpose_post, Category.assoc,Category.comp_id,Category.id_comp] using h
  have hgm := transpose_homotopic (hi ((ihom U).obj K) _ _ hmg)
  refine ⟨g, ?_, hg⟩
  simpa only [transpose_transpose] using hgm

lemma lastVertex_local (X : SSet.{u}) : Local (Subdivision.lastVertex.app X) :=
  local_of_homotopy_classes _ (fun K _ => precomp_lastVertex_surjective X K)
    (fun K _ => precomp_lastVertex_injective X K)

lemma local_of_precomp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : Local f) (hfg : Local (f ≫ g)) : Local g := by
  intro K hK
  have h := hfg K hK
  rw [pre_map,NatTrans.comp_app] at h
  exact heq_of_postcomp _ _ (hf K hK) h

lemma local_of_postcomp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hg : Local g) (hfg : Local (f ≫ g)) : Local f := by
  intro K hK
  have h := hfg K hK
  rw [pre_map,NatTrans.comp_app] at h
  exact heq_of_precomp _ _ (hg K hK) h

end Thomason.KanLocal

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition.Posetal
open SubdividedUnit KanLocal LastVertexProof

theorem kan_poset_replacement (K : SSet.{u}) [SSet.KanComplex K] :
    ∃ P : PartOrd.{u}, ∃ r : nerve P ⟶ K, Local r ∧ simplicialWeakEquivalences r := by
  obtain ⟨P,⟨e⟩⟩ := categorification_sdTwice_posetal K
  let E : N.obj (C.obj (D.obj K)) ≅ nerve P :=
    (oneNerveFunctorIso.app (C.obj (D.obj K))) ≪≫ nerveFunctor.mapIso e
  let l : D.obj K ⟶ K := Subdivision.lastVertex.app (SSet.sd.obj K) ≫
    Subdivision.lastVertex.app K
  have hl : Local l := local_comp (lastVertex_local _) (lastVertex_local _)
  obtain ⟨r,Hr⟩ := precomp_surjective (η (D.obj K)) (unit_local_one K) l
  have hr : Local r := local_of_precomp _ _ (unit_local_one K)
    (local_homotopic (homotopic_symm Hr) hl)
  have h : Local (E.inv ≫ r) := local_comp (local_iso _) hr
  exact ⟨P,E.inv ≫ r,h,local_weak _ h⟩
end Thomason.GeometricRecognition.Posetal

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath Subdivision

lemma kan_local_heq {A B : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) (h : Local f) : IsHomotopyEquivalence f := by
  obtain ⟨g,hg⟩ := precomp_surjective f h (𝟙 A)
  refine ⟨g,hg,precomp_injective f h _ _ ?_⟩
  simpa only [Category.assoc,Category.comp_id,Category.id_comp] using homotopic_post hg f

lemma kan_ex_poset_replacement (K : SSet.{u}) [SSet.KanComplex K] :
    ∃ P : PartOrd.{u}, ∃ r : nerve P ⟶ K, ∃ e : exInfinity (nerve P) ⟶ K,
      exInfinityComparison (nerve P) ≫ e = r ∧
      simplicialWeakEquivalences r ∧ IsHomotopyEquivalence e := by
  obtain ⟨P,r,hr,hw⟩ := Posetal.kan_poset_replacement K
  obtain ⟨e,he⟩ := extend_anodyne (exInfinityComparison (nerve P))
    (exInfinityComparison_anodyne _) r
  have : SSet.KanComplex (exInfinity (nerve P)) := exInfinity_kan _
  exact ⟨P,r,e,he,hw,kan_local_heq e (local_of_precomp _ _
    (local_anodyne _ (exInfinityComparison_anodyne _)) (he.symm ▸ hr))⟩

lemma relative_representative {E K A B : SSet.{u}}
    [SSet.KanComplex E] [SSet.KanComplex K]
    (e : E ⟶ K) (he : IsHomotopyEquivalence e) (i : B ⟶ A) [Mono i]
    (b : B ⟶ E) (a : A ⟶ K) (ha : i ≫ a = b ≫ e) :
    ∃ g : A ⟶ E, ∃ H : SSet.Homotopy (g ≫ e) a,
      i ≫ g = b ∧ (i ▷ Δ[1]) ≫ H.h = fst B Δ[1] ≫ b ≫ e := by
  let : HasLiftingProperty i (right e) := right_rlp e he i inferInstance
  let sq : CommSq (b ≫ left e) i (right e) a := ⟨by simpa using ha.symm⟩
  let g : A ⟶ E := sq.lift ≫ pullback.fst e (eval₀ K)
  let t : A ⟶ Paths K := sq.lift ≫ pullback.snd e (eval₀ K)
  have ht₀ : t ≫ eval₀ K = g ≫ e := by
    dsimp [t,g]
    simp only [Category.assoc,← pullback.condition]
  have ht₁ : t ≫ eval₁ K = a := sq.fac_right
  refine ⟨g,CoherentGluing.toHomotopy (uncurryR t)
    ((comp_eval₀ t).symm.trans ht₀) ((comp_eval₁ t).symm.trans ht₁), ?_, ?_⟩
  · dsimp [g]
    rw [← Category.assoc,sq.fac_left]
    simp [left, pullback.lift_fst]
  · change i ▷ Δ[1] ≫ uncurryR t = _
    rw [← uncurryR_pre]
    have ht : i ≫ t = b ≫ e ≫ const K := by
      dsimp [t]
      rw [← Category.assoc,sq.fac_left]
      simp [left, pullback.lift_snd]
    rw [ht]
    simp only [uncurryR_pre,const,uncurryR_curryR,whiskerRight_fst_assoc,whiskerRight_fst]

lemma finite_relative_stage {A B X : SSet.{u}} [SSet.Finite A] [SSet.Finite B]
    (i : B ⟶ A) (b : B ⟶ X) (g : A ⟶ exInfinity X)
    (hg : i ≫ g = b ≫ exInfinityComparison X) :
    ∃ n, ∃ t : A ⟶ exStage X n,
      t ≫ exInfinityInclusion X n = g ∧
      i ≫ t = b ≫ (exSequence X).map (homOfLE (Nat.zero_le n)) := by
  let : PreservesFilteredColimitsOfSize.{0,0} (coyoneda.obj (Opposite.op A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let : PreservesFilteredColimitsOfSize.{0,0} (coyoneda.obj (Opposite.op B)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨n,t,ht⟩ := Limits.exists_hom_of_preservesColimit_coyoneda
    (colimit.isColimit (exSequence X)) g
  obtain ⟨k,u,v,hk⟩ := Limits.exists_eq_of_preservesColimit_coyoneda
    (colimit.isColimit (exSequence X)) (j := 0) (i ≫ t) b (by
      rw [Category.assoc,ht]
      exact hg)
  change ∃ stage, ∃ stageLift : A ⟶ (exSequence X).obj stage,
    stageLift ≫ colimit.ι (exSequence X) stage = g ∧
      i ≫ stageLift = b ≫ (exSequence X).map (homOfLE (Nat.zero_le stage))
  refine ⟨k,t ≫ (exSequence X).map u,?_,?_⟩
  · rw [Category.assoc]
    rw [colimit.w]
    exact ht
  · have hv : v = homOfLE (Nat.zero_le k) := Subsingleton.elim _ _
    rw [Category.assoc,hv] at hk
    exact hk
end Thomason.GeometricRecognition

end

end OAI
