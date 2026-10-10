import OAI.CategoryTheory.Globular.Expansion

namespace OAI

universe u v w

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable def cutoffFreeGlobular {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : GlobularPresheaf.{v} ⥤ CutoffModels C q :=
  freeGlobular C ⋙ cutoffFunctor hC q

noncomputable def cutoffForgetGlobular (C : GlobularTheory.{v}) (q : ℕ) :
    CutoffModels C q ⥤ GlobularPresheaf.{v} :=
  (ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q)) ⋙ forgetGlobular C

noncomputable def cutoffGlobularAdjunction {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : cutoffFreeGlobular hC q ⊣ cutoffForgetGlobular C q :=
  (globularAdjunction C).comp (cutoffAdjunction hC q)

instance cutoffFreeGlobular_preservesColimits {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : PreservesColimitsOfSize.{v,v} (cutoffFreeGlobular hC q) :=
  (cutoffGlobularAdjunction hC q).leftAdjoint_preservesColimits

theorem cutoffFreeGlobular_cofibrant {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : GlobularPresheaf.{v}) :
    Cofibrant hC q ((cutoffFreeGlobular hC q).obj S) := by
  intro P Q p hp f
  have hp' : GlobularSet.LiftsBoundaries (underlyingMap p.hom) := by
    intro n
    exact (hasLiftingProperty_I_iff n p.hom).1
      ((boundaryClass_rlp_iff hC q 0 p).1 hp n (Nat.zero_le n))
  let A := cutoffGlobularAdjunction hC q
  obtain ⟨g, hg⟩ := GlobularPresheaf.liftsBoundaries_lift hp' (A.homEquiv S Q f)
  refine ⟨(A.homEquiv S P).symm g, ?_⟩
  apply (A.homEquiv S Q).injective
  rw [Adjunction.homEquiv_naturality_right]
  exact (congrArg (· ≫ (cutoffForgetGlobular C q).map p)
    ((A.homEquiv S P).apply_symm_apply g)).trans hg

noncomputable def shapeGlobularEquiv {C : GlobularTheory.{v}} (S : Shape) (X : C.Model) :
    (freeShape C S ⟶ X) ≃
      ((Shape.liftedRealization.{v}).obj S ⟶ (forgetGlobular C).obj X) :=
  yonedaEquiv.trans (Equiv.ofBijective (X.tuples.evaluation.app (op S))
    (X.tuples.evaluation_bijective S))

theorem shapeGlobularEquiv_natural {C : GlobularTheory.{v}} (S : Shape) {X Y : C.Model}
    (a : freeShape C S ⟶ X) (b : X ⟶ Y) :
    shapeGlobularEquiv S Y (a ≫ b) =
      shapeGlobularEquiv S X a ≫ (forgetGlobular C).map b := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  exact (ConcreteCategory.congr_hom (b.naturality
    (C.toTheoryData.arity.map (S.cellArrow k x.down)).op) (yonedaEquiv a)).symm

theorem cutoffFreeShape_cofibrant {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) : Cofibrant hC q ((cutoffFunctor hC q).obj (freeShape C S)) := by
  intro P Q p hp f
  have hp' : GlobularSet.LiftsBoundaries (underlyingMap p.hom) := by
    intro n
    exact (hasLiftingProperty_I_iff n p.hom).1
      ((boundaryClass_rlp_iff hC q 0 p).1 hp n (Nat.zero_le n))
  let A := cutoffAdjunction hC q
  let a := A.homEquiv (freeShape C S) Q f
  obtain ⟨g, hg⟩ := GlobularPresheaf.liftsBoundaries_lift hp' (shapeGlobularEquiv S Q.obj a)
  let l := (shapeGlobularEquiv S P.obj).symm g
  have hl : l ≫ p.hom = a := by
    apply (shapeGlobularEquiv S Q.obj).injective
    rw [shapeGlobularEquiv_natural]
    change shapeGlobularEquiv S P.obj ((shapeGlobularEquiv S P.obj).symm g) ≫ _ = _
    exact (congrArg (· ≫ (forgetGlobular C).map p.hom)
      ((shapeGlobularEquiv S P.obj).apply_symm_apply g)).trans hg
  refine ⟨(A.homEquiv (freeShape C S) P).symm l, ?_⟩
  apply (A.homEquiv (freeShape C S) Q).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact hl

open CategoryTheory CategoryTheory.Limits Opposite

structure CellGroupoid {C : GlobularTheory.{v}} (X : C.Model) (_hC : C.IsCoherator)
    (n : ℕ) where
  cell : X.underlying.Cell n

namespace CellGroupoid
variable {C : GlobularTheory.{v}} {X : C.Model} {hC : C.IsCoherator} {n : ℕ}

abbrev Edge (x y : CellGroupoid X hC n) :=
  {a : X.underlying.Cell (n+1) // X.underlying.source n a = x.cell ∧
    X.underlying.target n a = y.cell}

def edgeSetoid (x y : CellGroupoid X hC n) : Setoid (Edge x y) where
  r a b := X.underlying.Joined (n+1) a.1 b.1
  iseqv := ⟨fun a => X.joined_refl hC _ a.1,
    fun h => X.joined_symm hC h, fun h k => X.joined_trans hC h k⟩

noncomputable def edgeComp {x y z : CellGroupoid X hC n}
    (a : Edge x y) (b : Edge y z) : Edge x z :=
  ⟨X.compCell hC n a.1 b.1 (a.2.2.trans b.2.1.symm),
    (X.compCell_source hC n _ _ _).trans a.2.1,
    (X.compCell_target hC n _ _ _).trans b.2.2⟩

noncomputable instance : Category (CellGroupoid X hC n) where
  Hom x y := Quotient (edgeSetoid x y)
  id x := Quotient.mk _ ⟨X.unitCell hC n x.cell,
    X.unitCell_source hC n _, X.unitCell_target hC n _⟩
  comp a b := Quotient.map₂ edgeComp (fun {a a'} ha {b b'} hb =>
    X.joined_trans hC
      (X.compCell_congr_left hC n a.1 a'.1 b.1
        (a.2.2.trans b.2.1.symm) (a'.2.2.trans b.2.1.symm) ha)
      (X.compCell_congr_right hC n a'.1 b.1 b'.1
        (a'.2.2.trans b.2.1.symm) (a'.2.2.trans b'.2.1.symm) hb)) a b
  id_comp a := by
    induction a using Quotient.inductionOn with | h a =>
    apply Quotient.sound
    change X.underlying.Joined (n+1) (X.compCell hC n _ a.1 _) a.1
    simpa only [a.2.1] using X.compCell_left_unit hC n a.1
  comp_id a := by
    induction a using Quotient.inductionOn with | h a =>
    apply Quotient.sound
    change X.underlying.Joined (n+1) (X.compCell hC n a.1 _ _) a.1
    simpa only [a.2.2] using X.compCell_right_unit hC n a.1
  assoc a b c := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    induction c using Quotient.inductionOn with | h c =>
    exact Quotient.sound (X.compCell_assoc hC n a.1 b.1 c.1 _ _)

noncomputable def ofEdge {x y : CellGroupoid X hC n} (a : Edge x y) : x ⟶ y :=
  Quotient.mk _ a

theorem ofEdge_eq_iff {x y : CellGroupoid X hC n} (a b : Edge x y) :
    ofEdge a = ofEdge b ↔ X.underlying.Joined (n+1) a.1 b.1 :=
  Quotient.eq

noncomputable instance : Groupoid (CellGroupoid X hC n) := Groupoid.ofIsIso (by
  intro x y a
  induction a using Quotient.inductionOn with | h a =>
  refine ⟨ofEdge ⟨X.inverseCell hC n a.1,
    (X.inverseCell_source hC n _).trans a.2.2,
    (X.inverseCell_target hC n _).trans a.2.1⟩, ?_, ?_⟩
  · apply Quotient.sound
    change X.underlying.Joined (n+1) (X.compCell hC n a.1 (X.inverseCell hC n a.1) _) _
    simpa only [a.2.1] using X.compCell_inverse_right hC n a.1
  · apply Quotient.sound
    change X.underlying.Joined (n+1) (X.compCell hC n (X.inverseCell hC n a.1) a.1 _) _
    simpa only [a.2.2] using X.compCell_inverse_left hC n a.1)

noncomputable def map {Y : C.Model} (f : X ⟶ Y) :
    CellGroupoid X hC n ⥤ CellGroupoid Y hC n where
  obj x := ⟨(underlyingMap f).app n x.cell⟩
  map a := Quotient.map (fun a =>
    ⟨(underlyingMap f).app (n+1) a.1,
      ((underlyingMap f).source_app n a.1).symm.trans (congrArg _ a.2.1),
      ((underlyingMap f).target_app n a.1).symm.trans (congrArg _ a.2.2)⟩)
    (fun _ _ h => (underlyingMap f).map_joined h) a
  map_id x := by
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    exact map_unitCell f hC n x.cell
  map_comp a b := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    exact map_compCell f hC n a.1 b.1 _

end CellGroupoid
end Grothendieck.GlobularTheory.Model

namespace Grothendieck.GlobularSet

namespace LiftStage
variable {A X Y : GlobularSet.{v}} {p : Hom X Y} {f : Hom A Y}

noncomputable def extendTop {n : ℕ} (a : LiftStage p f n)
    (z : A.Cell (n+1) → X.Cell (n+1))
    (hs : ∀ x, X.source n (z x) = a.app n le_rfl (A.source n x))
    (ht : ∀ x, X.target n (z x) = a.app n le_rfl (A.target n x))
    (hzp : ∀ x, p.app (n+1) (z x) = f.app (n+1) x) : LiftStage p f (n+1) where
  app k hk x := if h : k ≤ n then a.app k h x else by
    have e : k = n+1 := by omega
    subst k
    exact z x
  source_app k hk x := by
    dsimp only
    split_ifs with h h'
    · exact a.source_app k h' x
    · have e : k = n := by omega
      subst k
      exact (hs x).symm
    · omega
    · omega
  target_app k hk x := by
    dsimp only
    split_ifs with h h'
    · exact a.target_app k h' x
    · have e : k = n := by omega
      subst k
      exact (ht x).symm
    · omega
    · omega
  fac k hk x := by
    dsimp only
    split_ifs with h
    · exact a.fac k h x
    · have e : k = n+1 := by omega
      subst k
      exact hzp x

noncomputable def ofBounded {n : ℕ} (a : LiftStage p f n)
    (hA : ∀ k, n < k → IsEmpty (A.Cell k)) : Hom A X where
  app k x := if hk : k ≤ n then a.app k hk x else (hA k (by omega)).false x |>.elim
  source_app k x := by
    have hk : k+1 ≤ n := by
      by_contra h
      exact (hA (k+1) (by omega)).false x
    simp only [dite_eq_left hk, dite_eq_left (show k ≤ n by omega)]
    exact a.source_app k hk x
  target_app k x := by
    have hk : k+1 ≤ n := by
      by_contra h
      exact (hA (k+1) (by omega)).false x
    simp only [dite_eq_left hk, dite_eq_left (show k ≤ n by omega)]
    exact a.target_app k hk x

theorem ofBounded_fac {n : ℕ} (a : LiftStage p f n)
    (hA : ∀ k, n < k → IsEmpty (A.Cell k)) : (a.ofBounded hA).comp p = f := by
  ext k x
  have hk : k ≤ n := by
    by_contra h
    exact (hA k (by omega)).false x
  simpa only [Hom.comp, ofBounded, dite_eq_left hk] using a.fac k hk x

end LiftStage

theorem lift_of_top_joined {A X Y : GlobularSet.{v}} {p : Hom X Y}
    (n : ℕ) (hp : LiftsSource p (n+1)) (f : Hom A Y) (a : Hom A X)
    (hA : ∀ k, n+1 < k → IsEmpty (A.Cell k))
    (ha : ∀ k, k ≤ n → ∀ x, p.app k (a.app k x) = f.app k x)
    (htop : ∀ x, Y.Joined (n+1) (p.app (n+1) (a.app (n+1) x)) (f.app (n+1) x)) :
    ∃ g : Hom A X, g.comp p = f := by
  let lo : LiftStage p f n :=
    { app := fun k _ => a.app k
      source_app := fun k _ => a.source_app k
      target_app := fun k _ => a.target_app k
      fac := ha }
  have h x : ∃ z : X.Cell (n+1),
      X.source n z = a.app n (A.source n x) ∧
      X.target n z = a.app n (A.target n x) ∧ p.app (n+1) z = f.app (n+1) x := by
    obtain ⟨c, hc₀, hc₁⟩ := htop x
    obtain ⟨d, hd₀, hd⟩ := hp (a.app (n+1) x) c hc₀
    refine ⟨X.target (n+1) d, ?_, ?_, ?_⟩
    · rw [← X.source_source, hd₀, ← a.source_app]
    · rw [← X.target_source, hd₀, ← a.target_app]
    · rw [p.target_app, hd, hc₁]
  choose z hs ht hz using h
  let b := lo.extendTop z hs ht hz
  exact ⟨b.ofBounded hA, b.ofBounded_fac hA⟩

end Grothendieck.GlobularSet

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits Opposite

theorem free_hasFillers_of_top_homotopy {C : GlobularTheory.{v}}
    (hC : C.IsCoherator) (q n : ℕ) (H : ExpansionContraction hC q (n+1))
    (S : GlobularPresheaf.{v})
    (hS : ∀ k, n+1 < k → IsEmpty (S.underlying.Cell k))
    (L : CutoffModels C q) (hL : Cofibrant hC q L)
    (hLF : L.obj.underlying.HasFillers)
    (f : (cutoffFreeGlobular hC q).obj S ⟶ L)
    (g : L ⟶ (cutoffFreeGlobular hC q).obj S)
    (hlo : ∀ k, k ≤ n → ∀ x,
      (underlyingMap (f ≫ g).hom).app k
        (GlobularPresheaf.underlyingMap ((cutoffGlobularAdjunction hC q).unit.app S) |>.app k x) =
      (GlobularPresheaf.underlyingMap ((cutoffGlobularAdjunction hC q).unit.app S)).app k x)
    (htop : ∀ x, ((cutoffFreeGlobular hC q).obj S).obj.underlying.Joined (n+1)
      ((underlyingMap (f ≫ g).hom).app (n+1)
        ((GlobularPresheaf.underlyingMap ((cutoffGlobularAdjunction hC q).unit.app S)).app (n+1) x))
      ((GlobularPresheaf.underlyingMap ((cutoffGlobularAdjunction hC q).unit.app S)).app (n+1) x)) :
    ((cutoffFreeGlobular hC q).obj S).obj.underlying.HasFillers := by
  let := sourceClass_smallObject hC q (n+1)
  let W := sourceClass hC q (n+1)
  let F := MorphismProperty.factorizationData W.rlp.llp W.rlp g
  have hQ := H F.i F.hi hL hLF
  let A := cutoffGlobularAdjunction hC q
  let U := cutoffForgetGlobular C q
  let eta := A.unit.app S
  let a := eta ≫ U.map f ≫ U.map F.i
  have hp : GlobularSet.LiftsSource (underlyingMap F.p.hom) (n+1) :=
    (hasLiftingProperty_J_iff (n+1) F.p.hom).1
      ((sourceClass_rlp_iff hC q (n+1) F.p).1 F.hp (n+1) le_rfl)
  have hap : a ≫ U.map F.p = eta ≫ U.map (f ≫ g) := by
    simp only [a, Category.assoc, ← Functor.map_comp, F.fac]
  have hap' := congrArg GlobularPresheaf.underlyingMap hap
  obtain ⟨b, hb⟩ := GlobularSet.lift_of_top_joined n hp
    (GlobularPresheaf.underlyingMap eta) (GlobularPresheaf.underlyingMap a) hS
    (by
      intro k hk x
      have e := congrFun (congrArg (fun z => z.app k) hap') x
      exact e.trans (hlo k hk x))
    (by
      intro x
      have e := congrFun (congrArg (fun z => z.app (n+1)) hap') x
      exact e ▸ htop x)
  let b' : S ⟶ U.obj F.Z := S.underlyingPresheafIso.inv ≫
    b.presheafMap ≫ (U.obj F.Z).underlyingPresheafIso.hom
  have hb' : b' ≫ U.map F.p = eta := by
    apply GlobularPresheaf.underlyingMap_injective
    exact hb
  let s := (A.homEquiv S F.Z).symm b'
  have hs : s ≫ F.p = 𝟙 _ := by
    apply (A.homEquiv S _).injective
    rw [Adjunction.homEquiv_naturality_right]
    change A.homEquiv S F.Z ((A.homEquiv S F.Z).symm b') ≫ U.map F.p = _
    rw [Equiv.apply_symm_apply, hb']
    exact (A.homEquiv_id S).symm
  apply hQ.retract (underlyingMap s.hom) (underlyingMap F.p.hom)
  exact congrArg (fun z => underlyingMap z.hom) hs

end Grothendieck.GlobularTheory.Model

end OAI
