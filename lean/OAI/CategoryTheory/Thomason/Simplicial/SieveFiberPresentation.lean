import OAI.CategoryTheory.Thomason.Simplicial.ConstructedPosetCosieves
import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.TerminalConeUniversal
import OAI.CategoryTheory.Thomason.Strict.FiniteLabelledPresentation
import Mathlib.Tactic.FinCases

namespace OAI

section

/-! # Target-fibre colimits in every positive finite dimension

All constructions are internal to the original category of truncated
strict categories. No preservation by its inclusion into omega is used.
-/

namespace Thomason.Construction.StrictOmegaCategory.FiniteOppositeLabels

open CategoryTheory CategoryTheory.Limits

variable (n : ℕ)

def object (C : Truncated.{0} (n + 1)) : Truncated.{0} (n + 1) :=
  ⟨opposite C.val, fun x => ⟨(C.property x).2, (C.property x).1⟩⟩

def functor : Truncated.{0} (n + 1) ⥤ Truncated.{0} (n + 1) where
  obj := object n
  map := oppositeMap
  map_id C := by apply Hom.ext; rfl
  map_comp f g := by apply Hom.ext; rfl

def doubleIso (C : Truncated.{0} (n + 1)) : object n (object n C) ≅ C where
  hom := (doubleOppositeIso C.val).hom
  inv := (doubleOppositeIso C.val).inv
  hom_inv_id := (doubleOppositeIso C.val).hom_inv_id
  inv_hom_id := (doubleOppositeIso C.val).inv_hom_id

def equivalence : Truncated.{0} (n + 1) ≌ Truncated.{0} (n + 1) where
  functor := functor n
  inverse := functor n
  unitIso := NatIso.ofComponents (fun C => (doubleIso n C).symm) (by
    intro C D f
    apply Hom.ext
    rfl)
  counitIso := NatIso.ofComponents (doubleIso n) (by
    intro C D f
    apply Hom.ext
    rfl)
  functor_unitIso_comp C := by apply Hom.ext; rfl

def overFunctor : Over (finiteInterval n) ⥤ Over (finiteInterval n) where
  obj X := Over.mk (show object n X.left ⟶ finiteInterval n from OppositeLabels.label X.hom)
  map {X Y} f := Over.homMk (oppositeMap f.left) (by
    apply Hom.ext
    funext x
    exact congrArg OppositeLabels.reverseCell (congrArg (fun q => q.toFun x) (Over.w f)))
  map_id X := Over.OverMorphism.ext (by apply Hom.ext; rfl)
  map_comp f g := Over.OverMorphism.ext (by apply Hom.ext; rfl)

def overDoubleIso (X : Over (finiteInterval n)) :
    (overFunctor n).obj ((overFunctor n).obj X) ≅ X :=
  Over.isoMk (doubleIso n X.left) (by
    apply Hom.ext
    funext x
    apply StrictPoset.Cell.ext <;> exact (Fin.rev_rev _).symm)

def overEquivalence : Over (finiteInterval n) ≌ Over (finiteInterval n) where
  functor := overFunctor n
  inverse := overFunctor n
  unitIso := NatIso.ofComponents (fun X => (overDoubleIso n X).symm) (by
    intro X Y f
    apply Over.OverMorphism.ext
    apply Hom.ext
    rfl)
  counitIso := NatIso.ofComponents (overDoubleIso n) (by
    intro X Y f
    apply Over.OverMorphism.ext
    apply Hom.ext
    rfl)
  functor_unitIso_comp X := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    rfl

def fiberIso (X : Over (finiteInterval n)) :
    object n ((finiteLabelFiberFunctor n 0).obj ((overFunctor n).obj X)) ≅
      (finiteLabelFiberFunctor n 1).obj X where
  hom := (OppositeLabels.fiberIso (Over.mk (show X.left.val ⟶ StrictPoset.category (Fin 2) from X.hom))).hom
  inv := (OppositeLabels.fiberIso (Over.mk (show X.left.val ⟶ StrictPoset.category (Fin 2) from X.hom))).inv
  hom_inv_id := by apply Hom.ext; funext x; apply Subtype.ext; rfl
  inv_hom_id := by apply Hom.ext; funext x; apply Subtype.ext; rfl

def fiberNatIso : overFunctor n ⋙ finiteLabelFiberFunctor n 0 ⋙ functor n ≅
    finiteLabelFiberFunctor n 1 :=
  NatIso.ofComponents (fiberIso n) (by
    intro X Y f
    apply Hom.ext
    funext x
    apply Subtype.ext
    rfl)

/-- Formation of the full target fibre preserves all colimits in the
specified positive finite dimension. -/
theorem oneFiber_preservesColimits :
    PreservesColimitsOfSize.{0,0} (finiteLabelFiberFunctor n 1) := by
  have := TerminalCone.finiteZeroFiber_preservesColimits n
  have : PreservesColimitsOfSize.{0,0} (overFunctor n) :=
    (overEquivalence n).toAdjunction.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0,0} (functor n) :=
    (equivalence n).toAdjunction.leftAdjoint_preservesColimits
  exact preservesColimits_of_natIso (fiberNatIso n)

end Thomason.Construction.StrictOmegaCategory.FiniteOppositeLabels

end

section

/-! # Both published endpoint-fibre colimit statements are constructed -/

namespace Thomason.Construction

open StrictOmegaCategory

/-- The complete endpoint-fibre interface is supplied by actual adjunctions
and explicit opposite equivalences, in all the required dimensions. -/
theorem constructedLabelFiberInput : PublishedLabelFiberInput where
  omega e := by
    fin_cases e
    · exact TerminalCone.zeroFiber_preservesColimits
    · exact OppositeLabels.oneFiber_preservesColimits
  finite n e := by
    fin_cases e
    · exact TerminalCone.finiteZeroFiber_preservesColimits n
    · exact FiniteOppositeLabels.oneFiber_preservesColimits n

end Thomason.Construction

end

section

/-! # Intersections of full cosieves on the actual strict categories -/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory

variable {C D : StrictOmegaCategory.{0}}

/-- Minimum combines membership in two full one fibres. -/
def minLabel (p q : C ⟶ StrictPoset.category (Fin 2)) :
    C ⟶ StrictPoset.category (Fin 2) where
  toFun x := ⟨min (p.toFun x).first (q.toFun x).first,
    min (p.toFun x).last (q.toFun x).last,
    min_le_min (p.toFun x).ordered (q.toFun x).ordered⟩
  map_face a n x := by
    change (⟨min (p.toFun (C.face a n x)).first (q.toFun (C.face a n x)).first,
      min (p.toFun (C.face a n x)).last (q.toFun (C.face a n x)).last, _⟩ :
      StrictPoset.Cell (Fin 2)) = _
    rw [p.map_face, q.map_face]
    cases n <;> cases a <;> rfl
  map_comp n x y hxy h' := by
    have hp' := (p.map_face true n x).symm.trans ((congrArg p.toFun hxy).trans (p.map_face false n y))
    have hq' := (q.map_face true n x).symm.trans ((congrArg q.toFun hxy).trans (q.map_face false n y))
    have hp := p.map_comp n x y hxy hp'
    have hq := q.map_comp n x y hxy hq'
    change (⟨min (p.toFun (C.comp n x y hxy)).first (q.toFun (C.comp n x y hxy)).first,
      min (p.toFun (C.comp n x y hxy)).last (q.toFun (C.comp n x y hxy)).last, _⟩ :
      StrictPoset.Cell (Fin 2)) = _
    rw [hp, hq]
    cases n <;> rfl

theorem minLabel_one_iff (p q : C ⟶ StrictPoset.category (Fin 2)) (x : C) :
    (minLabel p q).toFun x = StrictPoset.identity 1 ↔
      p.toFun x = StrictPoset.identity 1 ∧ q.toFun x = StrictPoset.identity 1 := by
  constructor
  · intro he
    have hs := congrArg (fun z : StrictPoset.Cell (Fin 2) => z.first) he
    have ht := congrArg (fun z : StrictPoset.Cell (Fin 2) => z.last) he
    change min (p.toFun x).first (q.toFun x).first = 1 at hs
    change min (p.toFun x).last (q.toFun x).last = 1 at ht
    have hp₀ : (p.toFun x).first = 1 := by
      have hh := min_le_left (p.toFun x).first (q.toFun x).first
      rw [hs] at hh
      omega
    have hq₀ : (q.toFun x).first = 1 := by
      have hh := min_le_right (p.toFun x).first (q.toFun x).first
      rw [hs] at hh
      omega
    have hp₁ : (p.toFun x).last = 1 := by
      have hh := min_le_left (p.toFun x).last (q.toFun x).last
      rw [ht] at hh
      omega
    have hq₁ : (q.toFun x).last = 1 := by
      have hh := min_le_right (p.toFun x).last (q.toFun x).last
      rw [ht] at hh
      omega
    exact ⟨StrictPoset.Cell.ext hp₀ hp₁, StrictPoset.Cell.ext hq₀ hq₁⟩
  · rintro ⟨hp, hq⟩
    apply StrictPoset.Cell.ext
    · change min (p.toFun x).first (q.toFun x).first = 1
      rw [hp, hq]
      rfl
    · change min (p.toFun x).last (q.toFun x).last = 1
      rw [hp, hq]
      rfl

theorem minLabel_precomp (p q : C ⟶ StrictPoset.category (Fin 2)) (f : D ⟶ C) :
    f ≫ minLabel p q = minLabel (f ≫ p) (f ≫ q) := by
  apply Hom.ext
  rfl

end Thomason.Construction.StrictOmegaCategory

namespace Thomason.Construction

open CategoryTheory StrictOmegaCategory

theorem cosieveCharacteristic_inter {E : Type} [PartialOrder E]
    (A B : Set E) (hA : IsUpperSet A) (hB : IsUpperSet B) (x : E) :
    cosieveCharacteristic (A ∩ B) (hA.inter hB) x =
      min (cosieveCharacteristic A hA x) (cosieveCharacteristic B hB x) := by
  have hone : cosieveCharacteristic (A ∩ B) (hA.inter hB) x = 1 ↔
      cosieveCharacteristic A hA x = 1 ∧ cosieveCharacteristic B hB x = 1 := by
    simp only [cosieveCharacteristic_one_iff, Set.mem_inter_iff]
  have h01 (i : Fin 2) : i = 0 ∨ i = 1 := by omega
  rcases h01 (cosieveCharacteristic A hA x) with ha | ha <;>
    rcases h01 (cosieveCharacteristic B hB x) with hb | hb <;> rw [ha, hb]
  all_goals first
  | exact (hone.mpr ⟨ha, hb⟩).trans (by rfl)
  | have hz : cosieveCharacteristic (A ∩ B) (hA.inter hB) x ≠ 1 := by
      intro hz
      obtain ⟨ha', hb'⟩ := hone.mp hz
      omega
    have hzero : cosieveCharacteristic (A ∩ B) (hA.inter hB) x = 0 := by omega
    exact hzero.trans (by decide)

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The minimum label cuts out the actual intersection of upper subsets. -/
theorem cosieveMembershipLabel_inter {E : Type} [PartialOrder E]
    (A B : Set E) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    minLabel (h.membershipLabel Aᶜ hA.compl) (h.membershipLabel Bᶜ hB.compl) =
      h.membershipLabel (A ∩ B)ᶜ (hA.inter hB).compl := by
  apply Hom.ext
  funext x
  apply StrictPoset.Cell.ext
  · exact (cosieveCharacteristic_inter A B hA hB ((h.posetEvaluation E).toFun x).first).symm
  · exact (cosieveCharacteristic_inter A B hA hB ((h.posetEvaluation E).toFun x).last).symm

end NormalizedSimplexIdentities
end Thomason.Construction

end

section

/-! # The actual right adjoint of the full one-fibre functor

The initial cone is obtained by reversing the terminal cone. The same
construction stays inside every positive finite dimension.
-/

namespace Thomason.Construction.StrictOmegaCategory.InitialCone

open CategoryTheory

def overFunctor : StrictOmegaCategory.{0} ⥤ Over (StrictPoset.category (Fin 2)) :=
  oppositeFunctor ⋙ TerminalCone.overFunctor ⋙ OppositeLabels.overFunctor

def category (C : StrictOmegaCategory.{0}) : StrictOmegaCategory.{0} :=
  (overFunctor.obj C).left

def label (C : StrictOmegaCategory.{0}) : category C ⟶ StrictPoset.category (Fin 2) :=
  (overFunctor.obj C).hom

noncomputable def adjunction : labelFiberFunctor (Fin 2) 1 ⊣ overFunctor :=
  ((OppositeLabels.equivalence.toAdjunction.comp TerminalCone.adjunction).comp
    oppositeEquivalence.toAdjunction).ofNatIsoLeft OppositeLabels.fiberNatIso

def finiteOverFunctor (n : ℕ) : Truncated.{0} (n+1) ⥤ Over (finiteInterval n) :=
  FiniteOppositeLabels.functor n ⋙ TerminalCone.finiteOverFunctor n ⋙
    FiniteOppositeLabels.overFunctor n

def finiteCategory (n : ℕ) (C : Truncated.{0} (n+1)) : Truncated.{0} (n+1) :=
  ((finiteOverFunctor n).obj C).left

noncomputable def finiteAdjunction (n : ℕ) :
    finiteLabelFiberFunctor n 1 ⊣ finiteOverFunctor n :=
  (((FiniteOppositeLabels.overEquivalence n).toAdjunction.comp
    (TerminalCone.finiteAdjunction n)).comp
      (FiniteOppositeLabels.equivalence n).toAdjunction).ofNatIsoLeft
        (FiniteOppositeLabels.fiberNatIso n)

/-- The finite adjunction uses the very same strict extension on cells. -/
theorem finite_homEquiv_underlying (n : ℕ) (X : Over (finiteInterval n))
    (D : Truncated.{0} (n+1)) (f : (finiteLabelFiberFunctor n 1).obj X ⟶ D) :
    ((finiteAdjunction n).homEquiv X D f).left =
      (adjunction.homEquiv (Over.mk (show X.left.val ⟶ StrictPoset.category (Fin 2) from X.hom))
        D.val (show labelFiber X.hom 1 ⟶ D.val from f)).left := by
  apply Hom.ext
  rfl

end Thomason.Construction.StrictOmegaCategory.InitialCone

end

section

/-! # Finite reflection commutes with the actual one fibre

The right adjoint of one-fibre formation is the initial cone, which stays
in every positive finite dimension. Its explicit adjunction therefore makes
the one-fibre of a reflected label a reflection of the original one-fibre.
-/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n) {X : StrictOmegaCategory.{0}}
  (p : X ⟶ StrictPoset.category (Fin 2))
  (q : (r.reflect.obj X).val ⟶ StrictPoset.category (Fin 2))
  (hq : r.adjunction.unit.app X ≫ q = p)

/-- The full one fibre, kept inside the positive finite category. -/
def reflectedOneLabelFiber : Truncated (n + 1) :=
  (finiteLabelFiberFunctor n 1).obj
    (Over.mk (show r.reflect.obj X ⟶ finiteInterval n from q))

/-- Restriction of the original reflection unit to its one fibre. -/
def oneFiberUnit : labelFiber p 1 ⟶ (r.reflectedOneLabelFiber q).val :=
  labelFiberMap p q 1 (r.adjunction.unit.app X) hq

/-- Reflection descends maps to the initial cone while retaining the label. -/
noncomputable def oneFiberOverEquiv (D : Truncated (n + 1)) :
    ((Over.mk (show r.reflect.obj X ⟶ finiteInterval n from q)) ⟶
        (InitialCone.finiteOverFunctor n).obj D) ≃
      ((Over.mk p) ⟶ InitialCone.overFunctor.obj D.val) where
  toFun g := by
    let gl : (r.reflect.obj X).val ⟶ InitialCone.category D.val := g.left
    have hg : gl ≫ InitialCone.label D.val = q := Over.w g
    refine Over.homMk (r.adjunction.unit.app X ≫ gl) ?_
    change (r.adjunction.unit.app X ≫ gl) ≫ InitialCone.label D.val = p
    exact (Category.assoc (r.adjunction.unit.app X) gl (InitialCone.label D.val)).trans
      ((congrArg (fun k => r.adjunction.unit.app X ≫ k) hg).trans hq)
  invFun f := by
    let g : r.reflect.obj X ⟶ InitialCone.finiteCategory n D :=
      (r.adjunction.homEquiv X (InitialCone.finiteCategory n D)).symm f.left
    have hg : r.adjunction.unit.app X ≫ g = f.left :=
      (r.adjunction.homEquiv_apply X (InitialCone.finiteCategory n D) g).symm.trans
        ((r.adjunction.homEquiv X (InitialCone.finiteCategory n D)).apply_symm_apply f.left)
    let gl : (r.reflect.obj X).val ⟶ InitialCone.category D.val := g
    let fl : X ⟶ InitialCone.category D.val := f.left
    have hg' : r.adjunction.unit.app X ≫ gl = fl := hg
    have hf : fl ≫ InitialCone.label D.val = p := Over.w f
    refine Over.homMk g ?_
    apply r.unit_hom_ext X (truncatedPoset (Fin 2))
    change r.adjunction.unit.app X ≫ (gl ≫ InitialCone.label D.val) =
      r.adjunction.unit.app X ≫ q
    exact ((Category.assoc (r.adjunction.unit.app X) gl (InitialCone.label D.val)).symm.trans
      ((congrArg (fun k => k ≫ InitialCone.label D.val) hg').trans hf)).trans hq.symm
  left_inv g := by
    apply Over.OverMorphism.ext
    apply r.unit_hom_ext X (InitialCone.finiteCategory n D)
    exact ((r.adjunction.homEquiv_apply X (InitialCone.finiteCategory n D) _).symm.trans
      ((r.adjunction.homEquiv X (InitialCone.finiteCategory n D)).apply_symm_apply _))
  right_inv f := by
    apply Over.OverMorphism.ext
    exact ((r.adjunction.homEquiv_apply X (InitialCone.finiteCategory n D) _).symm.trans
      ((r.adjunction.homEquiv X (InitialCone.finiteCategory n D)).apply_symm_apply _))

/-- The universal bijection of the reflected one fibre. -/
noncomputable def oneFiberHomEquiv (D : Truncated (n + 1)) :
    (r.reflectedOneLabelFiber q ⟶ D) ≃ (labelFiber p 1 ⟶ D.val) :=
  ((InitialCone.finiteAdjunction n).homEquiv
    (Over.mk (show r.reflect.obj X ⟶ finiteInterval n from q)) D).trans
      ((r.oneFiberOverEquiv p q hq D).trans
        (InitialCone.adjunction.homEquiv (Over.mk p) D.val).symm)

/-- The bijection is actual precomposition with the restricted unit. -/
theorem oneFiberHomEquiv_apply (D : Truncated (n + 1))
    (f : r.reflectedOneLabelFiber q ⟶ D) :
    r.oneFiberHomEquiv p q hq D f = r.oneFiberUnit p q hq ≫ f := by
  apply (InitialCone.adjunction.homEquiv (Over.mk p) D.val).injective
  change (InitialCone.adjunction.homEquiv (Over.mk p) D.val)
    ((InitialCone.adjunction.homEquiv (Over.mk p) D.val).symm _) = _
  rw [Equiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  change r.adjunction.unit.app X ≫
    (((InitialCone.finiteAdjunction n).homEquiv
      (Over.mk (show r.reflect.obj X ⟶ finiteInterval n from q)) D) f).left = _
  have hf := InitialCone.finite_homEquiv_underlying n
    (Over.mk (show r.reflect.obj X ⟶ finiteInterval n from q)) D f
  let u : Over.mk p ⟶ Over.mk q := Over.homMk (r.adjunction.unit.app X) hq
  exact (congrArg (fun k : (r.reflect.obj X).val ⟶ InitialCone.category D.val =>
    r.adjunction.unit.app X ≫ k) hf).trans
      (congrArg (fun z => z.left)
        (InitialCone.adjunction.homEquiv_naturality_left u
          (show labelFiber q 1 ⟶ D.val from f)).symm)

end Thomason.Construction.FiniteReflectionInput

end

section

/-! # Finite reflection commutes with the actual zero fibre

The right adjoint of zero-fibre formation is the terminal cone, which stays
in every positive finite dimension. Its explicit adjunction therefore makes
the zero-fibre of a reflected label a reflection of the original zero-fibre.
-/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n) {X : StrictOmegaCategory.{0}}
  (p : X ⟶ StrictPoset.category (Fin 2))
  (q : (r.reflect.obj X).val ⟶ StrictPoset.category (Fin 2))
  (hq : r.adjunction.unit.app X ≫ q = p)

/-- The full zero fibre, kept inside the positive finite category. -/
def reflectedLabelFiber : Truncated (n + 1) :=
  (finiteLabelFiberFunctor n 0).obj
    (Over.mk (show r.reflect.obj X ⟶ finiteInterval n from q))

/-- Restriction of the original reflection unit to its zero fibre. -/
def zeroFiberUnit : labelFiber p 0 ⟶ (r.reflectedLabelFiber q).val :=
  labelFiberMap p q 0 (r.adjunction.unit.app X) hq

/-- Reflection descends maps to the terminal cone while retaining the label. -/
noncomputable def zeroFiberOverEquiv (D : Truncated (n + 1)) :
    ((Over.mk (show r.reflect.obj X ⟶ finiteInterval n from q)) ⟶
        (TerminalCone.finiteOverFunctor n).obj D) ≃
      ((Over.mk p) ⟶ TerminalCone.overFunctor.obj D.val) where
  toFun g := by
    let gl : (r.reflect.obj X).val ⟶ TerminalCone.category D.val := g.left
    have hg : gl ≫ TerminalCone.label D.val = q := Over.w g
    refine Over.homMk (r.adjunction.unit.app X ≫ gl) ?_
    change (r.adjunction.unit.app X ≫ gl) ≫ TerminalCone.label D.val = p
    exact (Category.assoc (r.adjunction.unit.app X) gl (TerminalCone.label D.val)).trans
      ((congrArg (fun k => r.adjunction.unit.app X ≫ k) hg).trans hq)
  invFun f := by
    let g : r.reflect.obj X ⟶ TerminalCone.finiteCategory n D :=
      (r.adjunction.homEquiv X (TerminalCone.finiteCategory n D)).symm f.left
    have hg : r.adjunction.unit.app X ≫ g = f.left :=
      (r.adjunction.homEquiv_apply X (TerminalCone.finiteCategory n D) g).symm.trans
        ((r.adjunction.homEquiv X (TerminalCone.finiteCategory n D)).apply_symm_apply f.left)
    let gl : (r.reflect.obj X).val ⟶ TerminalCone.category D.val := g
    let fl : X ⟶ TerminalCone.category D.val := f.left
    have hg' : r.adjunction.unit.app X ≫ gl = fl := hg
    have hf : fl ≫ TerminalCone.label D.val = p := Over.w f
    refine Over.homMk g ?_
    apply r.unit_hom_ext X (truncatedPoset (Fin 2))
    change r.adjunction.unit.app X ≫ (gl ≫ TerminalCone.label D.val) =
      r.adjunction.unit.app X ≫ q
    exact ((Category.assoc (r.adjunction.unit.app X) gl (TerminalCone.label D.val)).symm.trans
      ((congrArg (fun k => k ≫ TerminalCone.label D.val) hg').trans hf)).trans hq.symm
  left_inv g := by
    apply Over.OverMorphism.ext
    apply r.unit_hom_ext X (TerminalCone.finiteCategory n D)
    exact ((r.adjunction.homEquiv_apply X (TerminalCone.finiteCategory n D) _).symm.trans
      ((r.adjunction.homEquiv X (TerminalCone.finiteCategory n D)).apply_symm_apply _))
  right_inv f := by
    apply Over.OverMorphism.ext
    exact ((r.adjunction.homEquiv_apply X (TerminalCone.finiteCategory n D) _).symm.trans
      ((r.adjunction.homEquiv X (TerminalCone.finiteCategory n D)).apply_symm_apply _))

/-- The universal bijection of the reflected zero fibre. -/
noncomputable def zeroFiberHomEquiv (D : Truncated (n + 1)) :
    (r.reflectedLabelFiber q ⟶ D) ≃ (labelFiber p 0 ⟶ D.val) :=
  (TerminalCone.finiteHomEquiv n
    (Over.mk (show r.reflect.obj X ⟶ finiteInterval n from q)) D).trans
      ((r.zeroFiberOverEquiv p q hq D).trans
        (TerminalCone.homEquiv (Over.mk p) D.val).symm)

/-- The bijection is actual precomposition with the restricted unit. -/
theorem zeroFiberHomEquiv_apply (D : Truncated (n + 1))
    (f : r.reflectedLabelFiber q ⟶ D) :
    r.zeroFiberHomEquiv p q hq D f = r.zeroFiberUnit p q hq ≫ f := by
  apply Hom.ext
  funext x
  apply TerminalCone.Cell.old.inj
  change TerminalCone.Cell.old
    ((TerminalCone.restrict p (r.adjunction.unit.app X ≫ TerminalCone.extend q f) _).toFun x) = _
  refine (TerminalCone.old_restrict p _ _ x).trans ?_
  change TerminalCone.extendCell q f ((r.adjunction.unit.app X).toFun x.val) = _
  have hx : lastLabel q ((r.adjunction.unit.app X).toFun x.val) = 0 := by
    have he := (fullCell_label_iff q 0
      ((r.zeroFiberUnit p q hq).toFun x).val).mp
        ((r.zeroFiberUnit p q hq).toFun x).property
    exact congrArg StrictPoset.Cell.last he
  exact TerminalCone.extendCell_zero q f _ hx

end Thomason.Construction.FiniteReflectionInput

end

section

/-! # The canonical reflection / zero-fibre comparison is an isomorphism -/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n) {X : StrictOmegaCategory.{0}}
  (p : X ⟶ StrictPoset.category (Fin 2))
  (q : (r.reflect.obj X).val ⟶ StrictPoset.category (Fin 2))
  (hq : r.adjunction.unit.app X ≫ q = p)

theorem zeroFiberUnit_hom_ext (D : Truncated (n + 1))
    {f g : r.reflectedLabelFiber q ⟶ D}
    (he : r.zeroFiberUnit p q hq ≫ f = r.zeroFiberUnit p q hq ≫ g) : f = g :=
  (r.zeroFiberHomEquiv p q hq D).injective
    ((r.zeroFiberHomEquiv_apply p q hq D f).trans
      (he.trans (r.zeroFiberHomEquiv_apply p q hq D g).symm))

/-- The canonical map from the reflected original fibre to the reflected label's fibre. -/
noncomputable def zeroFiberComparison :
    r.reflect.obj (labelFiber p 0) ⟶ r.reflectedLabelFiber q :=
  (r.adjunction.homEquiv (labelFiber p 0) (r.reflectedLabelFiber q)).symm
    (r.zeroFiberUnit p q hq)

/-- Compatibility on every original zero-fibre cell. -/
theorem zeroFiberComparison_fac :
    r.adjunction.unit.app (labelFiber p 0) ≫ r.zeroFiberComparison p q hq =
      r.zeroFiberUnit p q hq :=
  (r.adjunction.homEquiv_apply (labelFiber p 0) (r.reflectedLabelFiber q) _).symm.trans
    ((r.adjunction.homEquiv (labelFiber p 0) (r.reflectedLabelFiber q)).apply_symm_apply _)

/-- The terminal-cone bijection identifies the two reflection universal properties. -/
theorem zeroFiberComparison_isIso : IsIso (r.zeroFiberComparison p q hq) := by
  let F := labelFiber p 0
  let R := r.reflect.obj F
  let Q := r.reflectedLabelFiber q
  let c : R ⟶ Q := r.zeroFiberComparison p q hq
  let u : F ⟶ R.val := r.adjunction.unit.app F
  let v : F ⟶ Q.val := r.zeroFiberUnit p q hq
  have hc : u ≫ c = v := r.zeroFiberComparison_fac p q hq
  obtain ⟨j, hj⟩ := (r.zeroFiberHomEquiv p q hq R).surjective u
  have hj' : v ≫ j = u := (r.zeroFiberHomEquiv_apply p q hq R j).symm.trans hj
  let cr : R.val ⟶ Q.val := c
  let jr : Q.val ⟶ R.val := j
  have hcr : u ≫ cr = v := hc
  have hjr : v ≫ jr = u := hj'
  have hcj : c ≫ j = 𝟙 R := by
    apply r.unit_hom_ext F R
    change u ≫ (cr ≫ jr) = u ≫ 𝟙 R.val
    calc
      _ = (u ≫ cr) ≫ jr := (Category.assoc u cr jr).symm
      _ = v ≫ jr := congrArg (fun k : F ⟶ Q.val => k ≫ jr) hcr
      _ = u := hjr
      _ = _ := (Category.comp_id u).symm
  have hjc : j ≫ c = 𝟙 Q := by
    apply r.zeroFiberUnit_hom_ext p q hq Q
    change v ≫ (jr ≫ cr) = v ≫ 𝟙 Q.val
    calc
      _ = (v ≫ jr) ≫ cr := (Category.assoc v jr cr).symm
      _ = u ≫ cr := congrArg (fun k : F ⟶ R.val => k ≫ cr) hjr
      _ = v := hcr
      _ = _ := (Category.comp_id v).symm
  exact ⟨⟨j, hcj, hjc⟩⟩

end Thomason.Construction.FiniteReflectionInput

end

section

/-! # The canonical reflection / one-fibre comparison is an isomorphism -/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n) {X : StrictOmegaCategory.{0}}
  (p : X ⟶ StrictPoset.category (Fin 2))
  (q : (r.reflect.obj X).val ⟶ StrictPoset.category (Fin 2))
  (hq : r.adjunction.unit.app X ≫ q = p)

theorem oneFiberUnit_hom_ext (D : Truncated (n + 1))
    {f g : r.reflectedOneLabelFiber q ⟶ D}
    (he : r.oneFiberUnit p q hq ≫ f = r.oneFiberUnit p q hq ≫ g) : f = g :=
  (r.oneFiberHomEquiv p q hq D).injective
    ((r.oneFiberHomEquiv_apply p q hq D f).trans
      (he.trans (r.oneFiberHomEquiv_apply p q hq D g).symm))

/-- The canonical map from the reflected original fibre to the reflected label's fibre. -/
noncomputable def oneFiberComparison :
    r.reflect.obj (labelFiber p 1) ⟶ r.reflectedOneLabelFiber q :=
  (r.adjunction.homEquiv (labelFiber p 1) (r.reflectedOneLabelFiber q)).symm
    (r.oneFiberUnit p q hq)

/-- Compatibility on every original one-fibre cell. -/
theorem oneFiberComparison_fac :
    r.adjunction.unit.app (labelFiber p 1) ≫ r.oneFiberComparison p q hq =
      r.oneFiberUnit p q hq :=
  (r.adjunction.homEquiv_apply (labelFiber p 1) (r.reflectedOneLabelFiber q) _).symm.trans
    ((r.adjunction.homEquiv (labelFiber p 1) (r.reflectedOneLabelFiber q)).apply_symm_apply _)

/-- The initial-cone bijection identifies the two reflection universal properties. -/
theorem oneFiberComparison_isIso : IsIso (r.oneFiberComparison p q hq) := by
  let F := labelFiber p 1
  let R := r.reflect.obj F
  let Q := r.reflectedOneLabelFiber q
  let c : R ⟶ Q := r.oneFiberComparison p q hq
  let u : F ⟶ R.val := r.adjunction.unit.app F
  let v : F ⟶ Q.val := r.oneFiberUnit p q hq
  have hc : u ≫ c = v := r.oneFiberComparison_fac p q hq
  obtain ⟨j, hj⟩ := (r.oneFiberHomEquiv p q hq R).surjective u
  have hj' : v ≫ j = u := (r.oneFiberHomEquiv_apply p q hq R j).symm.trans hj
  let cr : R.val ⟶ Q.val := c
  let jr : Q.val ⟶ R.val := j
  have hcr : u ≫ cr = v := hc
  have hjr : v ≫ jr = u := hj'
  have hcj : c ≫ j = 𝟙 R := by
    apply r.unit_hom_ext F R
    change u ≫ (cr ≫ jr) = u ≫ 𝟙 R.val
    calc
      _ = (u ≫ cr) ≫ jr := (Category.assoc u cr jr).symm
      _ = v ≫ jr := congrArg (fun k : F ⟶ Q.val => k ≫ jr) hcr
      _ = u := hjr
      _ = _ := (Category.comp_id u).symm
  have hjc : j ≫ c = 𝟙 Q := by
    apply r.oneFiberUnit_hom_ext p q hq Q
    change v ≫ (jr ≫ cr) = v ≫ 𝟙 Q.val
    calc
      _ = (v ≫ jr) ≫ cr := (Category.assoc v jr cr).symm
      _ = u ≫ cr := congrArg (fun k : F ⟶ R.val => k ≫ cr) hjr
      _ = v := hcr
      _ = _ := (Category.comp_id v).symm
  exact ⟨⟨j, hcj, hjc⟩⟩

end Thomason.Construction.FiniteReflectionInput

end

section

/-! # The simplex colimit of a full sieve fibre

The explicit binary labels give the original oriental diagram in the slice.
Its zero fibre is a colimit by the constructed terminal-cone adjunction.
-/

namespace Thomason.Construction.SieveSimplex

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory
open NormalizedSimplexIdentities

variable {P : Type} [PartialOrder P] (A : Set P) (hA : IsLowerSet A)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The binary labels of all simplices form a natural transformation. -/
noncomputable def labels :
    (CostructuredArrow.proj SSet.stdSimplex (nerve P) ⋙ h.cosimplicial) ⟶
      (Functor.const _).obj (StrictPoset.category (Fin 2)) where
  app s := label A hA (simplexOrder (SSet.yonedaEquiv s.hom)) h
  naturality s t a := by
    change h.map a.left.toOrderHom ≫
      label A hA (simplexOrder (SSet.yonedaEquiv t.hom)) h = _
    rw [label_precomp, ← simplexOrder_precomp, CostructuredArrow.w a]
    rfl

/-- The labelled diagram has the original orientals as underlying objects. -/
noncomputable abbrev diagram :
    CostructuredArrow SSet.stdSimplex (nerve P) ⥤ Over (StrictPoset.category (Fin 2)) :=
  Over.lift _ (labels A hA h)

/-- The colimit point is the original categorification with its membership label. -/
noncomputable abbrev cocone : Cocone (diagram A hA h) where
  pt := Over.mk (h.membershipLabel A hA)
  ι :=
    { app := fun s => Over.homMk (h.simplexLeg s.hom) (h.membership_simplex_label A hA s.hom)
      naturality := by
        intro s t a
        apply Over.OverMorphism.ext
        exact (h.simplexCocone (nerve P)).ι.naturality a }

/-- Forgetting the labels recovers exactly the original simplex colimit. -/
noncomputable def coconeIsColimit : IsColimit (cocone A hA h) := by
  apply isColimitOfReflects (Over.forget (StrictPoset.category (Fin 2)))
  exact h.simplexCocone_isColimit (nerve P)

/-- Its full zero fibre is therefore the colimit of the full simplex fibres. -/
noncomputable abbrev fiberCocone : Cocone (diagram A hA h ⋙ labelFiberFunctor (Fin 2) 0) :=
  (labelFiberFunctor (Fin 2) 0).mapCocone (cocone A hA h)

/-- This uses the proved adjunction, with no published fibre-colimit input. -/
noncomputable def fiberCoconeIsColimit : IsColimit (fiberCocone A hA h) := by
  have := TerminalCone.zeroFiber_preservesColimits
  exact isColimitOfPreserves (labelFiberFunctor (Fin 2) 0) (coconeIsColimit A hA h)

/-- The clamping inverses form a cocone on the same full simplex fibres. -/
noncomputable def backCocone : Cocone (diagram A hA h ⋙ labelFiberFunctor (Fin 2) 0) where
  pt := h.categorification.obj (nerve A)
  ι :=
    { app := fun s => back A hA h (simplexOrder (SSet.yonedaEquiv s.hom))
      naturality := by
        intro s t a
        have he := (congrArg (fun z => simplexOrder (SSet.yonedaEquiv z))
          (CostructuredArrow.w a)).symm.trans (simplexOrder_precomp t.hom a.left)
        change _ ≫ back A hA h (simplexOrder (SSet.yonedaEquiv t.hom)) = _
        have hb := back_naturality A hA h
          (simplexOrder (SSet.yonedaEquiv t.hom)) a.left.toOrderHom
        apply Hom.ext
        funext x
        have hx := congrArg (fun f => f.toFun ⟨x.val, he ▸ x.property⟩) hb
        exact hx.trans (back_apply_congr A hA h he.symm _ x rfl) }

/-- Descending the compatible clamping maps gives the inverse of the sieve map. -/
noncomputable def inverse :
    labelFiber (h.membershipLabel A hA) 0 ⟶ h.categorification.obj (nerve A) :=
  (fiberCoconeIsColimit A hA h).desc (backCocone A hA h)

/-- The descended map restricts to the explicit inverse on every simplex fibre. -/
theorem inverse_fac (s : CostructuredArrow SSet.stdSimplex (nerve P)) :
    (fiberCocone A hA h).ι.app s ≫ inverse A hA h =
      back A hA h (simplexOrder (SSet.yonedaEquiv s.hom)) :=
  (fiberCoconeIsColimit A hA h).fac (backCocone A hA h) s

end Thomason.Construction.SieveSimplex

end

end OAI
