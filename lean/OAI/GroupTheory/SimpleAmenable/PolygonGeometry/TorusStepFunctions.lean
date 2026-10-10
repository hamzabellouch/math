import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PlaneStepFunctions

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TorusStepFunctions
open Classical

noncomputable def squareSign {a : ℕ} (l : PlaneCut) (p : GenericSquare a) : Bool :=
  decide (cutForm a l.1 p.val < ordinary l.2)

def HasSquareArrangement {a : ℕ} {K : Type*} (f : GenericSquare a → K) : Prop :=
  ∃ S : Finset PlaneCut, ∀ p q, (∀ l∈S, squareSign l p=squareSign l q) → f p=f q

theorem polygon_hasSquareArrangement {a : ℕ} {U : Set (GenericSquare a)}
    (hU : U ∈ polygonAlgebra a) : HasSquareArrangement (fun p => decide (p∈U)) := by
  refine polygon_induction (P := fun U => HasSquareArrangement (fun p => decide (p∈U)))
    ?_ ?_ ?_ ?_ hU
  · intro j z
    exact ⟨{(j,z)},fun p q h => h _ (Finset.mem_singleton_self _)⟩
  · exact ⟨∅,fun _ _ _ => rfl⟩
  · rintro U V ⟨S,hS⟩ ⟨T,hT⟩
    refine ⟨S∪T,fun p q h => ?_⟩
    have h₁ := decide_eq_decide.mp (hS p q (fun l hl => h l (Finset.mem_union_left T hl)))
    have h₂ := decide_eq_decide.mp (hT p q (fun l hl => h l (Finset.mem_union_right S hl)))
    exact decide_eq_decide.mpr (or_congr h₁ h₂)
  · rintro U ⟨S,hS⟩
    refine ⟨S,fun p q h => ?_⟩
    exact decide_eq_decide.mpr (not_congr (decide_eq_decide.mp (hS p q h)))

theorem squareArrangement_precomp {a : ℕ} {K : Type*} {f : GenericSquare a → K}
    (hf : HasSquareArrangement f) (t : GenericSquare a → GenericSquare a)
    (ht : ∀ l, HasSquareArrangement (fun p => squareSign l (t p))) :
    HasSquareArrangement (f ∘ t) := by
  choose S hS using ht
  obtain ⟨T,hT⟩ := hf
  refine ⟨T.biUnion S,fun p q hpq => hT (t p) (t q) (fun l hl => ?_)⟩
  exact hS l p q (fun k hk => hpq k (Finset.mem_biUnion.mpr ⟨l,hl,hk⟩))

theorem squareArrangement_translate {a : ℕ} {K : Type*} {f : GenericSquare a → K}
    (hf : HasSquareArrangement f) (u : CutRing × CutRing) :
    HasSquareArrangement (fun p => f (translate a u p)) := by
  apply squareArrangement_precomp hf
  intro l
  exact polygon_hasSquareArrangement (polygon_preimage_translate u (halfPlane_mem a l.1 l.2))

noncomputable def squareStepSubmodule (a : ℕ) : Submodule ℤ (GenericSquare a → ℤ) where
  carrier := {f | HasSquareArrangement f}
  zero_mem' := ⟨∅,fun _ _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨S,hS⟩ ⟨T,hT⟩
    exact ⟨S∪T,fun p q h => congrArg₂ (·+·)
      (hS p q (fun l hl => h l (Finset.mem_union_left T hl)))
      (hT p q (fun l hl => h l (Finset.mem_union_right S hl)))⟩
  smul_mem' := by
    rintro c f ⟨S,hS⟩
    exact ⟨S,fun p q hpq => congrArg (c • ·) (hS p q hpq)⟩

noncomputable abbrev SquareStep (a : ℕ) := ↥(squareStepSubmodule a)

namespace SquareStep
variable {a : ℕ}

noncomputable def translate (u : CutRing × CutRing) : SquareStep a →ₗ[ℤ] SquareStep a where
  toFun f := ⟨fun p => f.val (SimpleAmenable.translate a (-u) p),
    squareArrangement_translate f.property (-u)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem translate_apply (u : CutRing × CutRing) (f : SquareStep a) (p : GenericSquare a) :
    (translate u f).val p = f.val (SimpleAmenable.translate a (-u) p) := rfl

@[simp] theorem translate_zero (f : SquareStep a) : translate 0 f=f := by
  apply Subtype.ext
  funext p
  simp

@[simp] theorem translate_add (u v : CutRing × CutRing) (f : SquareStep a) :
    translate (u+v) f=translate u (translate v f) := by
  apply Subtype.ext
  funext p
  simp only [translate_apply,neg_add_rev,SimpleAmenable.translate_add]

noncomputable def representation (a : ℕ) :
    Representation ℤ (Multiplicative (CutRing × CutRing)) (SquareStep a) where
  toFun u := translate u.toAdd
  map_one' := by ext f p; exact congrFun (congrArg Subtype.val (translate_zero f)) p
  map_mul' u v := by ext f p; exact congrFun (congrArg Subtype.val (translate_add u.toAdd v.toAdd f)) p

noncomputable def restrict : PlaneStep a →ₗ[ℤ] SquareStep a where
  toFun f := ⟨fun p => f.val ⟨p.val,p.property.2.2⟩,by
    obtain ⟨S,hS⟩ := PlaneStep.hasArrangement f
    exact ⟨S,fun p q hpq => hS ⟨p.val,p.property.2.2⟩ ⟨q.val,q.property.2.2⟩ hpq⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrict_apply (f : PlaneStep a) (p : GenericSquare a) :
    (restrict f).val p=f.val ⟨p.val,p.property.2.2⟩ := rfl

end SquareStep
end TorusStepFunctions

section SquareZeroExtension

open Classical
namespace SquareStep
variable {a : ℕ}

def InSquare (p : GenericPlane a) : Prop :=
  p.val.1 ∈ Set.Ico (0:ℝ) 1 ∧ p.val.2 ∈ Set.Ico (0:ℝ) 1

noncomputable def squareEdgeCuts : Finset PlaneCut := {(0,0),(0,1),(1,0),(1,1)}

theorem square_signs {p q : GenericPlane a}
    (h : ∀ l∈squareEdgeCuts, planeSign l p=planeSign l q) :
    InSquare p ↔ InSquare q := by
  have hx₀ : p.val.1 < 0 ↔ q.val.1 < 0 := by
    simpa [planeSign,cutForm] using decide_eq_decide.mp
      (h (0,0) (by simp [squareEdgeCuts]))
  have hx₁ : p.val.1 < 1 ↔ q.val.1 < 1 := by
    simpa [planeSign,cutForm] using decide_eq_decide.mp
      (h (0,1) (by simp [squareEdgeCuts]))
  have hy₀ : p.val.2 < 0 ↔ q.val.2 < 0 := by
    simpa [planeSign,cutForm] using decide_eq_decide.mp
      (h (1,0) (by simp [squareEdgeCuts]))
  have hy₁ : p.val.2 < 1 ↔ q.val.2 < 1 := by
    simpa [planeSign,cutForm] using decide_eq_decide.mp
      (h (1,1) (by simp [squareEdgeCuts]))
  have hx₀' := not_congr hx₀
  have hy₀' := not_congr hy₀
  simp only [not_lt] at hx₀' hy₀'
  exact and_congr (and_congr hx₀' hx₁) (and_congr hy₀' hy₁)

noncomputable def extendFun (f : SquareStep a) (p : GenericPlane a) : ℤ :=
  if h : InSquare p then f.val ⟨p.val,h.1,h.2,p.property⟩ else 0

theorem extend_arrangement (f : SquareStep a) : HasPlaneArrangement (extendFun f) := by
  obtain ⟨S,hS⟩ := f.property
  refine ⟨S∪squareEdgeCuts,fun p q hpq => ?_⟩
  have hiff := square_signs (fun l hl => hpq l (Finset.mem_union_right S hl))
  by_cases hp : InSquare p
  · have hq := hiff.mp hp
    simp only [extendFun,dite_eq_left hp,dite_eq_left hq]
    exact hS _ _ (fun l hl => hpq l (Finset.mem_union_left squareEdgeCuts hl))
  · have hq := mt hiff.mpr hp
    simp only [extendFun,dite_eq_right hp,dite_eq_right hq]

theorem extend_compact (f : SquareStep a) : PlaneCompactSupport (extendFun f) := by
  refine ⟨1,fun p hp => ?_⟩
  have hn : ¬ InSquare p := by
    rintro ⟨⟨hx,hx'⟩,⟨hy,hy'⟩⟩
    rw [abs_of_nonneg hx,abs_of_nonneg hy] at hp
    rcases hp with hp|hp <;> linarith
  exact dite_eq_right hn

noncomputable def extend : SquareStep a →ₗ[ℤ] PlaneStep a where
  toFun f := ⟨extendFun f,extend_arrangement f,extend_compact f⟩
  map_add' f g := by
    apply Subtype.ext
    funext p
    by_cases hp : InSquare p <;> simp [extendFun,hp]
    rfl
  map_smul' n f := by
    apply Subtype.ext
    funext p
    by_cases hp : InSquare p <;> simp [extendFun,hp]
    rfl

@[simp] theorem extend_apply (f : SquareStep a) (p : GenericPlane a) :
    (extend f).val p = extendFun f p := rfl

@[simp] theorem restrict_extend (f : SquareStep a) : restrict (extend f)=f := by
  apply Subtype.ext
  funext p
  exact dite_eq_left ⟨p.property.1,p.property.2.1⟩

noncomputable def intPair (n : ℤ × ℤ) : CutRing × CutRing := ((n.1:CutRing),(n.2:CutRing))

@[simp] theorem intPair_zero : intPair (0:ℤ×ℤ)=0 := by ext <;> simp [intPair]
@[simp] theorem intPair_add (n m : ℤ×ℤ) : intPair (n+m)=intPair n+intPair m := by
  ext <;> simp [intPair]
@[simp] theorem intPair_neg (n : ℤ×ℤ) : intPair (-n) = - intPair n := by
  ext <;> simp [intPair]

noncomputable def slice (n : ℤ×ℤ) : PlaneStep a →ₗ[ℤ] SquareStep a :=
  restrict.comp (PlaneStep.translate (-intPair n))

@[simp] theorem slice_apply (n : ℤ×ℤ) (f : PlaneStep a) (p : GenericSquare a) :
    (slice n f).val p=f.val (GenericPlane.shift (intPair n) ⟨p.val,p.property.2.2⟩) := by
  change f.val (GenericPlane.shift (- -intPair n) ⟨p.val,p.property.2.2⟩)=_
  rw [neg_neg]

@[simp] theorem slice_zero (f : PlaneStep a) : slice 0 f=restrict f := by
  apply Subtype.ext
  funext p
  rw [slice_apply]
  rw [intPair_zero]
  exact congrArg f.val (GenericPlane.shift_zero ⟨p.val,p.property.2.2⟩)

end SquareStep
end SquareZeroExtension

end SimpleAmenable
end
end

end OAI
