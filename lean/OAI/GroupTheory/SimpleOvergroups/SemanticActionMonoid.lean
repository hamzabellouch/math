import Mathlib
import OAI.GroupTheory.SimpleOvergroups.ActionMonoid
import OAI.GroupTheory.SimpleOvergroups.NamedActions

namespace OAI


noncomputable section
open scoped Classical
namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding NamedAction
namespace SemanticActionMonoid

variable {G X V Y K L : Type*} [Group V] [MulAction V Y] {m : ℕ}
  {N : Operations G X} {C : ActionCalculus V Y K L m} (I : Interpretation N C)

abbrev groupValue (g : G) : V := (I.group g).val
abbrev pointValue (x : X) : Y := (I.point x).val

def letter : Letter G X → SourceActionMonoid.Generator V Y
  | .inl g => .grp (groupValue I g)
  | .inr (.inl x) => .pre (pointValue I x)
  | .inr (.inr (some x)) => .delete (pointValue I x)
  | .inr (.inr none) => .zero

def wordMap : FreeMonoid (Letter G X) →* SourceActionMonoid.M V Y :=
  (PresentedMonoid.mk (SourceActionMonoid.Relation V Y)).comp
    (FreeMonoid.lift (fun a => FreeMonoid.of (letter I a)))

def formValue : Form G X → SourceActionMonoid.Algorithm.Form (V:=V) (Z:=Y) :=
  Operations.formKey (groupValue I) (pointValue I)

 theorem formKey_injective {G X : Type*} {kg : G → K} {kx : X → L}
    (hg : Function.Injective kg) (hx : Function.Injective kx) :
    Function.Injective (Operations.formKey kg kx) := by
  apply Option.map_injective
  intro a b h
  apply Prod.ext
  · exact (List.map_injective_iff.mpr hx) (congrArg Prod.fst h)
  · apply Prod.ext
    · exact hg (congrArg (fun p => p.2.1) h)
    · exact (List.map_injective_iff.mpr hx) (congrArg (fun p => p.2.2) h)

 theorem formKey_comp (f : Form G X) :
    Operations.formKey C.group.key C.point.key (formValue I f) =
      Operations.formKey I.gkey I.xkey f := by
  cases f with
  | none => rfl
  | some p => simp only [Operations.formKey,formValue,Option.map_some,List.map_map]; rfl

variable [DecidableEq L]

 theorem formValue_step (hx : Function.Injective C.point.key)
    (a : Letter G X) (f : Form G X) :
    formValue I (N.totalStep I.xkey a f) =
      SourceActionMonoid.Algorithm.step (letter I a) (formValue I f) := by
  have hone : groupValue I N.one = 1 := congrArg WithBound.val I.one
  have hmul g h : groupValue I (N.mul g h) = groupValue I g * groupValue I h :=
    congrArg WithBound.val (I.mul g h)
  have hinv g : groupValue I (N.inv g) = (groupValue I g)⁻¹ :=
    congrArg WithBound.val (I.inv g)
  have hact g x : pointValue I (N.act g x) = groupValue I g • pointValue I x :=
    congrArg WithBound.val (I.act g x)
  have hkey x y : I.xkey x = I.xkey y ↔ pointValue I x = pointValue I y := hx.eq_iff
  cases f with
  | none => cases a <;> rfl
  | some p =>
    rcases p with ⟨l,g,r⟩
    rcases a with h | (x | y)
    · cases l <;> simp [Operations.totalStep,Operations.plan,formValue,Operations.formKey,
        letter,SourceActionMonoid.Algorithm.step,hmul,hact]
    · rfl
    · cases y with
      | none => rfl
      | some y =>
        cases l with
        | nil => simp [Operations.totalStep,Operations.plan,formValue,Operations.formKey,
            letter,SourceActionMonoid.Algorithm.step,hone,hact,hinv]
        | cons x l =>
          by_cases h : I.xkey y = I.xkey x
          · simp [Operations.totalStep,Operations.plan,formValue,Operations.formKey,
              letter,SourceActionMonoid.Algorithm.step,h,(hkey y x).mp h]
          · simp [Operations.totalStep,Operations.plan,formValue,Operations.formKey,
              letter,SourceActionMonoid.Algorithm.step,h,mt (hkey y x).mpr h]

 theorem formValue_normalize (hx : Function.Injective C.point.key) (w : List (Letter G X)) :
    formValue I (N.totalNormalize I.xkey w) = SourceActionMonoid.Algorithm.normalize (w.map (letter I)) := by
  induction w with
  | nil =>
    change some ([],groupValue I N.one,[]) = some ([],1,[])
    rw [show groupValue I N.one = 1 from congrArg WithBound.val I.one]
  | cons a w ih =>
    change formValue I (N.totalStep I.xkey a (N.totalNormalize I.xkey w)) = _
    rw [formValue_step I hx,ih]
    rfl

omit [DecidableEq L] in
 theorem wordMap_ofList (w : List (Letter G X)) :
    wordMap I (FreeMonoid.ofList w) =
      PresentedMonoid.mk (SourceActionMonoid.Relation V Y) (FreeMonoid.ofList (w.map (letter I))) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [FreeMonoid.ofList_cons,map_mul,List.map_cons,ih]; rfl

 theorem totalTest_eq_iff (hg : Function.Injective C.group.key) (hx : Function.Injective C.point.key)
    (u v : List (Letter G X)) :
    N.totalTest I.gkey I.xkey u = N.totalTest I.gkey I.xkey v ↔
      wordMap I (FreeMonoid.ofList u) = wordMap I (FreeMonoid.ofList v) := by
  change Operations.formKey I.gkey I.xkey _ = Operations.formKey I.gkey I.xkey _ ↔ _
  rw [← formKey_comp I,← formKey_comp I,(formKey_injective hg hx).eq_iff,
    formValue_normalize I hx,formValue_normalize I hx,wordMap_ofList,wordMap_ofList]
  exact (SourceActionMonoid.Algorithm.word_eq_iff _ _).symm

omit [DecidableEq L] in
 theorem wordMap_surjective (hg : Function.Surjective (groupValue I))
    (hx : Function.Surjective (pointValue I)) : Function.Surjective (wordMap I) := by
  have hl : Function.Surjective (letter I) := by
    intro a
    cases a with
    | grp g => obtain ⟨a,rfl⟩ := hg g; exact ⟨.inl a,rfl⟩
    | pre y => obtain ⟨a,rfl⟩ := hx y; exact ⟨.inr (.inl a),rfl⟩
    | delete y => obtain ⟨a,rfl⟩ := hx y; exact ⟨.inr (.inr (some a)),rfl⟩
    | zero => exact ⟨.inr (.inr none),rfl⟩
  intro z
  obtain ⟨v,rfl⟩ := PresentedMonoid.surjective_mk z
  obtain ⟨w,hw⟩ := (List.map_surjective_iff.mpr hl) v.toList
  refine ⟨FreeMonoid.ofList w,?_⟩
  rw [wordMap_ofList,hw,FreeMonoid.ofList_toList]

end SemanticActionMonoid
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
