import Mathlib
import OAI.Geometry.HyperbolicGroups.GraphAction
import OAI.Geometry.HyperbolicGroups.TableSelection
import OAI.Geometry.HyperbolicGroups.SixRows

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate

namespace Path
variable {a b c : Vertex}
def IsCore (p : Path a b) : Prop := ∀ f ∈ p.fields, ∃ e : Edge, f = .inl e
lemma isCore_append (p : Path a b) (q : Path b c) (hp : p.IsCore) (hq : q.IsCore) :
    (p.append q).IsCore := by
  induction p with
  | nil => exact hq
  | cons s p ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hp _ (List.mem_cons_self)
    · exact ih q (fun f hf => hp f (List.mem_cons_of_mem _ hf)) hq f hf
lemma isCore_symm (p : Path a b) (hp : p.IsCore) : p.symm.IsCore := by
  induction p with
  | nil => exact hp
  | cons s p ih =>
    apply isCore_append _ _ (ih (fun f hf => hp f (List.mem_cons_of_mem _ hf)))
    intro f hf
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at hf
    exact hf ▸ hp s.field (List.mem_cons_self)

lemma eval_map {G H L : Type*} [Group G] [Group H] (f : G →* H)
    (l : Field → L) (r : L → G) (p : Path a b) :
    f (p.eval l r) = p.eval l (fun i => f (r i)) := by
  induction p with
  | nil => exact map_one f
  | cons s p ih =>
    simp only [eval,map_mul,ih]
    congr 1
    cases h : s.forward <;> simp [Step.value,h]
end Path

theorem coreRoute_exists (v : CoreGeometry.Vertex) : ∃ p : Path root (.inl v), p.IsCore := by
  rcases v with r | l
  · fin_cases r
    · refine ⟨(.nil _), ?_⟩; simp only [Path.IsCore,Path.fields,List.not_mem_nil,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.cons (coreStep (a := (.inr 2)) (b := (.inl 1)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 2)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.cons (coreStep (a := (.inr 6)) (b := (.inl 3)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.cons (coreStep (a := (.inr 2)) (b := (.inl 4)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 5)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.cons (coreStep (a := (.inr 6)) (b := (.inl 6)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 7)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.cons (coreStep (a := (.inr 2)) (b := (.inl 8)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 9)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.cons (coreStep (a := (.inr 6)) (b := (.inl 10)) (by decide)) (.nil _))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
  · fin_cases l
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 2)) (by decide)) (.cons (coreStep (a := (.inl 2)) (b := (.inr 0)) (by decide)) (.nil _)))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.nil _)), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.nil _)), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 5)) (by decide)) (.cons (coreStep (a := (.inl 5)) (b := (.inr 3)) (by decide)) (.nil _)))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 2)) (by decide)) (.cons (coreStep (a := (.inl 2)) (b := (.inr 4)) (by decide)) (.nil _)))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 5)) (by decide)) (.cons (coreStep (a := (.inl 5)) (b := (.inr 5)) (by decide)) (.nil _)))), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]
    · refine ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.nil _)), ?_⟩; simp only [Path.IsCore,Path.fields,coreStep_field,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,Sum.inl.injEq,exists_eq',and_true,false_implies,implies_true]

def coreRoute (v : CoreGeometry.Vertex) : Path root (.inl v) := (coreRoute_exists v).choose
lemma coreRoute_core (v : CoreGeometry.Vertex) : (coreRoute v).IsCore :=
  (coreRoute_exists v).choose_spec

/-- The oriented source four-letter decoration, including the two given core sides. -/
def squareWord {G L : Type*} [Group G] (l : Field → L) (r : L → G) (τ : TwoPath) : G :=
  (first τ).value l r * (second τ).value l r * r (l (.inr (τ,0))) * r (l (.inr (τ,1)))

lemma squareWord_map {G H L : Type*} [Group G] [Group H] (f : G →* H)
    (l : Field → L) (r : L → G) (τ : TwoPath) :
    f (squareWord l r τ) = squareWord l (fun i => f (r i)) τ := by
  simp only [squareWord,map_mul,Step.value]
  split_ifs <;> simp

end MasterGraph

namespace LetterPresentation
open IncidenceTemplate MasterGraph
variable (n : ℕ)
abbrev Alphabet := SymmetricAlphabet n

def freeLetter (a : Alphabet n) : FreeGroup (Fin (n+1)) :=
  if a.2 then FreeGroup.of a.1 else (FreeGroup.of a.1)⁻¹

def inverseLetter : Alphabet n ≃ Alphabet n where
  toFun a := (a.1,!a.2)
  invFun a := (a.1,!a.2)
  left_inv := by rintro ⟨a,b⟩; cases b <;> rfl
  right_inv := by rintro ⟨a,b⟩; cases b <;> rfl

lemma freeLetter_inv (a : Alphabet n) : freeLetter n (inverseLetter n a) = (freeLetter n a)⁻¹ := by
  rcases a with ⟨i,b⟩
  cases b <;> simp [freeLetter,inverseLetter]

variable (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- The literal source letter relators: all included fans, all included top
occurrences (with all seven fan slots), and every included square/six-letter
row, even rows that do not occur in any master match. -/
inductive Relator : FreeGroup (Fin (n+1)) → Prop
  | fan (l : Field → Alphabet n) (i : Fin 7)
      (present : w (TableModel.row rowSupport l (.inl i)) = true)
      (v : MasterGraph.Vertex) (p : MasterGraph.Path v v)
      (fields : p.fields.toFinset ⊆ rowSupport (.inl i)) : Relator (p.eval l (freeLetter n))
  | top (l : Field → Alphabet n)
      (present : w (TableModel.row rowSupport l (.inr (.inl ()))) = true)
      (fans : ∀ i : Fin 7, w (TableModel.row rowSupport l (.inl i)) = true)
      (v : MasterGraph.Vertex) (p : MasterGraph.Path v v) (core : p.IsCore) :
      Relator (p.eval l (freeLetter n))
  | square (l : Field → Alphabet n) (τ : TwoPath)
      (present : w (TableModel.row rowSupport l (.inr (.inr τ))) = true) :
      Relator (MasterGraph.squareWord l (freeLetter n) τ)
  | six (x : Fin 6 → Alphabet n) (present : d x = true) :
      Relator ((List.ofFn (freeLetter n ∘ x)).prod)

abbrev Group := PresentedGroup (Relator n w d)
instance group : _root_.Group (Group n w d) := instGroupPresentedGroup _

def letter (a : Alphabet n) : Group n w d := PresentedGroup.mk _ (freeLetter n a)

lemma letter_inv (a : Alphabet n) : letter n w d (inverseLetter n a) = (letter n w d a)⁻¹ := by
  simp only [letter,freeLetter_inv,map_inv]

lemma letter_generates : Subgroup.closure (Set.range (letter n w d)) = ⊤ := by
  apply top_unique
  rw [← PresentedGroup.closure_range_of (Relator n w d)]
  apply Subgroup.closure_mono
  rintro _ ⟨i,rfl⟩
  exact ⟨(i,true),rfl⟩

lemma top_relator (a : StarModel.Matches rowSupport w) (v : MasterGraph.Vertex)
    (p : MasterGraph.Path v v) (hp : p.IsCore) : p.eval a.val (letter n w d) = 1 := by
  change p.eval a.val (fun i => PresentedGroup.mk (Relator n w d) (freeLetter n i)) = 1
  rw [← Path.eval_map]
  exact PresentedGroup.one_of_mem (Relator.top a.val (a.property _) (fun i => a.property _) v p hp)

lemma square_relator (a : StarModel.Matches rowSupport w) (τ : TwoPath) :
    MasterGraph.squareWord a.val (letter n w d) τ = 1 := by
  change squareWord a.val (fun i => PresentedGroup.mk (Relator n w d) (freeLetter n i)) τ = 1
  rw [← squareWord_map]
  exact PresentedGroup.one_of_mem (Relator.square a.val τ (a.property _))

lemma six_relator (x : Fin 6 → Alphabet n) (hx : d x = true) :
    (List.ofFn (letter n w d ∘ x)).prod = 1 := by
  have hh := PresentedGroup.one_of_mem (show Relator n w d ((List.ofFn (freeLetter n ∘ x)).prod) from Relator.six x hx)
  simpa only [map_list_prod,List.map_ofFn,Function.comp_def,letter] using hh


def coreValue (a : StarModel.Matches rowSupport w) (v : CoreGeometry.Vertex) : Group n w d :=
  (coreRoute v).eval a.val (letter n w d)

lemma coreValue_path (a : StarModel.Matches rowSupport w) {v z : CoreGeometry.Vertex}
    (p : MasterGraph.Path (.inl v) (.inl z)) (hp : p.IsCore) :
    coreValue n w d a z = coreValue n w d a v * p.eval a.val (letter n w d) := by
  have hh := top_relator n w d a root
    (((coreRoute v).append p).append (coreRoute z).symm)
    (Path.isCore_append _ _ (Path.isCore_append _ _ (coreRoute_core v) hp)
      (Path.isCore_symm _ (coreRoute_core z)))
  simp only [Path.eval_append,Path.eval_symm] at hh
  exact (eq_of_mul_inv_eq_one hh).symm

def vertexValue (a : StarModel.Matches rowSupport w) : MasterGraph.Vertex → Group n w d
  | .inl v => coreValue n w d a v
  | .inr τ => coreValue n w d a (right τ) * letter n w d (a.val (.inr (τ,0)))

lemma coreValue_step (a : StarModel.Matches rowSupport w)
    {v z : CoreGeometry.Vertex} (s : Step (.inl v) (.inl z))
    (hs : ∃ e : Edge, s.field = .inl e) :
    coreValue n w d a z = coreValue n w d a v * s.value a.val (letter n w d) := by
  have hh := coreValue_path n w d a (.cons s (.nil _)) (by
    intro f hf
    simp only [Path.fields,List.mem_cons,List.not_mem_nil,or_false] at hf
    exact hf ▸ hs)
  simpa only [Path.eval,mul_one] using hh

/-- Every master match has a genuine group-valued potential in the literal
letter presentation. Only its actual top and square relators are used. -/
def potential (a : StarModel.Matches rowSupport w) : Potential a.val (letter n w d) where
  val := vertexValue n w d a
  root_one := top_relator n w d a root (coreRoute (.inl 0)) (coreRoute_core _)
  edge f := by
    rcases f with e | ⟨τ,j⟩
    · exact coreValue_step n w d a (Step.pos (.inl e)) ⟨e,rfl⟩
    · fin_cases j
      · rfl
      · have h₁ := coreValue_step n w d a (first τ) ⟨_,first_field τ⟩
        have h₂ := coreValue_step n w d a (second τ) ⟨_,second_field τ⟩
        have hh := square_relator n w d a τ
        change coreValue n w d a (left τ) =
          (coreValue n w d a (right τ) * letter n w d (a.val (.inr (τ,0)))) *
            letter n w d (a.val (.inr (τ,1)))
        rw [h₂,h₁]
        simp only [mul_assoc]
        have hh' : (first τ).value a.val (letter n w d) *
            ((second τ).value a.val (letter n w d) *
              (letter n w d (a.val (.inr (τ,0))) * letter n w d (a.val (.inr (τ,1))))) = 1 := by
          simpa only [squareWord,mul_assoc] using hh
        rw [hh',mul_one]

lemma six_tail_relator (u : Alphabet n) (x : SixTable.Rows d u) :
    (List.ofFn (letter n w d ∘ SixTable.row d u x)).prod = (letter n w d u)⁻¹ := by
  have hh := six_relator n w d x.val x.property.2
  rw [List.ofFn_succ,List.prod_cons] at hh
  have hu : (letter n w d ∘ x.val) 0 = letter n w d u := congrArg _ x.property.1
  rw [hu] at hh
  exact eq_inv_of_mul_eq_one_right hh

end LetterPresentation
end HyperbolicObstruction
end
end

section

end
end

end OAI
