import Mathlib
import OAI.Geometry.HyperbolicGroups.Template

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate
abbrev Vertex := CoreGeometry.Vertex ⊕ TwoPath

def left (τ : TwoPath) : CoreGeometry.Vertex :=
  if τ.val.1.val.1 = τ.val.2.val.1 then .inr τ.val.1.val.2 else .inl τ.val.1.val.1
def middle (τ : TwoPath) : CoreGeometry.Vertex :=
  if τ.val.1.val.1 = τ.val.2.val.1 then .inl τ.val.1.val.1 else .inr τ.val.1.val.2
def right (τ : TwoPath) : CoreGeometry.Vertex :=
  if τ.val.1.val.1 = τ.val.2.val.1 then .inr τ.val.2.val.2 else .inl τ.val.2.val.1

def source : Field → Vertex
  | .inl e => .inl (.inl e.val.1)
  | .inr (τ, j) => if j = 0 then .inl (right τ) else .inr τ

def target : Field → Vertex
  | .inl e => .inl (.inr e.val.2)
  | .inr (τ, j) => if j = 0 then .inr τ else .inl (left τ)

/-- An oriented traversal of one of the fixed master fields. -/
structure Step (a b : Vertex) where
  field : Field
  forward : Bool
  endpoints : if forward then source field = a ∧ target field = b
    else target field = a ∧ source field = b

namespace Step

def pos (f : Field) : Step (source f) (target f) := ⟨f, true, by simp⟩
def neg (f : Field) : Step (target f) (source f) := ⟨f, false, by simp⟩
def symm {a b : Vertex} (s : Step a b) : Step b a :=
  ⟨s.field, !s.forward, by
    have hs := s.endpoints
    cases h : s.forward <;> simp only [h, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at hs ⊢ <;> exact hs.symm⟩

variable {a b : Vertex}
lemma endpoints_pos (s : Step a b) (h : s.forward = true) : source s.field = a ∧ target s.field = b := by
  simpa only [h, Bool.true_eq, ↓reduceIte] using s.endpoints
lemma endpoints_neg (s : Step a b) (h : s.forward = false) : target s.field = a ∧ source s.field = b := by
  simpa only [h, Bool.false_eq_true, ↓reduceIte] using s.endpoints
end Step

/-- Finite paths, with edges carrying their actual named fields. -/
inductive Path : Vertex → Vertex → Type
  | nil (a : Vertex) : Path a a
  | cons {a b c : Vertex} (s : Step a b) (p : Path b c) : Path a c

namespace Path
variable {a b c : Vertex}
def length : {a b : Vertex} → Path a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ p => p.length + 1

def fields : {a b : Vertex} → Path a b → List Field
  | _, _, .nil _ => []
  | _, _, .cons s p => s.field :: p.fields

lemma fields_length (p : Path a b) : p.fields.length = p.length := by
  induction p with
  | nil => rfl
  | cons s p ih => simp only [fields, List.length_cons, length, ih]

def append : {a b c : Vertex} → Path a b → Path b c → Path a c
  | _, _, _, .nil _, q => q
  | _, _, _, .cons s p, q => .cons s (append p q)

def symm : {a b : Vertex} → Path a b → Path b a
  | _, _, .nil a => .nil a
  | _, _, .cons s p => p.symm.append (.cons s.symm (.nil _))
end Path

/-- Core adjacency corresponds to the unique actual core field. -/
def coreStep {a b : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b) : Step (.inl a) (.inl b) := by
  cases a with
  | inl r =>
    cases b with
    | inl r' => exact h.elim
    | inr l => exact Step.pos (.inl ⟨(r,l), h⟩)
  | inr l =>
    cases b with
    | inl r => exact Step.neg (.inl ⟨(r,l), h⟩)
    | inr l' => exact h.elim

/-- The unoriented field of a core adjacency. -/
def coreEdge {a b : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b) : Edge := by
  cases a with
  | inl r =>
    cases b with
    | inl _ => exact h.elim
    | inr l => exact ⟨(r,l), h⟩
  | inr l =>
    cases b with
    | inl r => exact ⟨(r,l), h⟩
    | inr _ => exact h.elim

lemma coreStep_field {a b : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b) :
    (coreStep h).field = .inl (coreEdge h) := by
  cases a <;> cases b <;> first | exact h.elim | rfl

lemma core_adj_ne {a b : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b) : a ≠ b := by
  cases a <;> cases b <;> first | exact h.elim | exact Sum.inl_ne_inr | exact Sum.inr_ne_inl

lemma coreEdge_eq {a b c d : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b)
    (h' : CoreGeometry.Adjacent c d) (he : coreEdge h = coreEdge h') :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    first | exact h.elim | exact h'.elim |
      (have hv := congrArg Subtype.val he;
        simp only [coreEdge, Prod.mk.injEq] at hv; aesop)

lemma coreEdge_fan {a b : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b) (i : Fin 7) :
    coreEdge h ∈ fan i ↔ CoreGeometry.InFan i a b := by
  cases a <;> cases b <;> first | exact h.elim |
    (unfold fan; rw [Finset.mem_filter]; simp [coreEdge, isLoose, CoreGeometry.InFan])

lemma coreEdge_ne_consecutive {a b c : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b)
    (h' : CoreGeometry.Adjacent b c) (hne : a ≠ c) : coreEdge h ≠ coreEdge h' := by
  intro he
  rcases coreEdge_eq h h' he with hh | hh
  · exact core_adj_ne h hh.1
  · exact hne hh.1

lemma coreEdge_ne_third {a b c d : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b)
    (h' : CoreGeometry.Adjacent b c) (h'' : CoreGeometry.Adjacent c d) (hne : a ≠ c) :
    coreEdge h ≠ coreEdge h'' := by
  intro he
  rcases coreEdge_eq h h'' he with hh | hh
  · exact hne hh.1
  · exact core_adj_ne h' hh.2

lemma corePath_three_nodup {a b c d : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b)
    (h' : CoreGeometry.Adjacent b c) (h'' : CoreGeometry.Adjacent c d)
    (hac : a ≠ c) (hbd : b ≠ d) :
    [(.inl (coreEdge h) : Field), .inl (coreEdge h'), .inl (coreEdge h'')].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, Sum.inl.injEq,
    not_or, List.nodup_nil, and_true, not_false_eq_true]
  exact ⟨⟨coreEdge_ne_consecutive h h' hac, coreEdge_ne_third h h' h'' hac⟩,
    coreEdge_ne_consecutive h' h'' hbd⟩

/-- The actual two core sides of a decoration. -/
def first (τ : TwoPath) : Step (.inl (left τ)) (.inl (middle τ)) :=
  ⟨.inl τ.val.1, if τ.val.1.val.1 = τ.val.2.val.1 then false else true, by
    by_cases h : τ.val.1.val.1 = τ.val.2.val.1 <;>
      simp [h, source, target, left, middle]⟩

def second (τ : TwoPath) : Step (.inl (middle τ)) (.inl (right τ)) :=
  ⟨.inl τ.val.2, if τ.val.1.val.1 = τ.val.2.val.1 then true else false, by
    by_cases h : τ.val.1.val.1 = τ.val.2.val.1
    · simp [h, source, target, middle, right]
    · have he := τ.property.2.resolve_left h
      simp [h, he, source, target, middle, right]⟩

lemma first_field (τ : TwoPath) : (first τ).field = .inl τ.val.1 := rfl
lemma second_field (τ : TwoPath) : (second τ).field = .inl τ.val.2 := rfl

/-- A fixed anchor and genuine paths in the finite literal core graph. -/
def root : Vertex := .inl (.inl 0)

theorem corePath_nonempty (v : CoreGeometry.Vertex) : Nonempty (Path root (.inl v)) := by
  rcases v with r | l
  · fin_cases r
    · exact ⟨(.nil _)⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.cons (coreStep (a := (.inr 2)) (b := (.inl 1)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 2)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.cons (coreStep (a := (.inr 6)) (b := (.inl 3)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.cons (coreStep (a := (.inr 2)) (b := (.inl 4)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 5)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.cons (coreStep (a := (.inr 6)) (b := (.inl 6)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 7)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.cons (coreStep (a := (.inr 2)) (b := (.inl 8)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 9)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.cons (coreStep (a := (.inr 6)) (b := (.inl 10)) (by decide)) (.nil _)))⟩
  · fin_cases l
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 2)) (by decide)) (.cons (coreStep (a := (.inl 2)) (b := (.inr 0)) (by decide)) (.nil _))))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.nil _))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.nil _))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 5)) (by decide)) (.cons (coreStep (a := (.inl 5)) (b := (.inr 3)) (by decide)) (.nil _))))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 2)) (by decide)) (.cons (coreStep (a := (.inl 2)) (b := (.inr 4)) (by decide)) (.nil _))))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 5)) (by decide)) (.cons (coreStep (a := (.inl 5)) (b := (.inr 5)) (by decide)) (.nil _))))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.nil _))⟩


def corePath (v : CoreGeometry.Vertex) : Path root (.inl v) := Classical.choice (corePath_nonempty v)

def route (v : Vertex) : Path root v :=
  match v with
  | .inl v => corePath v
  | .inr τ => (corePath (right τ)).append (.cons (Step.pos (.inr (τ,0))) (.nil _))

lemma admissible_down (I J : Finset Field) (hIJ : I ⊆ J) (hJ : Admissible J) : Admissible I := by
  rcases hJ with ⟨hzero, hcard, hfan⟩ | ⟨τ, hτ, hc⟩
  · left
    refine ⟨Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_), ?_, ?_⟩
    · have hh := Finset.toRight_subset_toRight hIJ hx
      rw [hzero] at hh
      exact Finset.notMem_empty _ hh
    · exact (Finset.card_le_card (Finset.toLeft_subset_toLeft hIJ)).trans hcard
    · intro i
      exact (Finset.card_le_card (Finset.inter_subset_inter (Finset.toLeft_subset_toLeft hIJ)
        (Finset.Subset.refl _))).trans (hfan i)
  · exact Or.inr ⟨τ, hIJ.trans hτ, (Finset.card_le_card hIJ).trans hc⟩

lemma admissible_core_triple (e f g : Edge)
    (hq : ∀ i, ¬(e ∈ fan i ∧ f ∈ fan i ∧ g ∈ fan i)) :
    Admissible {(.inl e : Field), .inl f, .inl g} := by
  left
  refine ⟨by ext x; simp, ?_⟩
  have hleft : ({(.inl e : Field), .inl f, .inl g} : Finset Field).toLeft = {e,f,g} := by
    ext x
    simp
  rw [hleft]
  refine ⟨Finset.card_le_three, fun i => ?_⟩
  unfold fanCount
  have hpair (a b : Edge) : ({a,b} : Finset Edge).card ≤ 2 := Finset.card_le_two
  by_cases he : e ∈ fan i
  · by_cases hf : f ∈ fan i
    · have hg : g ∉ fan i := fun hg => hq i ⟨he, hf, hg⟩
      apply (Finset.card_le_card (show {e,f,g} ∩ fan i ⊆ {e,f} from ?_)).trans (hpair e f)
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hg (h ▸ hx.2)).elim
    · apply (Finset.card_le_card (show {e,f,g} ∩ fan i ⊆ {e,g} from ?_)).trans (hpair e g)
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx.1 with h | h | h
      · exact Or.inl h
      · exact (hf (h ▸ hx.2)).elim
      · exact Or.inr h
  · apply (Finset.card_le_card (show {e,f,g} ∩ fan i ⊆ {f,g} from ?_)).trans (hpair f g)
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx.1 with h | h | h
    · exact (he (h ▸ hx.2)).elim
    · exact Or.inl h
    · exact Or.inr h

lemma corePath_three_admissible {a b c d : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b)
    (h' : CoreGeometry.Adjacent b c) (h'' : CoreGeometry.Adjacent c d)
    (hq : CoreGeometry.ThreeQuota a b c d) :
    Admissible [(.inl (coreEdge h) : Field), .inl (coreEdge h'), .inl (coreEdge h'')].toFinset := by
  simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
  apply admissible_core_triple
  intro i hi
  exact hq i ⟨(coreEdge_fan h i).mp hi.1, (coreEdge_fan h' i).mp hi.2.1,
    (coreEdge_fan h'' i).mp hi.2.2⟩

end MasterGraph
end HyperbolicObstruction
end
end

section

end
end

end OAI
