import Mathlib
import OAI.Combinatorics.KMedian.PCP.Queries

namespace OAI

section Inline_PCPAlphabetReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]

structure BinaryCSP (V E A : Type) where
  left : E → V
  right : E → V
  allowed : E → Finset (A × A)

namespace BinaryCSP
variable {A : Type} [DecidableEq A] (C : BinaryCSP V E A)
def Satisfies (a : V → A) : Prop := ∀ e, (a (C.left e), a (C.right e)) ∈ C.allowed e
noncomputable def rejection (a : V → A) : ℝ :=
  testRate (fun e => (a (C.left e), a (C.right e)) ∉ C.allowed e)
end BinaryCSP

structure FourCSP (P T : Type) where
  query : T → FourQuery P
namespace FourCSP
variable {P T : Type} [Fintype T] (C : FourCSP P T)
def Satisfies (a : P → Bit) : Prop := ∀ t, ¬ (C.query t).Rejects a
noncomputable def rejection (a : P → Bit) : ℝ := testRate (fun t => (C.query t).Rejects a)
end FourCSP

namespace FourQuery
variable {P Q : Type}
def map (q : FourQuery P) (f : P → Q) : FourQuery Q := ⟨f ∘ q.address, q.accept⟩
@[simp] theorem map_rejects (q : FourQuery P) (f : P → Q) (a : Q → Bit) :
    (q.map f).Rejects a ↔ q.Rejects (a ∘ f) := Iff.rfl
end FourQuery

theorem testRate_eq_zero_iff {S : Type} [Fintype S] (p : S → Prop) :
    testRate p = 0 ↔ ∀ s, ¬ p s := by
  classical
  unfold testRate
  rw [Finset.expect_eq_zero_iff_of_nonneg (by intro s _; split_ifs <;> norm_num)]
  simp

namespace AlphabetReduction
variable (K)
abbrev Relations := Finset (BitVector K × BitVector K)
abbrev UniversalPad := (R : Relations K) → LocalRelation.Pad (R : LocalRelation.Relation K)
abbrev EdgeSample := Fin 6 × UniversalPad K

variable {K}
variable (C : BinaryCSP V E (BitVector K))
abbrev relation (e : E) : LocalRelation.Relation K := (C.allowed e : Set _)
abbrev Interior (e : E) := BitVector (LocalRelation.Vars (relation C e)) ⊕
  BitVector (LocalRelation.Vars (relation C e) × LocalRelation.Vars (relation C e))
abbrev Position := (V × BitVector K) ⊕ ((e : E) × Interior C e)
abbrev Test := E × EdgeSample K

def localMap (e : E) : LocalRelation.LocalPosition (relation C e) → Position C
  | .inl x => .inr ⟨e,.inl x⟩
  | .inr (.inl x) => .inr ⟨e,.inr x⟩
  | .inr (.inr (b,x)) => .inl (if b = 0 then C.left e else C.right e, x)

def reduced : FourCSP (Position C) (Test (E := E) (K := K)) where
  query t := (LocalRelation.query (relation C t.1) t.2.1
    (t.2.2 (C.allowed t.1) t.2.1)).map (localMap C t.1)

def vertexTable (a : Position C → Bit) (v : V) : BitVector K → Bit :=
  fun x => a (.inl (v,x))
def firstTable (a : Position C → Bit) (e : E) :
    BitVector (LocalRelation.Vars (relation C e)) → Bit := fun x => a (.inr ⟨e,.inl x⟩)
def secondTable (a : Position C → Bit) (e : E) :
    BitVector (LocalRelation.Vars (relation C e) × LocalRelation.Vars (relation C e)) → Bit :=
  fun x => a (.inr ⟨e,.inr x⟩)

omit [Fintype V] [Fintype E] [Fintype K] [DecidableEq K] in
@[simp] theorem restriction (a : Position C → Bit) (e : E) :
    a ∘ localMap C e = LocalRelation.assignment (relation C e)
      (firstTable C a e) (secondTable C a e)
      (vertexTable C a (C.left e)) (vertexTable C a (C.right e)) := by
  funext p
  rcases p with x | x
  · rfl
  rcases x with x | ⟨b,x⟩
  · rfl
  by_cases hb : b = 0 <;> simp [localMap, LocalRelation.assignment, vertexTable, hb]

omit [Fintype V] [Fintype E] in
theorem edge_rate (a : Position C → Bit) (e : E) :
    testRate (fun s : EdgeSample K => ((reduced C).query (e,s)).Rejects a) =
      LocalRelation.rejectionWeight (relation C e) (firstTable C a e) (secondTable C a e)
        (vertexTable C a (C.left e)) (vertexTable C a (C.right e)) / 6 := by
  classical
  let R := relation C e
  let p := fun (i : Fin 6) (s : LocalRelation.Sample R i) =>
    (LocalRelation.query R i s).Rejects (a ∘ localMap C e)
  have hm (i : Fin 6) :
      testRate (fun s : UniversalPad K => p i (s (C.allowed e) i)) =
      testRate (fun s : LocalRelation.Pad R => p i (s i)) :=
    testRate_pi_eval (fun R : Relations K => LocalRelation.Pad (R : LocalRelation.Relation K))
      (C.allowed e) (fun s : LocalRelation.Pad R => p i (s i))
  change testRate (fun s : Fin 6 × UniversalPad K => p s.1 (s.2 (C.allowed e) s.1)) = _
  rw [testRate_prod (S := Fin 6) (T := UniversalPad K)
    (fun (i : Fin 6) (s : UniversalPad K) => p i (s (C.allowed e) i))]
  simp_rw [hm]
  rw [← testRate_prod (S := Fin 6) (T := LocalRelation.Pad R)
    (fun (i : Fin 6) (s : LocalRelation.Pad R) => p i (s i))]
  change testRate (fun s => (LocalRelation.packed R s).Rejects (a ∘ localMap C e)) = _
  rw [restriction]
  exact LocalRelation.packed_rate _ _ _ _ _

noncomputable def decoded (a : Position C → Bit) : V → BitVector K :=
  fun v => nearestLabel (vertexTable C a v)

omit [Fintype V] in
theorem sound (a : Position C → Bit) :
    C.rejection (decoded C a) / 96 ≤ (reduced C).rejection a := by
  classical
  rw [FourCSP.rejection, testRate_prod (S := E) (T := EdgeSample K)
    (fun e s => ((reduced C).query (e,s)).Rejects a)]
  unfold BinaryCSP.rejection testRate
  rw [Finset.expect_div]
  apply Finset.expect_le_expect
  intro e _
  change (@ite ℝ ((decoded C a (C.left e), decoded C a (C.right e)) ∉ C.allowed e)
    (Classical.propDecidable _) 1 0) / 96 ≤ testRate (fun s : EdgeSample K =>
      ((reduced C).query (e,s)).Rejects a)
  rw [edge_rate]
  by_cases he : (decoded C a (C.left e), decoded C a (C.right e)) ∉ C.allowed e
  · simp only [ite_eq_left he]
    have hh := LocalRelation.sound (relation C e) (firstTable C a e) (secondTable C a e)
      (vertexTable C a (C.left e)) (vertexTable C a (C.right e)) he
    linarith
  · simp only [ite_eq_right he]
    have hh := LocalRelation.rejectionWeight_nonneg (relation C e) (firstTable C a e)
      (secondTable C a e) (vertexTable C a (C.left e)) (vertexTable C a (C.right e))
    linarith

omit [Fintype V] [Fintype E] in
theorem complete (x : V → BitVector K) (hx : C.Satisfies x) :
    ∃ a, (reduced C).Satisfies a := by
  classical
  have hh (e : E) := LocalRelation.complete (relation C e)
    ⟨(x (C.left e), x (C.right e)), hx e⟩
  choose f h he using hh
  let a : Position C → Bit := fun p => match p with
    | .inl (v,z) => dot (x v) z
    | .inr ⟨e,.inl z⟩ => f e z
    | .inr ⟨e,.inr z⟩ => h e z
  have hrate (e : E) : testRate (fun s : EdgeSample K =>
      ((reduced C).query (e,s)).Rejects a) = 0 := by
    rw [edge_rate]
    change LocalRelation.rejectionWeight (relation C e) (f e) (h e)
      (dot (x (C.left e))) (dot (x (C.right e))) / 6 = 0
    rw [he e]
    norm_num
  refine ⟨a,?_⟩
  rintro ⟨e,s⟩
  exact (testRate_eq_zero_iff _).mp (hrate e) s
end AlphabetReduction
end MetricKMedian.PCP

end Inline_PCPAlphabetReduction

end OAI
