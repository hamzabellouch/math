import OAI.ModelTheory.Categoricity.Partition

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Colors

abbrev Sequence := ℕ → Bool

def equivalent (a b : Sequence) : Prop := {n | a n ≠ b n}.Finite

def eventualSetoid : Setoid Sequence where
  r := equivalent
  iseqv := ⟨by intro a; simp [equivalent], by
    intro a b h
    simpa only [equivalent, ne_comm] using h, by
    intro a b c hab hbc
    apply (hab.union hbc).subset
    intro n hn
    by_cases hab' : a n = b n
    · exact Or.inr (fun hbc' => hn (hab'.trans hbc'))
    · exact Or.inl hab' ⟩

abbrev Color := Quotient eventualSetoid

def color (a : Sequence) : Color := Quotient.mk _ a

theorem color_eq_iff (a b : Sequence) : color a = color b ↔ equivalent a b :=
  Quotient.eq

def repeatSequence (a : Sequence) : Sequence := fun i => a (Nat.unpair i).1

theorem repeat_injective : Function.Injective (fun a => color (repeatSequence a)) := by
  intro a b hab
  have h := (color_eq_iff _ _).1 hab
  funext n
  by_contra hn
  have hi : Function.Injective (Nat.pair n) := by
    intro j k heq
    have := congrArg Nat.unpair heq
    simpa only [Nat.unpair_pair, Prod.mk.injEq, true_and] using this
  have hf : (Set.range (Nat.pair n)).Finite := h.subset (by
    rintro _ ⟨m, rfl⟩
    simpa only [repeatSequence, Nat.unpair_pair, Set.mem_ofPred_eq] using hn)
  exact Set.infinite_univ ((hf.preimage hi.injOn).subset (fun _ _ => Set.mem_range_self _))

theorem cardinal : #Color = (𝔠 : Cardinal) := by
  have h : #Sequence = (𝔠 : Cardinal) := by simp [Sequence]
  apply le_antisymm
  · exact Cardinal.mk_quotient_le.trans h.le
  · exact h.symm.le.trans (Cardinal.mk_le_of_injective repeat_injective)

abbrev Palette := ULift.{u} Color

theorem palette_cardinal : #Palette.{u} = (𝔠 : Cardinal.{u}) := by
  rw [Cardinal.mk_uLift, cardinal, Cardinal.lift_continuum]

def representative (s : Color) : Sequence := Quotient.out s

theorem representative_color (s : Color) : color (representative s) = s := Quotient.out_eq s

theorem function_bound (A : Type) [Countable A] (B : Type u)
    (hB : #B ≤ (𝔠 : Cardinal.{u})) : #(A → B) ≤ (𝔠 : Cardinal.{u}) := by
  rw [Cardinal.mk_arrow, Cardinal.lift_uzero]
  have hA : Cardinal.lift.{u} #A ≤ (ℵ₀ : Cardinal.{u}) := by
    simpa only [Cardinal.lift_aleph0] using
      (Cardinal.lift_le.{u, 0}.2 (Cardinal.mk_le_aleph0 (α := A)))
  exact ((Cardinal.power_le_power_right hB).trans
    (Cardinal.power_le_power_left Cardinal.continuum_ne_zero hA)).trans_eq
    Cardinal.continuum_power_aleph0

open Diagrams

theorem diagram_bound (hCH : CH.{u}) (n : ℕ) :
    #(Diagram.{u} (Fin n)) ≤ (𝔠 : Cardinal.{u}) := by
  let A := Label (Fin n)
  have hc : Cardinal.lift.{u} #(A → A → Prop) ≤ (𝔠 : Cardinal.{u}) := by
    have h : #(A → A → Prop) ≤ (𝔠 : Cardinal) :=
      function_bound A _ (function_bound A Prop (by rw [Cardinal.mk_Prop]; exact (Cardinal.nat_lt_continuum 2).le))
    simpa only [Cardinal.lift_continuum] using
      (Cardinal.lift_le.{u, 0}.2 h)
  have ht : #(A → Tag.{u}) ≤ (𝔠 : Cardinal.{u}) :=
    function_bound A _ (by rw [Cardinal.mk_toType, Ordinal.card_omega, ← Cardinal.two_power_aleph0, hCH])
  let f : Diagram.{u} (Fin n) → ((A → A → Prop) × (A → A → Prop)) × (A → Tag.{u}) :=
    fun d => ((d.eqv, d.rel), d.tag)
  have hf : Function.Injective f := by
    intro d e h
    cases d; cases e
    simpa only [f, Prod.mk.injEq, Diagram.mk.injEq, and_assoc] using h
  apply (Cardinal.mk_le_of_injective hf).trans
  simp only [Cardinal.mk_prod, Cardinal.lift_mul, Cardinal.lift_id, Cardinal.lift_uzero]
  exact (mul_le_mul' (mul_le_mul' hc hc) ht).trans_eq (by
    rw [Cardinal.mul_eq_self Cardinal.aleph0_le_continuum,
      Cardinal.mul_eq_self Cardinal.aleph0_le_continuum])

def code (hCH : CH.{u}) : (Σ n : ℕ, Diagram.{u} (Fin (n + 1))) ↪ Palette.{u} := by
  apply Classical.choice
  apply (Cardinal.le_def _ _).1
  rw [palette_cardinal, Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun n : ℕ => #(Diagram.{u} (Fin (n + 1)))) ≤
        Cardinal.sum (fun _ : ℕ => (𝔠 : Cardinal.{u})) :=
      Cardinal.sum_le_sum _ _ (fun n => diagram_bound hCH (n + 1))
    _ = (𝔠 : Cardinal.{u}) := by
      simp only [Cardinal.sum_const, Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_uzero]
      exact Cardinal.aleph0_mul_continuum

end Colors

namespace Tuples

abbrev Tuple (I : Type v) := Σ n : ℕ, Fin (n + 1) ↪ I

def sub {I : Type v} (t : Tuple I) {m : ℕ} (e : Fin (m + 1) ↪o Fin (t.1 + 1)) :
    Tuple I := ⟨m, e.toEmbedding.trans t.2⟩

@[simp] theorem sub_refl {I : Type v} (t : Tuple I) :
    sub t (OrderIso.refl _).toOrderEmbedding = t := by
  cases t
  rfl

theorem sub_comp {I : Type v} (t : Tuple I) {m k : ℕ}
    (e : Fin (m + 1) ↪o Fin (t.1 + 1)) (f : Fin (k + 1) ↪o Fin (m + 1)) :
    sub (sub t e) f = sub t (f.comp e) := rfl

end Tuples

namespace Tests

theorem embedding_refl (A : Type v) [Preorder A] :
    (OrderIso.refl A).toOrderEmbedding.toEmbedding = Function.Embedding.refl A := by
  ext x
  rfl

open Diagrams Colors Tuples

variable (hCH : CH.{u})

def Passes {n : ℕ}
    (s : ∀ m : ℕ, (Fin (m + 1) ↪o Fin (n + 1)) → Palette.{u}) : Prop :=
  ∃ d : Diagram.{u} (Fin (n + 1)), ∀ m (e : Fin (m + 1) ↪o Fin (n + 1)),
    (d.restrict e.toEmbedding).Valid ∧
      code hCH ⟨m, d.restrict e.toEmbedding⟩ = s m e

def Test {I : Type v} (c : Tuple I → Palette.{u}) (t : Tuple I) : Prop :=
  Passes hCH (fun _ e => c (sub t e))

instance emptyLabel : IsEmpty (Label (Fin 0)) := ⟨fun l => by
  obtain ⟨x, _⟩ := l.1.property
  exact Fin.elim0 x⟩

def emptyDiagram : Diagram.{u} (Fin 0) where
  eqv a := isEmptyElim a
  rel a := isEmptyElim a
  tag a := isEmptyElim a

theorem empty_valid : emptyDiagram.{u}.Valid := by
  constructor
  · exact ⟨fun a => isEmptyElim a, fun {a} => isEmptyElim a, fun {a} => isEmptyElim a⟩
  all_goals intro a; exact isEmptyElim a

theorem empty_unique (d : Diagram.{u} (Fin 0)) : d = emptyDiagram := by
  cases d
  congr <;> funext a <;> exact isEmptyElim a

theorem no_pattern (p : ℕ → Palette.{u})
    (hp : ∀ n : ℕ, Passes hCH (n := n) (fun m _ => p m)) : False := by
  choose d hd using hp
  have hvalid : ∀ n, (d n).Valid := by
    intro n
    simpa only [embedding_refl, Diagram.restrict_refl] using (hd n n (OrderIso.refl _).toOrderEmbedding).1
  have hcode : ∀ n, code hCH ⟨n, d n⟩ = p n := by
    intro n
    simpa only [embedding_refl, Diagram.restrict_refl] using (hd n n (OrderIso.refl _).toOrderEmbedding).2
  have hcoh : ∀ m n (e : Fin (m + 1) ↪o Fin (n + 1)),
      d m = (d n).restrict e.toEmbedding := by
    intro m n e
    have he := (code hCH).injective ((hcode m).trans (hd n m e).2.symm)
    exact eq_of_heq (Sigma.mk.inj_iff.1 he).2
  let allD : ∀ k : ℕ, Diagram.{u} (Fin k)
    | 0 => emptyDiagram
    | n + 1 => d n
  apply NoPattern.impossible allD
  · intro k
    cases k with
    | zero => exact empty_valid
    | succ n => exact hvalid n
  · intro m n e
    cases m with
    | zero => exact (empty_unique ((allD n).restrict e.toEmbedding)).symm
    | succ m =>
      cases n with
      | zero => exact Fin.elim0 (e 0)
      | succ n => exact hcoh m n e

end Tests

end CHObstruction

end

end OAI
