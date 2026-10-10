import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite
import OAI.Computability.PerfectCompleteness.Reduction.CompletionLemmas

namespace OAI

section

noncomputable section

open scoped Classical

namespace PerfectCompleteness.CompletionProbability

variable {L A B : Type*}

abbrev Illegal (legal : L ↪ A) := {a : A // a ∉ Set.range legal}

def uniformProbability {Ω : Type*} [Fintype Ω] (event : Ω → Prop) : ℝ :=
  (Fintype.card {ω : Ω // event ω} : ℝ) / Fintype.card Ω

theorem card_illegal [Fintype L] [Fintype A] (legal : L ↪ A) :
    Fintype.card (Illegal legal) = Fintype.card A - Fintype.card L := by
  rw [Fintype.card_subtype_compl, Fintype.card_range legal]

def rotate {n : ℕ} [NeZero n] (legal : L ↪ A)
    (enum : Illegal legal ≃ Fin n) (seed : Fin n) : Equiv.Perm (Illegal legal) where
  toFun a := enum.symm (seed + enum a)
  invFun a := enum.symm (-seed + enum a)
  left_inv a := by simp [← add_assoc]
  right_inv a := by simp [← add_assoc]

def rotateAll {n : ℕ} [NeZero n] (legal : L ↪ A)
    (enum : Illegal legal ≃ Fin n) (seed : Fin n) : Equiv.Perm A :=
  (Equiv.refl {a : A // a ∈ Set.range legal}).subtypeCongr (rotate legal enum seed)

def sample {n : ℕ} [NeZero n] (legal : L ↪ A) (pHat : A → B)
    (enum : Illegal legal ≃ Fin n) (seed : Fin n) (a : A) : B :=
  pHat (rotateAll legal enum seed a)

@[simp] theorem sample_legal {n : ℕ} [NeZero n] (legal : L ↪ A)
    (pHat : A → B) (enum : Illegal legal ≃ Fin n) (seed : Fin n) (l : L) :
    sample legal pHat enum seed (legal l) = pHat (legal l) := by
  have hl : legal l ∈ Set.range legal := ⟨l, rfl⟩
  exact congrArg pHat (Equiv.Perm.subtypeCongr.left_apply
    (Equiv.refl {a : A // a ∈ Set.range legal}) (rotate legal enum seed) hl)

theorem sample_exact_two [Fintype A] {n : ℕ} [NeZero n]
    (legal : L ↪ A) (pHat : A → B) (enum : Illegal legal ≃ Fin n)
    (hexact : ∀ b, Fintype.card {a : A // pHat a = b} = 2) (seed : Fin n) (b : B) :
    Fintype.card {a : A // sample legal pHat enum seed a = b} = 2 := by
  exact (Fintype.card_congr ((rotateAll legal enum seed).subtypeEquivOfSubtype
    (p := fun a : A => pHat a = b))).trans (hexact b)

def seedEquiv {n : ℕ} [NeZero n] (legal : L ↪ A)
    (enum : Illegal legal ≃ Fin n) (a : Illegal legal) : Fin n ≃ Illegal legal where
  toFun seed := enum.symm (seed + enum a)
  invFun j := enum j - enum a
  left_inv seed := by simp
  right_inv j := by simp

@[simp] theorem sample_illegal {n : ℕ} [NeZero n] (legal : L ↪ A)
    (pHat : A → B) (enum : Illegal legal ≃ Fin n) (seed : Fin n) (a : Illegal legal) :
    sample legal pHat enum seed a.val = pHat ((seedEquiv legal enum a) seed).val := by
  exact congrArg pHat (Equiv.Perm.subtypeCongr.right_apply
    (Equiv.refl {a : A // a ∈ Set.range legal}) (rotate legal enum seed) a.property)

theorem sample_event_card [Fintype A] {n : ℕ} [NeZero n]
    (legal : L ↪ A) (pHat : A → B) (enum : Illegal legal ≃ Fin n)
    (a : Illegal legal) (b : B) :
    Fintype.card {seed : Fin n // sample legal pHat enum seed a.val = b} =
      Fintype.card {j : Illegal legal // pHat j.val = b} := by
  exact Fintype.card_congr ((seedEquiv legal enum a).subtypeEquiv
    (fun seed => by simp))

theorem sample_probability [Fintype A] {n : ℕ} [NeZero n]
    (legal : L ↪ A) (pHat : A → B) (enum : Illegal legal ≃ Fin n)
    (a : Illegal legal) (b : B) :
    uniformProbability (fun seed : Fin n => sample legal pHat enum seed a.val = b) =
      (Fintype.card {j : Illegal legal // pHat j.val = b} : ℝ) / n := by
  rw [uniformProbability, sample_event_card, Fintype.card_fin]

theorem residual_fiber_le_two [Fintype A] (legal : L ↪ A) (pHat : A → B)
    (hexact : ∀ b, Fintype.card {a : A // pHat a = b} = 2) (b : B) :
    Fintype.card {j : Illegal legal // pHat j.val = b} ≤ 2 := by
  let incl : {j : Illegal legal // pHat j.val = b} ↪ {a : A // pHat a = b} :=
    ⟨fun j => ⟨j.val.val, j.property⟩, by
      intro j k h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {a : A // pHat a = b} => z.val) h⟩
  exact (Fintype.card_le_of_embedding incl).trans (le_of_eq (hexact b))

theorem residual_fiber_card [Fintype L] [Fintype A]
    (legal : L ↪ A) (p : L → B) (pHat : A → B)
    (hext : ∀ l, pHat (legal l) = p l)
    (hexact : ∀ b, Fintype.card {a : A // pHat a = b} = 2) (b : B) :
    Fintype.card {a : Illegal legal // pHat a.val = b} =
      2 - Fintype.card {l : L // p l = b} := by
  let F := {a : A // pHat a = b}
  let P : F → Prop := fun a => a.val ∈ Set.range legal
  let eLegal : {l : L // p l = b} ≃ {a : F // P a} := by
    refine Equiv.ofBijective
      (fun l : {l : L // p l = b} =>
        (⟨⟨legal l.val, (hext l.val).trans l.property⟩,
          ⟨l.val, rfl⟩⟩ : {a : F // P a})) ⟨?_, ?_⟩
    · intro x y h
      apply Subtype.ext
      apply legal.injective
      exact congrArg (fun a : {a : F // P a} => a.val.val) h
    · intro a
      obtain ⟨l, hl⟩ := (a.property : a.val.val ∈ Set.range legal)
      have hpl : p l = b :=
        (hext l).symm.trans ((congrArg pHat hl).trans a.val.property)
      refine ⟨⟨l, hpl⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hl
  let eResidual : {a : Illegal legal // pHat a.val = b} ≃ {a : F // ¬P a} := {
    toFun := fun a => ⟨⟨a.val.val, a.property⟩, a.val.property⟩
    invFun := fun a => ⟨⟨a.val.val, a.property⟩, a.val.property⟩
    left_inv := fun a => by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := fun a => by
      apply Subtype.ext
      apply Subtype.ext
      rfl
  }
  have hF : Fintype.card F = 2 := hexact b
  calc
    _ = Fintype.card {a : F // ¬P a} := Fintype.card_congr eResidual
    _ = Fintype.card F - Fintype.card {a : F // P a} :=
      Fintype.card_subtype_compl P
    _ = 2 - Fintype.card {l : L // p l = b} := by
      rw [hF, ← Fintype.card_congr eLegal]

theorem sample_probability_residual [Fintype L] [Fintype A] {n : ℕ} [NeZero n]
    (legal : L ↪ A) (p : L → B) (pHat : A → B) (enum : Illegal legal ≃ Fin n)
    (hext : ∀ l, pHat (legal l) = p l)
    (hexact : ∀ b, Fintype.card {a : A // pHat a = b} = 2)
    (a : Illegal legal) (b : B) :
    uniformProbability (fun seed : Fin n => sample legal pHat enum seed a.val = b) =
      ((2 - Fintype.card {l : L // p l = b} : ℕ) : ℝ) /
        (Fintype.card A - Fintype.card L : ℕ) := by
  rw [sample_probability]
  have hn : n = Fintype.card A - Fintype.card L := by
    rw [← card_illegal legal]
    simpa only [Fintype.card_fin] using (Fintype.card_congr enum).symm
  rw [← hn]
  simpa only [← Nat.card_eq_fintype_card] using
    congrArg (fun k : ℕ => (k : ℝ) / (n : ℝ))
      (residual_fiber_card legal p pHat hext hexact b)

theorem sample_probability_le [Fintype L] [Fintype A] {n : ℕ} [NeZero n]
    (legal : L ↪ A) (pHat : A → B) (enum : Illegal legal ≃ Fin n)
    (hexact : ∀ b, Fintype.card {a : A // pHat a = b} = 2)
    (a : Illegal legal) (b : B) :
    uniformProbability (fun seed : Fin n => sample legal pHat enum seed a.val = b) ≤
      2 / (Fintype.card A - Fintype.card L : ℕ) := by
  have hn : n = Fintype.card A - Fintype.card L := by
    rw [← card_illegal legal]
    simpa only [Fintype.card_fin] using (Fintype.card_congr enum).symm
  rw [sample_probability, hn]
  apply div_le_div_of_nonneg_right
  · exact Nat.cast_le.mpr (residual_fiber_le_two legal pHat hexact b)
  · exact Nat.cast_nonneg _

theorem exists_completion_sampler [Fintype L] [Fintype A] [Fintype B]
    (legal : L ↪ A) (p : L → B)
    (hsmall : ∀ b, Fintype.card {l : L // p l = b} ≤ 2)
    (hcard : Fintype.card A = 2 * Fintype.card B) :
    ∃ n : ℕ, 0 < n ∧ ∃ sampler : Fin n → A → B,
      (∀ seed l, sampler seed (legal l) = p l) ∧
      (∀ seed b, Fintype.card {a : A // sampler seed a = b} = 2) ∧
      ∀ (a : Illegal legal) (b : B),
        uniformProbability (fun seed => sampler seed a.val = b) =
          ((2 - Fintype.card {l : L // p l = b} : ℕ) : ℝ) /
            (Fintype.card A - Fintype.card L : ℕ) ∧
        uniformProbability (fun seed => sampler seed a.val = b) ≤
          2 / (Fintype.card A - Fintype.card L : ℕ) := by
  obtain ⟨pHat, hext, hexact⟩ :=
    Completion.exists_exact_two_completion legal p hsmall hcard
  by_cases hz : Fintype.card (Illegal legal) = 0
  · refine ⟨1, Nat.zero_lt_one, (fun _ => pHat), ?_, ?_, ?_⟩
    · intro seed l
      exact hext l
    · intro seed b
      exact hexact b
    · intro a b
      have hp : 0 < Fintype.card (Illegal legal) := Fintype.card_pos_iff.mpr ⟨a⟩
      exact False.elim (Nat.ne_of_gt hp hz)
  · let : NeZero (Fintype.card (Illegal legal)) := ⟨hz⟩
    let enum := Fintype.equivFin (Illegal legal)
    refine ⟨Fintype.card (Illegal legal), Nat.pos_of_ne_zero hz,
      sample legal pHat enum, ?_, ?_, ?_⟩
    · intro seed l
      simpa only [sample_legal] using hext l
    · intro seed b
      exact sample_exact_two legal pHat enum hexact seed b
    · intro a b
      exact ⟨sample_probability_residual legal p pHat enum hext hexact a b,
        sample_probability_le legal pHat enum hexact a b⟩

end PerfectCompleteness.CompletionProbability

end

end

end OAI
