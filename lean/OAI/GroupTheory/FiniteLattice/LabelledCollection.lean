import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

namespace OAI

/-! Collection of subgroup factors by labels. The error subgroup normalizes each factor; it need not be normal in the generated group. -/

namespace FiniteLattice.LabelledCollection

open scoped commutatorElement

variable {G Λ I : Type*} [Group G]

def generated (P : Λ → Subgroup G) (S : Set Λ) : Subgroup G :=
  Subgroup.closure {g | ∃ l, l ∈ S ∧ g ∈ P l}

lemma generator_mem (P : Λ → Subgroup G) (S : Set Λ)
    {l : Λ} (hl : l ∈ S) {g : G} (hg : g ∈ P l) : g ∈ generated P S :=
  Subgroup.subset_closure ⟨l, hl, hg⟩

lemma conjugate_generated (P : Λ → Subgroup G) (C : Subgroup G)
    (hN : ∀ l, C ≤ Subgroup.normalizer (P l : Set G)) (S : Set Λ)
    {c g : G} (hc : c ∈ C) (hg : g ∈ generated P S) :
    c * g * c⁻¹ ∈ generated P S := by
  change g ∈ Subgroup.closure {g | ∃ l, l ∈ S ∧ g ∈ P l} at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨l, hl, hx⟩ := hx
      exact generator_mem P S hl ((Subgroup.mem_normalizer_iff.mp (hN l hc) x).mp hx)
  | one => simp
  | mul x y hx hy ihx ihy =>
      convert (generated P S).mul_mem ihx ihy using 1
      group
  | inv x hx ih =>
      convert (generated P S).inv_mem ih using 1
      group

lemma move_labelled_word (P : Λ → Subgroup G) (label : Λ → I)
    (C : Subgroup G) (hN : ∀ l, C ≤ Subgroup.normalizer (P l : Set G))
    (hComm : ∀ l m, label l ≠ label m → ⁅P l, P m⁆ ≤ C)
    (k : I) (l : Λ) (hl : label l ≠ k)
    {q : G} (hq : q ∈ generated P {m | label m = k}) :
    ∀ a ∈ P l, ∃ p ∈ P l, ∃ q' ∈ generated P {m | label m = k},
      ∃ c ∈ C, q * a = p * q' * c := by
  classical
  let B := generated P {m | label m = k}
  have step (b : G) (hb : ∃ m, label m = k ∧ b ∈ P m)
      (q : G) (ih : ∀ a ∈ P l, ∃ p ∈ P l, ∃ q' ∈ B,
        ∃ c ∈ C, q * a = p * q' * c) :
      ∀ a ∈ P l, ∃ p ∈ P l, ∃ q' ∈ B,
        ∃ c ∈ C, (b * q) * a = p * q' * c := by
    obtain ⟨m, hm, hb⟩ := hb
    intro a ha
    obtain ⟨p, hp, q', hq', c, hc, heq⟩ := ih a ha
    let d : G := ⁅b, p⁆
    have hd : d ∈ C := by
      apply hComm m l (by intro h; exact hl (h.symm.trans hm))
      exact Subgroup.commutator_mem_commutator hb hp
    have hp' : d * p * d⁻¹ ∈ P l :=
      (Subgroup.mem_normalizer_iff.mp (hN l hd) p).mp hp
    have hbB : b ∈ B := generator_mem P _ hm hb
    have hq'' : d * (b * q') * d⁻¹ ∈ B :=
      conjugate_generated P C hN _ hd (B.mul_mem hbB hq')
    refine ⟨d * p * d⁻¹, hp', d * (b * q') * d⁻¹, hq'',
      d * c, C.mul_mem hd hc, ?_⟩
    calc
      (b * q) * a = b * (p * q' * c) := by rw [mul_assoc, heq]
      _ = (d * p * d⁻¹) * (d * (b * q') * d⁻¹) * (d * c) := by
        dsimp [d]
        simp only [commutatorElement_def]
        group
  change q ∈ Subgroup.closure {g | ∃ m, label m = k ∧ g ∈ P m} at hq
  refine Subgroup.closure_induction_left (p := fun q _ =>
    ∀ a ∈ P l, ∃ p ∈ P l, ∃ q' ∈ B, ∃ c ∈ C, q * a = p * q' * c)
    ?_ ?_ ?_ hq
  · intro a ha
    exact ⟨a, ha, 1, B.one_mem, 1, C.one_mem, by simp⟩
  · intro b hb q _ ih
    exact step b hb q ih
  · intro b hb q _ ih
    obtain ⟨m, hm, hb⟩ := hb
    exact step b⁻¹ ⟨m, hm, (P m).inv_mem hb⟩ q ih

theorem collection_flattened [Finite Λ] (P : Λ → Subgroup G) (label : Λ → I)
    (C : Subgroup G) (hN : ∀ l, C ≤ Subgroup.normalizer (P l : Set G))
    (hComm : ∀ l m, label l ≠ label m → ⁅P l, P m⁆ ≤ C)
    (k : I) {g : G} (hg : g ∈ generated P Set.univ) :
    ∃ p ∈ generated P {l | label l ≠ k},
      ∃ q ∈ generated P {l | label l = k},
        ∃ c ∈ C, g = p * q * c := by
  classical
  let A := generated P {l | label l ≠ k}
  let B := generated P {l | label l = k}
  have step (x : G)
      (ih : ∃ p ∈ A, ∃ q ∈ B, ∃ c ∈ C, x = p * q * c)
      (a : G) (ha : ∃ l, l ∈ (Set.univ : Set Λ) ∧ a ∈ P l) :
      ∃ p ∈ A, ∃ q ∈ B, ∃ c ∈ C, x * a = p * q * c := by
    obtain ⟨p, hp, q, hq, c, hc, rfl⟩ := ih
    obtain ⟨l, _, ha⟩ := ha
    let a' := c * a * c⁻¹
    have ha' : a' ∈ P l :=
      (Subgroup.mem_normalizer_iff.mp (hN l hc) a).mp ha
    by_cases hl : label l = k
    · have haB : a' ∈ B := generator_mem P _ hl ha'
      refine ⟨p, hp, q * a', B.mul_mem hq haB, c, hc, ?_⟩
      dsimp [a']
      group
    · obtain ⟨p', hp', q', hq', c', hc', heq⟩ :=
        move_labelled_word P label C hN hComm k l hl hq a' ha'
      have hpA : p' ∈ A := generator_mem P _ hl hp'
      refine ⟨p * p', A.mul_mem hp hpA, q', hq', c' * c, C.mul_mem hc' hc, ?_⟩
      calc
        (p * q * c) * a = p * (q * a') * c := by dsimp [a']; group
        _ = (p * p') * q' * (c' * c) := by rw [heq]; group
  change g ∈ Subgroup.closure {g | ∃ l, l ∈ (Set.univ : Set Λ) ∧ g ∈ P l} at hg
  refine Subgroup.closure_induction_right (p := fun g _ =>
    ∃ p ∈ A, ∃ q ∈ B, ∃ c ∈ C, g = p * q * c) ?_ ?_ ?_ hg
  · exact ⟨1, A.one_mem, 1, B.one_mem, 1, C.one_mem, by simp⟩
  · intro x _ a ha ih
    exact step x ih a ha
  · intro x _ a ha ih
    obtain ⟨l, hl, ha⟩ := ha
    exact step x ih a⁻¹ ⟨l, hl, (P l).inv_mem ha⟩

lemma generated_labels (P : Λ → Subgroup G) (label : Λ → I) (J : Set I) :
    generated (fun j => generated P {l | label l = j}) J =
      generated P {l | label l ∈ J} := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨j, hj, hx⟩
    have hle : generated P {l | label l = j} ≤ generated P {l | label l ∈ J} := by
      apply (Subgroup.closure_le _).mpr
      rintro y ⟨l, hl, hy⟩
      have hlabel : label l = j := hl
      have hmem : label l ∈ J := hlabel.symm ▸ hj
      exact Subgroup.subset_closure ⟨l, hmem, hy⟩
    exact hle hx
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨l, hl, hx⟩
    have hx' : x ∈ generated P {m | label m = label l} :=
      Subgroup.subset_closure ⟨l, rfl, hx⟩
    exact Subgroup.subset_closure ⟨label l, hl, hx'⟩

theorem collection [Finite Λ] (P : Λ → Subgroup G) (label : Λ → I)
    (C : Subgroup G) (hN : ∀ l, C ≤ Subgroup.normalizer (P l : Set G))
    (hComm : ∀ l m, label l ≠ label m → ⁅P l, P m⁆ ≤ C)
    (k : I) {g : G}
    (hg : g ∈ generated (fun j => generated P {l | label l = j}) Set.univ) :
    ∃ p ∈ generated (fun j => generated P {l | label l = j}) {j | j ≠ k},
      ∃ q ∈ generated P {l | label l = k},
        ∃ c ∈ C, g = p * q * c := by
  have hg' : g ∈ generated P Set.univ := by
    rw [generated_labels] at hg
    simpa only [Set.mem_univ, Set.ofPred_true] using hg
  obtain ⟨p, hp, q, hq, c, hc, heq⟩ := collection_flattened P label C hN hComm k hg'
  refine ⟨p, ?_, q, hq, c, hc, heq⟩
  rw [generated_labels]
  exact hp

end FiniteLattice.LabelledCollection

end OAI
