import OAI.NumberTheory.TwoPoint.Circuits.CircuitComparison
import OAI.NumberTheory.TwoPoint.Bounds.CommonResidueLift
import OAI.NumberTheory.TwoPoint.Bounds.LitBlockGeometry
import Mathlib.Data.Nat.Squarefree

namespace OAI

/-! The actual deleted event is a finite depth-two DNF of prime tests. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace AC0Circuit

/-- One conjunction for each accepted numerical word. -/
noncomputable def finiteDNF {W : Type*} [Fintype W] (T : W → Type*) [∀ w, Fintype (T w)]
    {n : ℕ} (input : ∀ w, T w → Fin n) : AC0Circuit n :=
  .orGate (fun j : Fin (Fintype.card W) =>
    .andGate (fun k : Fin (Fintype.card (T ((Fintype.equivFin W).symm j))) =>
      .literal (input _ ((Fintype.equivFin _).symm k)) true))

lemma finiteDNF_eval {W : Type*} [Fintype W] (T : W → Type*) [∀ w, Fintype (T w)]
    {n : ℕ} (input : ∀ w, T w → Fin n) (x : BooleanCube n) :
    (finiteDNF T input).eval x = true ↔ ∃ w, ∀ t, x (input w t) = true := by
  simp only [finiteDNF, eval, ite_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨(Fintype.equivFin W).symm j, ?_⟩
    intro t
    simpa only [Equiv.symm_apply_apply] using hj ((Fintype.equivFin _ ) t)
  · rintro ⟨w, hw⟩
    obtain ⟨j, rfl⟩ := (Fintype.equivFin W).symm.surjective w
    exact ⟨j, fun k => hw ((Fintype.equivFin _).symm k)⟩

lemma finiteDNF_depth {W : Type*} [Fintype W] (T : W → Type*) [∀ w, Fintype (T w)]
    {n : ℕ} (input : ∀ w, T w → Fin n) : (finiteDNF T input).depth ≤ 2 := by
  simp only [finiteDNF, depth]
  have h : (univ.sup fun j : Fin (Fintype.card W) =>
      1 + univ.sup (fun _ : Fin (Fintype.card (T ((Fintype.equivFin W).symm j))) => (0 : ℕ))) ≤ 1 := by
    apply Finset.sup_le
    intro j _
    simp
  omega

lemma finiteDNF_size {W : Type*} [Fintype W] (T : W → Type*) [∀ w, Fintype (T w)]
    {n : ℕ} (input : ∀ w, T w → Fin n) :
    (finiteDNF T input).size = 1 + ∑ w, (1 + Fintype.card (T w)) := by
  simp only [finiteDNF, size, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 1
  simpa only [Nat.cast_id] using
    (Fintype.equivFin W).symm.sum_comp (fun w => 1 + Fintype.card (T w))

end AC0Circuit

/-- Finite numerical alphabet: an orientation and an admissible tuple/padding pair. -/
abbrev StepAlphabet (pairs : Finset (ℕ × ℕ)) := Bool × pairs

def decodeStep {pairs : Finset (ℕ × ℕ)} (a : StepAlphabet pairs) : SignedStep :=
  ⟨a.1, a.2.val.1, a.2.val.2⟩

abbrev BoundedStepWords (pairs : Finset (ℕ × ℕ)) (s : ℕ) :=
  (m : Fin (s + 1)) × (Fin m.val → StepAlphabet pairs)

def decodeStepWord {pairs : Finset (ℕ × ℕ)} {s : ℕ} (c : BoundedStepWords pairs s) :
    List SignedStep := List.ofFn (fun i => decodeStep (c.2 i))

lemma decodeStepWord_length {pairs : Finset (ℕ × ℕ)} {s : ℕ}
    (c : BoundedStepWords pairs s) : (decodeStepWord c).length = c.1.val := by
  simp [decodeStepWord]

lemma stepWord_covered (pairs : Finset (ℕ × ℕ)) (s : ℕ) (w : List SignedStep)
    (hlen : w.length ≤ s) (hpairs : ∀ a ∈ w, (a.tuple, a.padding) ∈ pairs) :
    ∃ c : BoundedStepWords pairs s, decodeStepWord c = w := by
  let f : Fin w.length → StepAlphabet pairs := fun i =>
    ⟨(w.get i).forward, ⟨((w.get i).tuple, (w.get i).padding), hpairs _ (List.get_mem _ _)⟩⟩
  refine ⟨⟨⟨w.length, by omega⟩, f⟩, ?_⟩
  change List.ofFn (fun i : Fin w.length => decodeStep (f i)) = w
  have he : (fun i : Fin w.length => decodeStep (f i)) = w.get := by
    funext i
    cases hw : w.get i
    simp only [f, decodeStep, hw]
  rw [he, List.ofFn_get]

abbrev ProhibitedCatalog (pairs : Finset (ℕ × ℕ)) (h s : ℕ) :=
  {c : BoundedStepWords pairs s //
    MinimalWord (ForwardProhibited h s (fun d q => (d, q) ∈ pairs)) (decodeStepWord c)}

abbrev ProhibitedWordTests {pairs : Finset (ℕ × ℕ)} {h s : ℕ}
    (c : ProhibitedCatalog pairs h s) :=
  (i : Fin (decodeStepWord c.val).length) ×
    {p : ℕ // p ∈ (((decodeStepWord c.val).get i).padding *
      ((decodeStepWord c.val).get i).tuple).primeFactors}

abbrev ProhibitedInputs (pairs : Finset (ℕ × ℕ)) (h s : ℕ) :=
  (c : ProhibitedCatalog pairs h s) × ProhibitedWordTests c

noncomputable def prohibitedInputIndex (pairs : Finset (ℕ × ℕ)) (h s : ℕ) :
    ProhibitedInputs pairs h s ≃ Fin (Fintype.card (ProhibitedInputs pairs h s)) :=
  Fintype.equivFin _

noncomputable def prohibitedCircuit (pairs : Finset (ℕ × ℕ)) (h s : ℕ) :
    AC0Circuit (Fintype.card (ProhibitedInputs pairs h s)) :=
  AC0Circuit.finiteDNF ProhibitedWordTests (fun c t => prohibitedInputIndex pairs h s ⟨c, t⟩)

noncomputable def prohibitedInputAt (pairs : Finset (ℕ × ℕ)) (h s : ℕ) (n : ℤ) :
    BooleanCube (Fintype.card (ProhibitedInputs pairs h s)) := fun j =>
  let t := (prohibitedInputIndex pairs h s).symm j
  decide ((t.2.2.val : ℤ) ∣ n + wordDisplacement h ((decodeStepWord t.1.val).take t.2.1.val))

lemma prohibitedInputAt_index (pairs : Finset (ℕ × ℕ)) (h s : ℕ) (n : ℤ)
    (c : ProhibitedCatalog pairs h s) (t : ProhibitedWordTests c) :
    prohibitedInputAt pairs h s n (prohibitedInputIndex pairs h s ⟨c, t⟩) =
      decide ((t.2.val : ℤ) ∣ n + wordDisplacement h ((decodeStepWord c.val).take t.1.val)) := by
  exact congrArg (fun u : ProhibitedInputs pairs h s =>
    decide ((u.2.2.val : ℤ) ∣ n + wordDisplacement h ((decodeStepWord u.1.val).take u.2.1.val)))
      ((prohibitedInputIndex pairs h s).symm_apply_apply ⟨c, t⟩)

lemma squarefree_divisor_iff (d : ℕ) (hd : Squarefree d) (n : ℤ) :
    (d : ℤ) ∣ n ↔ ∀ p ∈ d.primeFactors, (p : ℤ) ∣ n := by
  constructor
  · intro hn p hp
    have hp' : (p : ℤ) ∣ (d : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
    exact hp'.trans hn
  · intro hn
    rw [← Nat.prod_primeFactors_of_squarefree hd, Nat.cast_prod]
    apply prod_dvd_of_coprime
    · intro p hp q hq hpq
      exact ((Nat.coprime_primes (Nat.mem_primeFactors.mp hp).1
        (Nat.mem_primeFactors.mp hq).1).mpr hpq).cast (R := ℤ)
    · exact hn

lemma positiveWord_iff_prime_tests (h : ℕ) (n : ℤ) (w : List SignedStep)
    (hsq : ∀ a ∈ w, Squarefree (a.padding * a.tuple)) :
    PositiveWord h n w ↔ ∀ i : Fin w.length,
      ∀ p ∈ ((w.get i).padding * (w.get i).tuple).primeFactors,
        (p : ℤ) ∣ n + wordDisplacement h (w.take i.val) := by
  rw [positiveWord_iff_departures]
  apply forall_congr'
  intro i
  simpa only [SignedStep.divisor, Nat.cast_mul] using
    squarefree_divisor_iff _ (hsq _ (List.get_mem _ _)) (n + wordDisplacement h (w.take i.val))

/-- The circuit accepts precisely the manuscript's deleted event, not a
larger class of arbitrary positive paths. Minimal words are preselected. -/
theorem prohibitedCircuit_correct (pairs : Finset (ℕ × ℕ)) (h s : ℕ) (n : ℤ)
    (hsq : ∀ dq ∈ pairs, Squarefree (dq.2 * dq.1)) :
    (prohibitedCircuit pairs h s).eval (prohibitedInputAt pairs h s n) = true ↔
      ProhibitedSite h s (fun d q => (d, q) ∈ pairs) n := by
  rw [prohibitedCircuit, AC0Circuit.finiteDNF_eval]
  have hprime (c : ProhibitedCatalog pairs h s) :
      (∀ t : ProhibitedWordTests c,
        prohibitedInputAt pairs h s n (prohibitedInputIndex pairs h s ⟨c, t⟩) = true) ↔
        PositiveWord h n (decodeStepWord c.val) := by
    have hc : ∀ a ∈ decodeStepWord c.val, Squarefree (a.padding * a.tuple) := by
      intro a ha
      exact hsq _ (c.property.1.2.2.1 a ha)
    rw [positiveWord_iff_prime_tests h n _ hc]
    simp only [prohibitedInputAt_index, decide_eq_true_eq]
    constructor
    · intro ht i p hp
      exact ht ⟨i, ⟨p, hp⟩⟩
    · intro ht t
      exact ht t.1 t.2.val t.2.property
  simp_rw [hprime]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨decodeStepWord c.val, hc, c.property⟩
  · rintro ⟨w, hw, hmin⟩
    obtain ⟨c, hc⟩ := stepWord_covered pairs s w hmin.1.2.1 hmin.1.2.2.1
    refine ⟨⟨c, ?_⟩, ?_⟩
    · simpa only [hc] using hmin
    · simpa only [hc] using hw

theorem prohibitedCircuit_depth (pairs : Finset (ℕ × ℕ)) (h s : ℕ) :
    (prohibitedCircuit pairs h s).depth ≤ 2 := AC0Circuit.finiteDNF_depth _ _

theorem prohibitedCircuit_size (pairs : Finset (ℕ × ℕ)) (h s : ℕ) :
    (prohibitedCircuit pairs h s).size =
      1 + ∑ c : ProhibitedCatalog pairs h s, (1 + Fintype.card (ProhibitedWordTests c)) :=
  AC0Circuit.finiteDNF_size _ _

theorem card_boundedStepWords_le (pairs : Finset (ℕ × ℕ)) (s : ℕ) :
    Fintype.card (BoundedStepWords pairs s) ≤
      (s + 1) * (max 1 (2 * pairs.card)) ^ s := by
  rw [show Fintype.card (BoundedStepWords pairs s) =
    ∑ m : Fin (s + 1), (2 * pairs.card) ^ m.val by
      simp only [BoundedStepWords, Fintype.card_sigma, Fintype.card_fun,
        StepAlphabet, Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, Fintype.card_fin]]
  calc
    _ ≤ ∑ _m : Fin (s + 1), (max 1 (2 * pairs.card)) ^ s := by
      apply sum_le_sum
      intro m _
      exact (Nat.pow_le_pow_left (le_max_right _ _) _).trans
        (Nat.pow_le_pow_right (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) (by omega))
    _ = _ := by simp [Nat.mul_comm]

theorem card_prohibitedWordTests_le {pairs : Finset (ℕ × ℕ)} {h s M : ℕ}
    (c : ProhibitedCatalog pairs h s)
    (hM : ∀ a ∈ decodeStepWord c.val, (a.padding * a.tuple).primeFactors.card ≤ M) :
    Fintype.card (ProhibitedWordTests c) ≤ s * M := by
  change Fintype.card ((i : Fin (decodeStepWord c.val).length) ×
    {p : ℕ // p ∈ (((decodeStepWord c.val).get i).padding *
      ((decodeStepWord c.val).get i).tuple).primeFactors}) ≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _i : Fin (decodeStepWord c.val).length, M := by
      apply sum_le_sum
      intro i _
      simpa only [Fintype.card_coe] using hM _ (List.get_mem _ _)
    _ = (decodeStepWord c.val).length * M := by simp
    _ ≤ s * M := Nat.mul_le_mul_right M (by
      rw [decodeStepWord_length]
      exact Nat.le_of_lt_succ c.val.1.isLt)

/-- An explicit size bound, including every input occurrence. The only
numerical data are the finite step alphabet and its prime-factor cap. -/
theorem prohibitedCircuit_size_le (pairs : Finset (ℕ × ℕ)) (h s M : ℕ)
    (hM : ∀ dq ∈ pairs, (dq.2 * dq.1).primeFactors.card ≤ M) :
    (prohibitedCircuit pairs h s).size ≤
      1 + ((s + 1) * (max 1 (2 * pairs.card)) ^ s) * (1 + s * M) := by
  have htests (c : ProhibitedCatalog pairs h s) : Fintype.card (ProhibitedWordTests c) ≤ s * M :=
    card_prohibitedWordTests_le c (fun a ha => hM _ (c.property.1.2.2.1 a ha))
  have hcatalog : Fintype.card (ProhibitedCatalog pairs h s) ≤
      (s + 1) * (max 1 (2 * pairs.card)) ^ s :=
    (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
      (card_boundedStepWords_le pairs s)
  rw [prohibitedCircuit_size]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _c : ProhibitedCatalog pairs h s, (1 + s * M) :=
      sum_le_sum (fun c _ => Nat.add_le_add_left (htests c) 1)
    _ = Fintype.card (ProhibitedCatalog pairs h s) * (1 + s * M) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hcatalog

end TwoPointCorrelations

end OAI
