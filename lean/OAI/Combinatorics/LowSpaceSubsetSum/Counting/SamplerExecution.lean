import OAI.Combinatorics.LowSpaceSubsetSum.Counting.SamplerAttempts
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FiniteProductSamplerCoupling

namespace OAI

/-! # Counter-carrying execution of finite sampler compositions

The value fields agree with the bounded samplers. A dependent bind
does not execute its second sampler after first-stage exhaustion. Counts are
retained on every branch, including failure; ideal backup values do not add
candidate reads to the bounded execution.
-/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SamplerExecution

structure Trace (α : Type*) where
  value : Option α
  reads : ℕ
  tests : ℕ

structure Execution {α : Type*} [Fintype α] (S : SamplerCoupling α) where
  run : S.Seed → Trace α
  value_eq : ∀ s, (run s).value = S.bounded s

theorem Execution.ideal_eq_of_some {α : Type*} [Fintype α] {S : SamplerCoupling α}
    (X : Execution S) (s : S.Seed) (a : α) (h : (X.run s).value = some a) :
    S.ideal s = a := by
  rw [X.value_eq] at h
  rcases S.agrees s with hf | hs
  · simp only [hf, reduceCtorEq] at h
  · exact Option.some.inj (hs.symm.trans h)

def Execution.Bounded {α : Type*} [Fintype α] {S : SamplerCoupling α}
    (X : Execution S) (reads tests : ℕ) : Prop :=
  ∀ s, (X.run s).reads ≤ reads ∧ (X.run s).tests ≤ tests

theorem Execution.Bounded.mono {α : Type*} [Fintype α] {S : SamplerCoupling α}
    {X : Execution S} {r t r' t' : ℕ} (h : X.Bounded r t)
    (hr : r ≤ r') (ht : t ≤ t') : X.Bounded r' t' :=
  fun s => ⟨(h s).1.trans hr, (h s).2.trans ht⟩

def cast {α : Type*} [Fintype α] {S T : SamplerCoupling α}
    (h : S = T) (X : Execution S) : Execution T := h ▸ X

theorem cast_bounded {α : Type*} [Fintype α] {S T : SamplerCoupling α}
    (h : S = T) (X : Execution S) {r t : ℕ} (hx : X.Bounded r t) :
    (cast h X).Bounded r t := by
  subst T
  exact hx

variable {α β : Type} [Fintype α] [Fintype β]

def pure (a : α) : Execution (SamplerCoupling.pure a) where
  run _ := ⟨some a, 0, 0⟩
  value_eq _ := rfl

theorem pure_bounded (a : α) : (pure a).Bounded 0 0 := fun _ => ⟨le_rfl, le_rfl⟩

def map {S : SamplerCoupling α} (X : Execution S) (f : α → β) :
    Execution (S.map f) where
  run s := let r := X.run s; ⟨r.value.map f, r.reads, r.tests⟩
  value_eq s := congrArg (Option.map f) (X.value_eq s)

theorem map_bounded {S : SamplerCoupling α} (X : Execution S) (f : α → β)
    {r t : ℕ} (h : X.Bounded r t) : (map X f).Bounded r t := h

def bind {S : SamplerCoupling α} (X : Execution S)
    (B : α → Type) [∀ a, Fintype (B a)] (T : ∀ a, SamplerCoupling (B a))
    (Y : ∀ a, Execution (T a)) : Execution (S.bind B T) where
  run s :=
    let first := X.run s.1
    if first.value = none then ⟨none, first.reads, first.tests⟩ else
      let second := (Y (S.ideal s.1)).run s.2
      ⟨second.value.map (fun b => ⟨S.ideal s.1, b⟩),
        first.reads + second.reads, first.tests + second.tests⟩
  value_eq s := by
    simp only [X.value_eq, SamplerCoupling.bind]
    split
    · rfl
    · exact congrArg (Option.map _) ((Y (S.ideal s.1)).value_eq s.2)

/-- On acceptance, the dependent second stage is exactly the stage indexed
by the value actually returned by the first stage. The cast changes only
its type, so no ideal backup value is needed to choose a runtime branch. -/
theorem bind_run_some {S : SamplerCoupling α} (X : Execution S)
    (B : α → Type) [∀ a, Fintype (B a)] (T : ∀ a, SamplerCoupling (B a))
    (Y : ∀ a, Execution (T a)) (s : S.Seed) (a : α)
    (h : (X.run s).value = some a) (t : (T (S.ideal s)).Seed) :
    let ha := X.ideal_eq_of_some s a h
    let second := (Y a).run (ha ▸ t)
    (bind X B T Y).run ⟨s, t⟩ =
      ⟨second.value.map (fun b => ⟨a, b⟩), (X.run s).reads + second.reads,
        (X.run s).tests + second.tests⟩ := by
  dsimp only
  have ha := X.ideal_eq_of_some s a h
  subst a
  simp only [bind, h, reduceCtorEq, ↓reduceIte]

theorem bind_bounded {S : SamplerCoupling α} (X : Execution S)
    (B : α → Type) [∀ a, Fintype (B a)] (T : ∀ a, SamplerCoupling (B a))
    (Y : ∀ a, Execution (T a)) {r t r' t' : ℕ}
    (hX : X.Bounded r t) (hY : ∀ a, (Y a).Bounded r' t') :
    (bind X B T Y).Bounded (r + r') (t + t') := by
  intro s
  have hx := hX s.1
  have hy := hY (S.ideal s.1) s.2
  simp only [bind]
  split
  · exact ⟨hx.1.trans (Nat.le_add_right _ _), hx.2.trans (Nat.le_add_right _ _)⟩
  · exact ⟨Nat.add_le_add hx.1 hy.1, Nat.add_le_add hx.2 hy.2⟩

def prod {S : SamplerCoupling α} {T : SamplerCoupling β}
    (X : Execution S) (Y : Execution T) : Execution (S.prod T) :=
  map (bind X (fun _ => β) (fun _ => T) (fun _ => Y)) (Equiv.sigmaEquivProd α β)

theorem prod_bounded {S : SamplerCoupling α} {T : SamplerCoupling β}
    (X : Execution S) (Y : Execution T) {r t r' t' : ℕ}
    (hX : X.Bounded r t) (hY : Y.Bounded r' t') :
    (prod X Y).Bounded (r + r') (t + t') :=
  map_bounded _ _ (bind_bounded X _ _ (fun _ => Y) hX (fun _ => hY))

def pi : (k : ℕ) → (A : Fin k → Type) → [∀ i, Fintype (A i)] →
    (S : ∀ i, SamplerCoupling (A i)) → (∀ i, Execution (S i)) →
      Execution (SamplerCoupling.pi k A S)
  | 0, _, _, _, _ => pure (fun i => Fin.elim0 i)
  | k + 1, A, _, S, X =>
      map (prod (X 0) (pi k (fun i => A i.succ) (fun i => S i.succ)
        (fun i => X i.succ))) (Fin.consEquiv A)

theorem pi_bounded : ∀ (k : ℕ) (A : Fin k → Type) [∀ i, Fintype (A i)]
    (S : ∀ i, SamplerCoupling (A i)) (X : ∀ i, Execution (S i))
    (r t : Fin k → ℕ), (∀ i, (X i).Bounded (r i) (t i)) →
      (pi k A S X).Bounded (∑ i, r i) (∑ i, t i) := by
  intro k
  induction k with
  | zero =>
    intro A _ S X r t _
    simpa only [pi, SamplerCoupling.pi, Fin.sum_univ_zero] using
      pure_bounded (fun i : Fin 0 => (Fin.elim0 i : A i))
  | succ k ih =>
    intro A _ S X r t h
    simpa only [pi, SamplerCoupling.pi, Fin.sum_univ_succ] using map_bounded _ _
      (prod_bounded (X 0) _ (h 0)
        (ih (fun i => A i.succ) (fun i => S i.succ) (fun i => X i.succ)
          (fun i => r i.succ) (fun i => t i.succ) (fun i => h i.succ)))

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]

def certify (A : Ω → Prop) (o : Option Ω) (h : ∀ a, o = some a → A a) :
    Option {a : Ω // A a} :=
  match o with
  | none => none
  | some a => some ⟨a, h a rfl⟩

omit [Fintype Ω] [Nonempty Ω] in
theorem certify_firstAccept (A : Ω → Prop) [DecidablePred A] (N : ℕ)
    (f : Fin N → Ω) (o : Option Ω) (ho : o = firstAccept A N f)
    (h : ∀ a, o = some a → A a) :
    certify A o h = firstAcceptSubtype A N f := by
  subst o
  unfold certify
  unfold firstAcceptSubtype
  split <;> split <;> simp_all

def test (A : Ω → Prop) [DecidablePred A] [Nonempty {a : Ω // A a}]
    (evaluator : Ω → Bool × ℕ) (he : ∀ a, (evaluator a).1 = true ↔ A a)
    (N : ℕ) : Execution (firstAcceptCoupling A N) where
  run s :=
    let r := SamplerAttempts.runCostAcc evaluator N s.1 0 0
    have hv : r.1 = firstAccept A N s.1 := by
      rw [SamplerAttempts.runCostAcc_value]
      congr 1
      funext a
      exact propext (he a)
    ⟨certify A r.1 (fun a ha => firstAccept_some_eligible A N s.1 (hv.symm.trans ha)),
      r.2.1, r.2.2⟩
  value_eq s := certify_firstAccept A N s.1 _ (by
    rw [SamplerAttempts.runCostAcc_value]
    congr 1
    funext a
    exact propext (he a)) _

theorem test_bounded (A : Ω → Prop) [DecidablePred A] [Nonempty {a : Ω // A a}]
    (evaluator : Ω → Bool × ℕ) (he : ∀ a, (evaluator a).1 = true ↔ A a)
    (N K : ℕ) (hK : ∀ a, (evaluator a).2 ≤ K) :
    (test A evaluator he N).Bounded N (N * K) := by
  intro s
  simpa only [test, Nat.zero_add] using
    SamplerAttempts.runCostAcc_bounds evaluator K hK N s.1 0 0

def range {D : ℕ} (hD : 1 < D) (n : ℕ) : Execution (rangeCoupling hD n) := by
  let : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
  let : Nonempty {x : Fin (2 ^ Nat.clog 2 D) // rangeEligible D x} :=
    ⟨(rangeEligibleEquiv D).symm ⟨0, by omega⟩⟩
  exact map (test (rangeEligible D) (fun a => (decide (rangeEligible D a), 0))
    (fun _ => by simp only [decide_eq_true_eq]) (n ^ 3)) (rangeEligibleEquiv D)

theorem range_bounded {D : ℕ} (hD : 1 < D) (n : ℕ) :
    (range hD n).Bounded (n ^ 3) 0 := by
  let : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
  let : Nonempty {x : Fin (2 ^ Nat.clog 2 D) // rangeEligible D x} :=
    ⟨(rangeEligibleEquiv D).symm ⟨0, by omega⟩⟩
  unfold range
  apply map_bounded
  simpa only [Nat.mul_zero] using test_bounded (rangeEligible D)
    (fun a => (decide (rangeEligible D a), 0)) (fun _ => by simp only [decide_eq_true_eq])
      (n ^ 3) 0 (fun _ => le_rfl)

def prime {ell : ℕ} (hell : 4 ≤ ell) (n : ℕ) : Execution (primeCoupling hell n) := by
  let : Nonempty ↥(primeRange ell) := (primeRange_nonempty hell).to_subtype
  let : Nonempty {x : Fin (2 ^ ell) // primeEligible ell x} :=
    ⟨(primeEligibleEquiv hell).symm (Classical.choice inferInstance)⟩
  exact map (test (primeEligible ell) (SamplerAttempts.primeTest ell)
    (SamplerAttempts.primeTest_correct ell) (n ^ 3)) (primeEligibleEquiv hell)

theorem prime_bounded {ell : ℕ} (hell : 4 ≤ ell) (n : ℕ) :
    (prime hell n).Bounded (n ^ 3) (n ^ 3 * 2 ^ ((ell + 1) / 2)) := by
  let : Nonempty ↥(primeRange ell) := (primeRange_nonempty hell).to_subtype
  let : Nonempty {x : Fin (2 ^ ell) // primeEligible ell x} :=
    ⟨(primeEligibleEquiv hell).symm (Classical.choice inferInstance)⟩
  unfold prime
  apply map_bounded
  exact test_bounded (primeEligible ell) (SamplerAttempts.primeTest ell)
    (SamplerAttempts.primeTest_correct ell) (n ^ 3) _
      (SamplerAttempts.divisorsBits_tests ell)

def fin (n D : ℕ) [NeZero D] : Execution (finCoupling n D) :=
  if h : 1 < D then cast (by simp only [finCoupling, dite_eq_left h]) (range h n)
  else cast (by simp only [finCoupling, dite_eq_right h])
    (pure (⟨0, Nat.pos_of_ne_zero (NeZero.ne D)⟩ : Fin D))

theorem fin_bounded (n D : ℕ) [NeZero D] : (fin n D).Bounded (n ^ 3) 0 := by
  by_cases h : 1 < D
  · simp only [fin, dite_eq_left h]
    exact cast_bounded _ _ (range_bounded h n)
  · simp only [fin, dite_eq_right h]
    exact cast_bounded _ _ ((pure_bounded _).mono (Nat.zero_le _) le_rfl)

def permutation (n : ℕ) : (k : ℕ) → Execution (permutationCoupling n k)
  | 0 => pure (Equiv.refl _)
  | k + 1 => map (prod (fin n (k + 1)) (permutation n k)) Equiv.Perm.decomposeFin.symm

theorem permutation_bounded (n k : ℕ) :
    (permutation n k).Bounded (k * n ^ 3) 0 := by
  induction k with
  | zero => simpa only [permutation, permutationCoupling, Nat.zero_mul] using
      pure_bounded (Equiv.refl (Fin 0))
  | succ k ih =>
    simpa only [permutation, permutationCoupling, Nat.succ_mul, Nat.add_comm,
      Nat.zero_add] using
      map_bounded _ _ (prod_bounded _ _ (fin_bounded n (k + 1)) ih)

def finiteChoice (n : ℕ) (A : Type) [Fintype A] [Nonempty A] :
    Execution (finiteChoiceCoupling n A) :=
  map (fin n (Fintype.card A)) (Fintype.equivFin A).symm

theorem finiteChoice_bounded (n : ℕ) (A : Type) [Fintype A] [Nonempty A] :
    (finiteChoice n A).Bounded (n ^ 3) 0 := map_bounded _ _ (fin_bounded _ _)

def finitePermutation (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    Execution (finitePermutationCoupling n A) :=
  map (permutation n (Fintype.card A)) (Equiv.permCongr (Fintype.equivFin A).symm)

theorem finitePermutation_bounded (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] :
    (finitePermutation n A).Bounded (Fintype.card A * n ^ 3) 0 :=
  map_bounded _ _ (permutation_bounded _ _)

def coloring (n : ℕ) {A K : Type} [Fintype A] [DecidableEq A]
    [Fintype K] [DecidableEq K] {t : K → ℕ} (f : MatchingSmoothing.Colorings A K t) :
    Execution (coloringCoupling n f) :=
  map (finitePermutation n A) (coloringOfPermutation f)

theorem coloring_bounded (n : ℕ) {A K : Type} [Fintype A] [DecidableEq A]
    [Fintype K] [DecidableEq K] {t : K → ℕ} (f : MatchingSmoothing.Colorings A K t) :
    (coloring n f).Bounded (Fintype.card A * n ^ 3) 0 :=
  map_bounded _ _ (finitePermutation_bounded _ _)

end SamplerExecution
end LowSpaceSubsetSum

end

end OAI
