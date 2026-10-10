import OAI.Geometry.PeriodicTiling.EncodingParameters
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Sum.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose

namespace OAI

universe uι

noncomputable section

namespace PeriodicTilingThree
namespace EncodingPrimeSelection

private def nextPrime (bound : ℕ) : ℕ :=
  Classical.choose (Nat.exists_infinite_primes (bound + 1))

private theorem nextPrime_prime (bound : ℕ) : Nat.Prime (nextPrime bound) :=
  (Classical.choose_spec (Nat.exists_infinite_primes (bound + 1))).2

private theorem nextPrime_gt (bound : ℕ) : bound < nextPrime bound := by
  have h := (Classical.choose_spec (Nat.exists_infinite_primes (bound + 1))).1
  exact h

private def primeSequence (bound : ℕ) : ℕ → ℕ
  | 0 => nextPrime bound
  | n + 1 => nextPrime (primeSequence bound n)

private theorem primeSequence_strictMono (bound : ℕ) :
    StrictMono (primeSequence bound) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact nextPrime_gt _

private theorem primeSequence_prime (bound n : ℕ) :
    Nat.Prime (primeSequence bound n) := by
  cases n with
  | zero => exact nextPrime_prime _
  | succ n => exact nextPrime_prime _

private theorem primeSequence_gt (bound n : ℕ) : bound < primeSequence bound n :=
  lt_of_lt_of_le (nextPrime_gt bound)
    ((primeSequence_strictMono bound).monotone (Nat.zero_le n))

theorem exists_prime_family (ι : Type uι) [Fintype ι] (bound : ℕ) :
    ∃ f : ι → ℕ, Function.Injective f ∧
      ∀ i, Nat.Prime (f i) ∧ bound < f i := by
  let e := Fintype.equivFin ι
  refine ⟨fun i => primeSequence bound (e i).val, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    apply Fin.ext
    exact (primeSequence_strictMono bound).injective hij
  · intro i
    exact ⟨primeSequence_prime _ _, primeSequence_gt _ _⟩

theorem exists_positive_combination {a b r : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 < a) (hb : 1 < b) (hr : a * b + a + b < r) :
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ r = A * a + B * b := by
  have hmem : r - a - b ∈ AddSubmonoid.closure ({a, b} : Set ℕ) := by
    by_contra hnot
    have hle := (frobeniusNumber_pair hab ha hb).2 hnot
    have hbound : a * b - a - b ≤ a * b :=
      (Nat.sub_le (a * b - a) b).trans (Nat.sub_le (a * b) a)
    omega
  obtain ⟨A, B, hAB⟩ := (AddSubmonoid.mem_closure_pair a b (r - a - b)).mp hmem
  simp only [smul_eq_mul] at hAB
  refine ⟨A + 1, B + 1, by omega, by omega, ?_⟩
  calc
    r = (r - a - b) + a + b := by omega
    _ = (A * a + B * b) + a + b := by rw [hAB]
    _ = (A + 1) * a + (B + 1) * b := by ring

private abbrev UsefulTag (p : ℕ) := Channel p ⊕ Channel p
private abbrev FreshUsefulTag (p : ℕ) := Column p ⊕ Channel p
private abbrev DigitTag (p : ℕ) := Σ i, Label p i

private def usefulTagEquiv (p : ℕ) :
    UsefulTag p ≃ Fin 2 ⊕ FreshUsefulTag p :=
  (Equiv.sumCongr (Equiv.sumComm (Column p) (Fin 2))
    (Equiv.refl (Channel p))).trans (Equiv.sumAssoc (Fin 2) (Column p) (Channel p))

private def usefulPrime {p : ℕ} (f : FreshUsefulTag p → ℕ) : UsefulTag p → ℕ :=
  Sum.elim (fun t : Fin 2 => t.val + 2) f ∘ usefulTagEquiv p

private theorem usefulPrime_injective {p : ℕ} {f : FreshUsefulTag p → ℕ}
    (hf : Function.Injective f) (hlarge : ∀ t, 3 < f t) :
    Function.Injective (usefulPrime f) := by
  have hseed : Function.Injective (fun t : Fin 2 => t.val + 2) := by
    intro t u htu
    apply Fin.ext
    change t.val + 2 = u.val + 2 at htu
    exact Nat.add_right_cancel htu
  have hsep : ∀ t : Fin 2, ∀ i, t.val + 2 ≠ f i := by
    intro t i heq
    have ht := t.isLt
    have hi := hlarge i
    omega
  exact (hseed.sumElim hf hsep).comp (usefulTagEquiv p).injective

private theorem usefulPrime_prime {p : ℕ} {f : FreshUsefulTag p → ℕ}
    (hf : ∀ i, Nat.Prime (f i)) (i : UsefulTag p) :
    Nat.Prime (usefulPrime f i) := by
  rcases i with (i | t) | i
  · exact hf (.inl i)
  · change Nat.Prime (t.val + 2)
    fin_cases t
    · exact Nat.prime_two
    · exact Nat.prime_three
  · exact hf (.inr i)

private def attachDigits {p : ℕ} (f : UsefulTag p → ℕ) (g : DigitTag p → ℕ) :
    PrimeTag p → ℕ :=
  Sum.elim f g ∘ (Equiv.sumAssoc (Channel p) (Channel p) (DigitTag p)).symm

private theorem attachDigits_injective {p : ℕ}
    {f : UsefulTag p → ℕ} {g : DigitTag p → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hsep : ∀ i j, f i ≠ g j) : Function.Injective (attachDigits f g) :=
  (hf.sumElim hg hsep).comp
    (Equiv.sumAssoc (Channel p) (Channel p) (DigitTag p)).symm.injective

theorem exists_parameters {p : ℕ} (hp : Nat.Prime p) (hlarge : 200 < p) :
    Nonempty (EncodingParameters p) := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨f, hfinj, hf⟩ := exists_prime_family (FreshUsefulTag p) (p ^ 4 + p + 3)
  let useful : UsefulTag p → ℕ := usefulPrime f
  have huseful_prime : ∀ i, Nat.Prime (useful i) :=
    usefulPrime_prime (fun i => (hf i).1)
  have huseful_inj : Function.Injective useful := by
    apply usefulPrime_injective hfinj
    intro i
    have := (hf i).2
    omega
  have huseful_ne_p : ∀ i, useful i ≠ p := by
    intro i
    rcases i with (i | t) | i
    · change f (.inl i) ≠ p
      have := (hf (.inl i)).2
      omega
    · change t.val + 2 ≠ p
      have := t.isLt
      omega
    · change f (.inr i) ≠ p
      have := (hf (.inr i)).2
      omega
  let threshold : Channel p → ℕ := fun i =>
    useful (.inl i) * useful (.inr i) + useful (.inl i) + useful (.inr i)
  let bound := p + Finset.univ.sup useful + Finset.univ.sup threshold
  obtain ⟨g, hginj, hg⟩ := exists_prime_family (DigitTag p) bound
  have hseparate : ∀ i j, useful i < g j := by
    intro i j
    have hi : useful i ≤ Finset.univ.sup useful := Finset.le_sup (Finset.mem_univ i)
    have hj := (hg j).2
    dsimp [bound] at hj
    omega
  have hthreshold : ∀ i j, threshold i < g ⟨i, j⟩ := by
    intro i j
    have hi : threshold i ≤ Finset.univ.sup threshold :=
      Finset.le_sup (Finset.mem_univ i)
    have hj := (hg ⟨i, j⟩).2
    dsimp [bound] at hj
    omega
  have hrepresentation : ∀ i (j : Label p i), ∃ A B : ℕ,
      0 < A ∧ 0 < B ∧ g ⟨i, j⟩ = A * useful (.inl i) + B * useful (.inr i) := by
    intro i j
    have hcop : Nat.Coprime (useful (.inl i)) (useful (.inr i)) := by
      apply (Nat.coprime_primes (huseful_prime _) (huseful_prime _)).2
      intro h
      have htags := huseful_inj h
      cases htags
    exact exists_positive_combination hcop
      (huseful_prime _).one_lt (huseful_prime _).one_lt (hthreshold i j)
  choose A B hA hB hrepresentation using hrepresentation
  refine ⟨{
    p_prime := hp
    p_large := hlarge
    primeAt := attachDigits useful g
    prime_isPrime := ?_
    prime_injective := attachDigits_injective huseful_inj hginj
      (fun i j => (hseparate i j).ne)
    prime_ne_p := ?_
    seed_a_eq := ?_
    seed_b_large := ?_
    blockA := A
    blockB := B
    blockA_pos := hA
    blockB_pos := hB
    digit_representation := ?_
  }⟩
  · intro t
    rcases t with i | (i | j)
    · exact huseful_prime (.inl i)
    · exact huseful_prime (.inr i)
    · exact (hg j).1
  · intro t
    rcases t with i | (i | j)
    · exact huseful_ne_p (.inl i)
    · exact huseful_ne_p (.inr i)
    · change g j ≠ p
      have hj := (hg j).2
      dsimp [bound] at hj
      omega
  · intro t
    rfl
  · intro t
    change p ^ 4 < f (.inr (.inr t))
    have ht := (hf (.inr (.inr t))).2
    omega
  · intro i j
    exact hrepresentation i j

end EncodingPrimeSelection

theorem exists_encodingParameters {p : ℕ} (hp : Nat.Prime p) (hlarge : 200 < p) :
    Nonempty (EncodingParameters p) :=
  EncodingPrimeSelection.exists_parameters hp hlarge

def encodingParameters {p : ℕ} (hp : Nat.Prime p) (hlarge : 200 < p) :
    EncodingParameters p :=
  Classical.choice (exists_encodingParameters hp hlarge)

end PeriodicTilingThree

end

end OAI
