import OAI.NumberTheory.Ostmann.Characters.HigherBiasSelection
import OAI.NumberTheory.Ostmann.Construction.RepeatedPeriod
import OAI.NumberTheory.Ostmann.Construction.RepeatedPhysical

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Characters
open Construction

def phasedCharacter {q : ℕ} (χ : MulChar (ZMod q) ℂ) (a : ZMod q)
    (z : ℂ) (x : ZMod q) : ℂ := z*χ (x-a)

theorem phasedCharacter_sum_zero {q : ℕ} [NeZero q]
    (χ : MulChar (ZMod q) ℂ) (hχ : χ ≠ 1) (a : ZMod q) (z : ℂ) :
    ∑ x : ZMod q, phasedCharacter χ a z x = 0 := by
  unfold phasedCharacter
  rw [← Finset.mul_sum]
  have hh := (Equiv.subRight a).sum_comp χ
  change (∑ i, χ (i-a)) = ∑ i, χ i at hh
  rw [hh, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

theorem phasedCharacter_norm_le_one {q : ℕ} [Fact q.Prime]
    (χ : MulChar (ZMod q) ℂ) (a : ZMod q) {z : ℂ} (hz : ‖z‖ ≤ 1) (x : ZMod q) :
    ‖phasedCharacter χ a z x‖ ≤ 1 := by
  rw [phasedCharacter, norm_mul]
  exact (mul_le_mul hz (norm_character_le_one χ _) (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

theorem phasedCharacter_sq_sum_le {q : ℕ} [Fact q.Prime]
    (χ : MulChar (ZMod q) ℂ) (a : ZMod q) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∑ x : ZMod q, ‖phasedCharacter χ a z x‖^2) ≤ (q : ℝ) := by
  calc
    _ ≤ ∑ _x : ZMod q, (1 : ℝ) := Finset.sum_le_sum (fun x _ => by
      have hh := phasedCharacter_norm_le_one χ a hz x
      nlinarith [norm_nonneg (phasedCharacter χ a z x)])
    _ = _ := by simp

def occurrenceLocalTest {ι : Type*} (p : ι → ℕ)
    (F : ι → (q : ℕ) → ZMod q → ℂ) (i : ι) (q : ℕ) (x : ZMod q) : ℂ :=
  if p i = q then F i q x else 0

theorem phased_character_tuple_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (χ : ι → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : ι → (q : ℕ) → ZMod q) (z : ι → ℕ → ℂ)
    (hχ : ∀ i, χ i (p i) ≠ 1) (hz : ∀ i, ‖z i (p i)‖ ≤ 1)
    {X : ℝ} (hX : 0 < X)
    (hperiod : ((∏ q : ↥(tupleDistinctPrimes p), (q : ℕ) : ℕ) : ℝ)/4 < X) :
    ‖(∑' n : ℤ, (∏ i, phasedCharacter (χ i (p i)) (a i (p i)) (z i (p i))
      (n : ZMod (p i)))*SchwartzCutoff.psi ((n : ℝ)/X))/(Real.sqrt X : ℂ)‖ ≤
      Real.sqrt X*‖𝓕 SchwartzCutoff.psi 0‖*
        (Real.sqrt (∏ i, p i : ℕ)/(∏ q : ↥(tupleDistinctPrimes p), (q : ℕ) : ℕ)) := by
  classical
  let F := fun i q => phasedCharacter (χ i q) (a i q) (z i q)
  let (q : ↥(tupleDistinctPrimes p)) : NeZero (q : ℕ) :=
    ⟨(tupleDistinctPrimes_prime p hp q).ne_zero⟩
  have hzero (q : ↥(tupleDistinctPrimes p)) (i : ι) :
      (∑ x : ZMod (q : ℕ), occurrenceLocalTest p F i q x) = 0 := by
    by_cases hi : p i = (q : ℕ)
    · simp only [occurrenceLocalTest, hi, ite_true]
      exact phasedCharacter_sum_zero _ (hi ▸ hχ i) _ _
    · simp [occurrenceLocalTest, hi]
  have hsq (q : ↥(tupleDistinctPrimes p)) (i : ι) :
      (∑ x : ZMod (q : ℕ), ‖occurrenceLocalTest p F i q x‖^2) ≤ (q : ℝ) := by
    by_cases hi : p i = (q : ℕ)
    · let : Fact (q : ℕ).Prime := ⟨tupleDistinctPrimes_prime p hp q⟩
      simp only [occurrenceLocalTest, hi, ite_true]
      exact phasedCharacter_sq_sum_le _ _ (hi ▸ hz i)
    · simp [occurrenceLocalTest, hi]
  have hh := centered_tuple_physical_bound p hp (occurrenceLocalTest p F) hzero hsq hX hperiod
  simpa only [occurrenceLocalTest, ite_true, F] using hh

theorem phased_character_tuple_singleton_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (χ : ι → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : ι → (q : ℕ) → ZMod q) (z : ι → ℕ → ℂ)
    (hχ : ∀ i, χ i (p i) ≠ 1)
    (q : ↥(tupleDistinctPrimes p)) (hq : (tuplePrimeFiber p q).card = 1)
    {X : ℝ} (hX : 0 < X)
    (hperiod : ((∏ q : ↥(tupleDistinctPrimes p), (q : ℕ) : ℕ) : ℝ)/4 < X) :
    (∑' n : ℤ, (∏ i, phasedCharacter (χ i (p i)) (a i (p i)) (z i (p i))
      (n : ZMod (p i)))*SchwartzCutoff.psi ((n : ℝ)/X)) = 0 := by
  classical
  let F := fun i q => phasedCharacter (χ i q) (a i q) (z i q)
  let (q : ↥(tupleDistinctPrimes p)) : NeZero (q : ℕ) :=
    ⟨(tupleDistinctPrimes_prime p hp q).ne_zero⟩
  let : NeZero (∏ q : ↥(tupleDistinctPrimes p), (q : ℕ)) :=
    ⟨(Finset.prod_pos (fun q _ => (tupleDistinctPrimes_prime p hp q).pos)).ne'⟩
  have hcop : Pairwise (fun q r : ↥(tupleDistinctPrimes p) => (q : ℕ).Coprime (r : ℕ)) := by
    intro q r hqr
    exact (Nat.coprime_primes (tupleDistinctPrimes_prime p hp q)
      (tupleDistinctPrimes_prime p hp r)).mpr (fun he => hqr (Subtype.ext he))
  have hzero (i : ι) : (∑ x : ZMod (q : ℕ), occurrenceLocalTest p F i q x) = 0 := by
    by_cases hi : p i = (q : ℕ)
    · simp only [occurrenceLocalTest, hi, ite_true]
      exact phasedCharacter_sum_zero _ (hi ▸ hχ i) _ _
    · simp [occurrenceLocalTest, hi]
  have hh := crt_singleton_cutoff_zero (fun q : ↥(tupleDistinctPrimes p) => (q : ℕ))
    hcop (fun q => groupedLocalTest p (occurrenceLocalTest p F) q) q
    (groupedLocalTest_sum_zero_singleton p (occurrenceLocalTest p F) hq hzero) hX hperiod
  simp_rw [groupedLocalTest_product] at hh
  simpa only [occurrenceLocalTest, ite_true, F] using hh

end Ostmann.Characters

end

end OAI
