import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalCoarse
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMultiplicativeReduction

namespace OAI

/-! Multiplication outside the selected prime bands preserves the typical
mask. The resulting identity uses the unmasked factor on the left: the
typical coefficient itself need not be multiplicative. In particular, the
complete part can be extracted at every power of an outside prime, without
a coprimality condition on the remaining argument. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrtPrimeAvoids_prime_outside (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) {p : ℕ} (hp : p.Prime) (hpout : p ∉ P) :
    mrtPrimeAvoids P p := by
  intro q hq hqp
  have he : q = p := (Nat.prime_dvd_prime_iff_eq (hP q hq) hp).mp hqp
  exact hpout (he ▸ hq)

lemma mrtPrimeAvoids_pow (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {d : ℕ} (hd : mrtPrimeAvoids P d) (k : ℕ) :
    mrtPrimeAvoids P (d ^ k) := by
  induction k with
  | zero =>
    intro p hp hdiv
    exact (hP p hp).ne_one (Nat.eq_one_of_dvd_one (by simpa only [pow_zero] using hdiv))
  | succ k ih =>
    rw [pow_succ']
    exact (mrtPrimeAvoids_mul P hP d (d ^ k)).mpr ⟨hd, ih⟩

/-- Extract an avoiding factor from a completely multiplicative coefficient,
while keeping the same typical mask on the cofactor. -/
theorem mrtTypicalCoefficient_mul_of_avoids {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b)
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (havoid : mrtPrimeAvoids (J.biUnion P) d) :
    mrtTypicalCoefficient J P F (d * n) = F d * mrtTypicalCoefficient J P F n := by
  unfold mrtTypicalCoefficient
  rw [mrtTypical_mul_of_avoids J P hP havoid n]
  split_ifs
  · exact hF d n hd hn
  · simp only [mul_zero]

theorem mrtTypicalComplete_mul_of_avoids {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (havoid : mrtPrimeAvoids (J.biUnion P) d) :
    mrtTypicalCoefficient J P (mrtCompletePart F) (d * n) =
      mrtCompletePart F d * mrtTypicalCoefficient J P (mrtCompletePart F) n := by
  exact mrtTypicalCoefficient_mul_of_avoids J P hP (mrtCompletePart F)
    (fun _ _ ha hb => mrtCompletePart_mul F ha hb) hd hn havoid

/-- Prime powers outside the bands can be extracted even when the prime
also divides the cofactor. -/
theorem mrtTypicalComplete_prime_pow_outside {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ q ∈ P j, q.Prime)
    (F : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (hpout : p ∉ J.biUnion P)
    (k n : ℕ) (hn : 0 < n) :
    mrtTypicalCoefficient J P (mrtCompletePart F) (p ^ k * n) =
      F p ^ k * mrtTypicalCoefficient J P (mrtCompletePart F) n := by
  have hprime : ∀ q ∈ J.biUnion P, q.Prime := by
    intro q hq
    obtain ⟨j, hj, hqj⟩ := mem_biUnion.mp hq
    exact hP j hj q hqj
  have ha := mrtPrimeAvoids_prime_outside (J.biUnion P) hprime hp hpout
  rw [mrtTypicalComplete_mul_of_avoids J P hP F (pow_pos hp.pos k) hn
    (mrtPrimeAvoids_pow (J.biUnion P) hprime ha k), mrtCompletePart_prime_pow F hp k]

/-- A real upper endpoint for all selected bands discharges the outside
condition used in the truncated prime convolution. -/
theorem mrtTypicalComplete_prime_pow_above {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ q ∈ P j, q.Prime)
    {U : ℝ} (hupper : ∀ j ∈ J, ∀ q ∈ P j, (q : ℝ) ≤ U)
    (F : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (hUp : U < (p : ℝ))
    (k n : ℕ) (hn : 0 < n) :
    mrtTypicalCoefficient J P (mrtCompletePart F) (p ^ k * n) =
      F p ^ k * mrtTypicalCoefficient J P (mrtCompletePart F) n := by
  apply mrtTypicalComplete_prime_pow_outside J P hP F hp _ k n hn
  intro hmem
  obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hmem
  exact (not_le_of_gt hUp) (hupper j hj p hpj)

end TwoPointCorrelations

end OAI
