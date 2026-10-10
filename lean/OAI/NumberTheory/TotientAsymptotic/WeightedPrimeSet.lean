import OAI.NumberTheory.TotientAsymptotic.PrimeInterval
import OAI.NumberTheory.TotientAsymptotic.LowerPrimeCutoff
import OAI.NumberTheory.TotientAsymptotic.WeightedIntervalGeometry

namespace OAI

noncomputable section
open scoped Topology Classical
open Filter
namespace TotientAsymptotic

def intervalHeads (x : ℝ) (k D A : ℕ) : Finset ℕ :=
  (shiftedPrimeSet x x D).filter (fun p : ℕ =>
    (k : ℝ)*x < (p*A : ℕ) ∧ (p*A : ℕ) ≤ (k+1 : ℝ)*x)

lemma mem_primeInterval {l u : ℝ} (hu : 0 ≤ u) (p : ℕ) :
    p ∈ primeInterval l u ↔ p.Prime ∧ l < p ∧ (p : ℝ) ≤ u := by
  simp only [primeInterval,Finset.mem_filter,Nat.mem_primesLE,Nat.le_floor_iff hu]
  tauto

lemma intervalHeads_eq_cutoff {x : ℝ} {k D A : ℕ}
    (hx : 0 ≤ x) (hD : 0 < D) (hA : 0 < A) :
    intervalHeads x k D A =
      (primeInterval ((k : ℝ)*x/A) (min (1+x/D) ((k+1 : ℝ)*x/A))).filter
        (fun p : ℕ => x^(9/10 : ℝ) ≤ p) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hu : 0 ≤ min (1+x/D) ((k+1 : ℝ)*x/A) := le_min (by positivity) (by positivity)
  ext p
  rw [intervalHeads,Finset.mem_filter,Finset.mem_filter,mem_shiftedPrimeSet hx hD,mem_primeInterval hu]
  by_cases hp : p.Prime
  · simp only [hp,true_and]
    have hv : (((p-1)*D : ℕ) : ℝ) ≤ x ↔ (p : ℝ) ≤ 1+x/D := by
      rw [Nat.cast_mul,Nat.cast_sub hp.one_lt.le,Nat.cast_one]
      rw [← le_div_iff₀ hD0]
      constructor <;> intro h <;> linarith
    simp only [Nat.cast_mul] at hv
    simp only [hv,Nat.cast_mul,le_min_iff,div_lt_iff₀ hA0,le_div_iff₀ hA0]
    tauto
  · simp [hp]

lemma finite_prime_cutoff_error {x : ℝ} (hx : 0 ≤ x) (S : Finset ℕ) :
    |((S.filter (fun p : ℕ => x^(9/10 : ℝ) ≤ p)).card : ℝ)-S.card| ≤ x^(9/10 : ℝ)+1 := by
  let E := S.filter (fun p : ℕ => ¬x^(9/10 : ℝ) ≤ p)
  have he : E.card ≤ ⌊x^(9/10 : ℝ)⌋₊+1 := by
    apply (Finset.card_le_card (t := Finset.range (⌊x^(9/10 : ℝ)⌋₊+1)) ?_).trans_eq (Finset.card_range _)
    intro p hp
    have ht := lt_of_not_ge (Finset.mem_filter.mp hp).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ht.le))
  have hs := Finset.card_filter_add_card_filter_not (s := S) (fun p : ℕ => x^(9/10 : ℝ) ≤ p)
  have hsR := congrArg (fun n : ℕ => (n : ℝ)) hs
  rw [Nat.cast_add] at hsR
  change ((S.filter (fun p : ℕ => x^(9/10 : ℝ) ≤ p)).card : ℝ)+(E.card : ℝ)=S.card at hsR
  rw [show ((S.filter (fun p : ℕ => x^(9/10 : ℝ) ≤ p)).card : ℝ)-S.card=-(E.card : ℝ) by linarith,
    abs_neg,abs_of_nonneg (Nat.cast_nonneg _)]
  have heR : (E.card : ℝ) ≤ (⌊x^(9/10 : ℝ)⌋₊ : ℝ)+1 := by exact_mod_cast he
  exact heR.trans (by linarith [Nat.floor_le (Real.rpow_nonneg hx (9/10 : ℝ))])

end TotientAsymptotic

end

end OAI
