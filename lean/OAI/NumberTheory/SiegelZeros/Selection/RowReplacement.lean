import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.NumberTheory.SiegelZeros.Differentials.InvariantDerivation

namespace OAI

namespace SiegelZeros


noncomputable section

namespace WeightedTorusJets.W19

open MvPolynomial
open scoped BigOperators
open WeightedTorusJets.W18

variable {σ R : Type*} [CommSemiring R] [Fintype σ]

theorem invariantDerivation_commute (v w : σ → R) (p : MvPolynomial σ R) :
    invariantDerivation v (invariantDerivation w p) =
      invariantDerivation w (invariantDerivation v p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial n r =>
      simp only [invariantDerivation_monomial]
      congr 1
      exact mul_left_comm _ _ _
  | add p q hp hq =>
      simp only [map_add, hp, hq]

def iteratedInvariant (v : σ → R) (a : ℕ) (p : MvPolynomial σ R) :
    MvPolynomial σ R :=
  (fun f => invariantDerivation v f)^[a] p

theorem iteratedInvariant_commute (v w : σ → R) (a b : ℕ)
    (p : MvPolynomial σ R) :
    iteratedInvariant v a (iteratedInvariant w b p) =
      iteratedInvariant w b (iteratedInvariant v a p) := by
  have h : Function.Commute (fun f => invariantDerivation v f)
      (fun f => invariantDerivation w f) := invariantDerivation_commute v w
  exact (h.iterate_iterate a b) p

theorem iteratedInvariant_monomial (v : σ → R) (a : ℕ) (n : σ →₀ ℕ) (r : R) :
    iteratedInvariant v a (monomial n r) =
      monomial n ((eigenvalue v n)^a * r) := by
  induction a with
  | zero => simp [iteratedInvariant]
  | succ a ha =>
      simp only [iteratedInvariant, Function.iterate_succ_apply'] at *
      rw [ha, invariantDerivation_monomial]
      congr 1
      rw [pow_succ]
      simp only [mul_left_comm, mul_comm]

theorem iteratedInvariant_zero (v : σ → R) (a : ℕ) :
    iteratedInvariant v a 0 = 0 := by
  induction a with
  | zero => rfl
  | succ a ha =>
      simp only [iteratedInvariant, Function.iterate_succ_apply'] at *
      rw [ha, map_zero]

theorem iteratedInvariant_add (v : σ → R) (a : ℕ) (p q : MvPolynomial σ R) :
    iteratedInvariant v a (p + q) = iteratedInvariant v a p + iteratedInvariant v a q := by
  induction a with
  | zero => rfl
  | succ a ha =>
      simp only [iteratedInvariant, Function.iterate_succ_apply'] at *
      rw [ha, map_add]

theorem iteratedInvariant_smul (v : σ → R) (a : ℕ) (c : R) (p : MvPolynomial σ R) :
    iteratedInvariant v a (c • p) = c • iteratedInvariant v a p := by
  induction a with
  | zero => rfl
  | succ a ha =>
      simp only [iteratedInvariant, Function.iterate_succ_apply'] at *
      rw [ha, Derivation.map_smul]

def mixedInvariant (v : Fin 3 → σ → R) (a : Fin 3 → ℕ)
    (p : MvPolynomial σ R) : MvPolynomial σ R :=
  iteratedInvariant (v 0) (a 0)
    (iteratedInvariant (v 1) (a 1) (iteratedInvariant (v 2) (a 2) p))

theorem mixedInvariant_zero (v : Fin 3 → σ → R) (a : Fin 3 → ℕ) :
    mixedInvariant v a 0 = 0 := by
  simp only [mixedInvariant, iteratedInvariant_zero]

theorem mixedInvariant_add (v : Fin 3 → σ → R) (a : Fin 3 → ℕ)
    (p q : MvPolynomial σ R) :
    mixedInvariant v a (p + q) = mixedInvariant v a p + mixedInvariant v a q := by
  simp only [mixedInvariant, iteratedInvariant_add]

theorem mixedInvariant_smul (v : Fin 3 → σ → R) (a : Fin 3 → ℕ)
    (c : R) (p : MvPolynomial σ R) :
    mixedInvariant v a (c • p) = c • mixedInvariant v a p := by
  simp only [mixedInvariant, iteratedInvariant_smul]

theorem mixedInvariant_sum {ι : Type*} (v : Fin 3 → σ → R) (a : Fin 3 → ℕ)
    (s : Finset ι) (p : ι → MvPolynomial σ R) :
    mixedInvariant v a (∑ i ∈ s, p i) = ∑ i ∈ s, mixedInvariant v a (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mixedInvariant_zero]
  | insert i s hi hs => simp only [Finset.sum_insert hi, mixedInvariant_add, hs]

theorem mixedInvariant_monomial (v : Fin 3 → σ → R) (a : Fin 3 → ℕ)
    (n : σ →₀ ℕ) (r : R) :
    mixedInvariant v a (monomial n r) =
      monomial n ((eigenvalue (v 0) n ^ a 0 * eigenvalue (v 1) n ^ a 1 *
        eigenvalue (v 2) n ^ a 2) * r) := by
  simp only [mixedInvariant, iteratedInvariant_monomial, mul_assoc]

theorem derivative_row_at_one (v : Fin 3 → σ → R) (a : Fin 3 → ℕ)
    (n : σ →₀ ℕ) :
    MvPolynomial.eval (fun _ => (1 : R)) (mixedInvariant v a (monomial n 1)) =
      eigenvalue (v 0) n ^ a 0 * eigenvalue (v 1) n ^ a 1 *
        eigenvalue (v 2) n ^ a 2 := by
  simp [mixedInvariant_monomial, MvPolynomial.eval_monomial]

theorem eigenvalue_map {S : Type*} [CommSemiring S] (φ : R →+* S)
    (v : σ → R) (n : σ →₀ ℕ) :
    eigenvalue (fun i => φ (v i)) n = φ (eigenvalue v n) := by
  simp [eigenvalue, map_sum, map_mul]

theorem derivative_row_endomorphisms (g : Fin 3 → R →+* R) (u : σ → R)
    (a : Fin 3 → ℕ) (n : σ →₀ ℕ) :
    MvPolynomial.eval (fun _ => (1 : R))
      (mixedInvariant (fun j i => g j (u i)) a (monomial n 1)) =
      (g 0 (eigenvalue u n)) ^ a 0 * (g 1 (eigenvalue u n)) ^ a 1 *
        (g 2 (eigenvalue u n)) ^ a 2 := by
  rw [derivative_row_at_one]
  simp only [eigenvalue_map]

end WeightedTorusJets.W19

end


namespace WeightedTorusJets.W40

open scoped BigOperators

variable {R : Type*} [CommRing R]

def rowEntry (x y z : R) (a b c : ℕ) : R := x ^ a * y ^ b * z ^ c

def replacementCoefficient (k m : ℕ) : R := (-1) ^ m * (k.choose m : R)

theorem replacement_expansion_second (x y z : R) (p k r b c : ℕ) :
    x ^ r * (x ^ p - y) ^ k * y ^ b * z ^ c =
      ∑ m ∈ Finset.range (k + 1), replacementCoefficient k m *
        rowEntry x y z (p * (k - m) + r) (b + m) c := by
  rw [show x ^ p - y = -y + x ^ p by ring, add_pow]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [neg_pow]
  simp only [replacementCoefficient, rowEntry, pow_add, pow_mul]
  ring

theorem replacement_expansion_third (x y z : R) (p k r b c : ℕ) :
    x ^ r * (x ^ p - z) ^ k * y ^ b * z ^ c =
      ∑ m ∈ Finset.range (k + 1), replacementCoefficient k m *
        rowEntry x y z (p * (k - m) + r) b (c + m) := by
  have h := replacement_expansion_second x z y p k r c b
  simpa only [rowEntry, mul_assoc, mul_left_comm, mul_comm] using h

@[simp] theorem replacementCoefficient_zero (k : ℕ) :
    replacementCoefficient k 0 = (1 : R) := by
  simp [replacementCoefficient]

theorem replacement_leading_term (x y z : R) (p k r b c : ℕ) :
    replacementCoefficient k 0 * rowEntry x y z (p * (k - 0) + r) (b + 0) c =
      rowEntry x y z (p * k + r) b c := by simp

theorem replacement_original_add_lower (x y z : R) (p k r b c : ℕ) :
    x ^ r * (x ^ p - y) ^ k * y ^ b * z ^ c =
      rowEntry x y z (p * k + r) b c +
        ∑ m ∈ Finset.range k, replacementCoefficient k (m + 1) *
          rowEntry x y z (p * (k - (m + 1)) + r) (b + (m + 1)) c := by
  rw [replacement_expansion_second, Finset.sum_range_succ']
  simp only [replacementCoefficient_zero, Nat.sub_zero, Nat.add_zero, one_mul]
  exact add_comm _ _

theorem replacement_vector_original_add_lower {ι : Type*}
    (x y z : ι → R) (p k r b c : ℕ) :
    (fun n => x n ^ r * (x n ^ p - y n) ^ k * y n ^ b * z n ^ c) =
      (fun n => rowEntry (x n) (y n) (z n) (p * k + r) b c) +
        ∑ m ∈ Finset.range k, replacementCoefficient (R := R) k (m + 1) •
          (fun n => rowEntry (x n) (y n) (z n)
            (p * (k - (m + 1)) + r) (b + (m + 1)) c) := by
  funext n
  simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    replacement_original_add_lower (x n) (y n) (z n) p k r b c

theorem shifted_first_index (p k r m : ℕ) (hm : m ≤ k) :
    p * (k - m) + r = (p * k + r) - p * m := by
  have hkm : k - m + m = k := Nat.sub_add_cancel hm
  have hpm : p * m ≤ p * k := Nat.mul_le_mul_left p hm
  have hprod : p * (k - m) + p * m = p * k := by nlinarith
  omega

def weight (H a b c : ℕ) : ℕ := a + H * b + H * c

theorem replacement_weight_lt_second (H p k r b c m : ℕ)
    (hp : H < p) (hm0 : 0 < m) (hm : m ≤ k) :
    weight H (p * (k - m) + r) (b + m) c < weight H (p * k + r) b c := by
  have hkm : k - m + m = k := Nat.sub_add_cancel hm
  have hpm : H * m < p * m := Nat.mul_lt_mul_of_pos_right hp hm0
  unfold weight
  nlinarith

theorem replacement_weight_lt_third (H p k r b c m : ℕ)
    (hp : H < p) (hm0 : 0 < m) (hm : m ≤ k) :
    weight H (p * (k - m) + r) b (c + m) < weight H (p * k + r) b c := by
  have h := replacement_weight_lt_second H p k r c b m hp hm0 hm
  simpa only [weight, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

theorem rowEntry_eq_actual_jet {σ : Type*} [Fintype σ]
    (g : Fin 3 → R →+* R) (u : σ → R) (n : σ →₀ ℕ) (a : Fin 3 → ℕ) :
    rowEntry (g 0 (WeightedTorusJets.W18.eigenvalue u n))
      (g 1 (WeightedTorusJets.W18.eigenvalue u n))
      (g 2 (WeightedTorusJets.W18.eigenvalue u n)) (a 0) (a 1) (a 2) =
      MvPolynomial.eval (fun _ => (1 : R))
        (WeightedTorusJets.W19.mixedInvariant (fun j i => g j (u i)) a
          (MvPolynomial.monomial n 1)) :=
  (WeightedTorusJets.W19.derivative_row_endomorphisms g u a n).symm

end WeightedTorusJets.W40



end SiegelZeros

end OAI
