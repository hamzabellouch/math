import OAI.NumberTheory.Ostmann.QuadraticCenter.WalshScalar
import OAI.NumberTheory.Ostmann.QuadraticCenter.WalshTensorMinkowski
import OAI.NumberTheory.Ostmann.QuadraticCenter.WalshTensorSplit

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem signMean_const {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ) :
    signMean (fun _ : ι → Bool => r) = r := by
  simp [signMean, nsmul_eq_mul]

theorem signMean_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : (ι → Bool) → ℝ} (h : ∀ ε, f ε ≤ g ε) : signMean f ≤ signMean g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ε hε => h ε)) (by positivity)

theorem signMean_pair_flip {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (f : (ι → Bool) → ℝ) :
    signMean (fun ε => (f ε + f (flipSign i ε)) / 2) = signMean f := by
  have hs : (∑ ε, f (flipSign i ε)) = ∑ ε, f ε := (flipSignEquiv i).sum_comp f
  simp only [signMean, ← Finset.sum_div, Finset.sum_add_distrib, hs]
  ring

theorem restrictedWalsh_even_moment_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (c : Finset ι → ℝ) {l : ℕ} (hl : 1 ≤ l) :
    signMean (fun ε => restrictedWalshPolynomial I c ε ^ (2 * l)) ≤
      (restrictedWalshEnergy I c (((2 * l : ℕ) : ℝ) ^ 2)) ^ l := by
  classical
  let w : ℝ := ((2 * l : ℕ) : ℝ) ^ 2
  have hw : 0 ≤ w := sq_nonneg _
  change signMean (fun ε => restrictedWalshPolynomial I c ε ^ (2 * l)) ≤
    restrictedWalshEnergy I c w ^ l
  induction I using Finset.induction_on generalizing c with
  | empty =>
      simp only [restrictedWalshPolynomial, restrictedWalshEnergy,
        Finset.powerset_empty, Finset.sum_singleton, walshCharacter_empty,
        mul_one, Finset.card_empty, pow_zero, one_mul, signMean_const, pow_mul]
      exact le_rfl
  | @insert i I hi ih =>
      let f := restrictedWalshPolynomial I c
      let g := restrictedWalshPolynomial I (fun s => c (insert i s))
      let A := restrictedWalshEnergy I c w
      let B := restrictedWalshEnergy I (fun s => c (insert i s)) w
      have hA : 0 ≤ A := restrictedWalshEnergy_nonneg I c hw
      have hB : 0 ≤ B := restrictedWalshEnergy_nonneg I _ hw
      have hpair (ε : ι → Bool) :
          (restrictedWalshPolynomial (insert i I) c ε ^ (2 * l) +
            restrictedWalshPolynomial (insert i I) c (flipSign i ε) ^ (2 * l)) / 2 ≤
          (f ε ^ 2 + w * g ε ^ 2) ^ l := by
        rw [restrictedWalshPolynomial_insert hi, restrictedWalshPolynomial_insert hi,
          restrictedWalshPolynomial_flip hi, restrictedWalshPolynomial_flip hi, sign_flipSign]
        have hh := sign_pair_even_moment_le (f ε) (sign (ε i) * g ε) l
        simpa only [f, g, w, mul_pow, sign_sq, one_mul, sub_eq_add_neg, neg_mul] using hh
      have hMf : signMean (fun ε => (f ε ^ 2) ^ l) ≤ A ^ l := by
        simpa only [f, A, ← pow_mul] using ih c
      have hMg : signMean (fun ε => (w * g ε ^ 2) ^ l) ≤ (w * B) ^ l := by
        simp_rw [mul_pow, ← pow_mul]
        rw [signMean_const_mul]
        exact mul_le_mul_of_nonneg_left (ih (fun s => c (insert i s))) (pow_nonneg hw _)
      calc
        signMean (fun ε => restrictedWalshPolynomial (insert i I) c ε ^ (2 * l)) =
            signMean (fun ε => (restrictedWalshPolynomial (insert i I) c ε ^ (2 * l) +
              restrictedWalshPolynomial (insert i I) c (flipSign i ε) ^ (2 * l)) / 2) :=
          (signMean_pair_flip i _).symm
        _ ≤ signMean (fun ε => (f ε ^ 2 + w * g ε ^ 2) ^ l) := signMean_mono hpair
        _ ≤ (A + w * B) ^ l :=
          signMean_power_add_le (fun ε => f ε ^ 2) (fun ε => w * g ε ^ 2)
            hA (mul_nonneg hw hB) (fun ε => sq_nonneg _) (fun ε => mul_nonneg hw (sq_nonneg _))
            hl hMf hMg
        _ = restrictedWalshEnergy (insert i I) c w ^ l := by
          rw [restrictedWalshEnergy_insert hi]

theorem walsh_even_moment_le_weighted_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) {l : ℕ} (hl : 1 ≤ l) :
    signMean (fun ε => (∑ s : Finset ι, c s * walshCharacter s ε) ^ (2 * l)) ≤
      (∑ s : Finset ι, ((((2 * l : ℕ) : ℝ) ^ 2) ^ s.card) * c s ^ 2) ^ l := by
  simpa only [restrictedWalshPolynomial, restrictedWalshEnergy, Finset.powerset_univ] using
    restrictedWalsh_even_moment_le (Finset.univ : Finset ι) c hl

end Ostmann.QuadraticCenter

end OAI
