import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifierWeight
import OAI.NumberTheory.Ostmann.QuadraticCenter.IntegratedDistinct
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeBlockCenter

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def primeProductCenter (q : ℕ) (t : ℕ → ℤ) : ℕ :=
  primeBlockCenter q.primeFactors (fun _ hp => (Nat.mem_primeFactors.mp hp).1) t

theorem primeProductCenter_prod (U : Finset ℕ) (hU : ∀ p ∈ U, Nat.Prime p) (t : ℕ → ℤ) :
    primeProductCenter (∏ p ∈ U, p) t = primeBlockCenter U hU t := by
  unfold primeProductCenter
  have h := Nat.primeFactors_prod hU
  simp only [h]

def primeProductTransform {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam X : ℝ) (t : ℕ → ℤ) (q : ℕ) : ℂ :=
  ∑' n : ℤ, (jacobiSym (n - primeProductCenter q t) q : ℂ) *
    (amplifier p hcop S lam (n : ZMod (∏ i, p i)) : ℂ) * SchwartzCutoff.psi ((n : ℝ) / X)

theorem oriented_subset_transform_bound {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam X : ℝ)
    (U : Finset ℕ) (hU : ∀ r ∈ U, Nat.Prime r) (ε t : ℕ → ℤ)
    (hε : ∀ r ∈ U, ε r = -1 ∨ ε r = 1) :
    |∑' n : ℤ, amplifierWeight p hcop S lam X n *
      ∏ r ∈ U, ((ε r * jacobiSym (n - t r) r : ℤ) : ℝ)| ≤
        ‖primeProductTransform p hcop S lam X t (∏ r ∈ U, r)‖ := by
  have hp (n : ℤ) :
      (((∏ r ∈ U, ((ε r * jacobiSym (n - t r) r : ℤ) : ℝ)) : ℝ) : ℂ) =
      ((∏ r ∈ U, ε r : ℤ) : ℂ) *
        (jacobiSym (n - primeProductCenter (∏ r ∈ U, r) t) (∏ r ∈ U, r) : ℂ) := by
    rw [primeProductCenter_prod U hU t]
    exact_mod_cast primeBlock_oriented_product U hU ε t n
  have hw (n : ℤ) : ((amplifierWeight p hcop S lam X n : ℝ) : ℂ) =
      (amplifier p hcop S lam (n : ZMod (∏ i, p i)) : ℂ) * SchwartzCutoff.psi ((n : ℝ) / X) := by
    apply Complex.ext <;> simp [amplifierWeight, Complex.mul_re, Complex.mul_im, SchwartzCutoff.psi_im]
    ring
  have he (n : ℤ) :
      (((amplifierWeight p hcop S lam X n *
        ∏ r ∈ U, ((ε r * jacobiSym (n - t r) r : ℤ) : ℝ)) : ℝ) : ℂ) =
      ((∏ r ∈ U, ε r : ℤ) : ℂ) *
        ((jacobiSym (n - primeProductCenter (∏ r ∈ U, r) t) (∏ r ∈ U, r) : ℂ) *
          (amplifier p hcop S lam (n : ZMod (∏ i, p i)) : ℂ) *
            SchwartzCutoff.psi ((n : ℝ) / X)) := by
    rw [Complex.ofReal_mul, hp, hw]
    ring
  have ho : ‖((∏ r ∈ U, ε r : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Int.cast_prod, norm_prod]
    calc
      _ ≤ ∏ _r ∈ U, (1 : ℝ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro r hr
        rcases hε r hr with h | h <;> simp [h]
      _ = _ := by simp
  calc
    _ = ‖(((∑' n : ℤ, amplifierWeight p hcop S lam X n *
      ∏ r ∈ U, ((ε r * jacobiSym (n - t r) r : ℤ) : ℝ)) : ℝ) : ℂ)‖ := by simp
    _ = ‖((∏ r ∈ U, ε r : ℤ) : ℂ) * primeProductTransform p hcop S lam X t (∏ r ∈ U, r)‖ := by
      rw [Complex.ofReal_tsum]
      simp_rw [he]
      rw [tsum_mul_left]
      rfl
    _ ≤ _ := by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) ho

theorem amplified_distinct_le_product_transforms {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) {lam X : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam < 1) (hX : 0 < X)
    (P : Finset ℕ) (hP : ∀ r ∈ P, Nat.Prime r) (ε t : ℕ → ℤ)
    (hε : ∀ r ∈ P, ε r = -1 ∨ ε r = 1) (k : ℕ) :
    (∑' n : ℤ, amplifierWeight p hcop S lam X n *
      distinctSignAverage P (fun r => ε r * jacobiSym (n - t r) r) k) ≤
      ((k.factorial : ℝ) / (P.card : ℝ) ^ k) *
        ∑ U ∈ P.powersetCard k, ‖primeProductTransform p hcop S lam X t (∏ r ∈ U, r)‖ := by
  apply (integrated_distinct_le_sum_abs P (amplifierWeight p hcop S lam X)
    (amplifierWeight_nonneg p hcop S hlam hlam1 X)
    (amplifierWeight_summable p hcop S hlam hlam1 hX)
    (fun n r => ε r * jacobiSym (n - t r) r)
    (fun n r hr => oriented_jacobi_trichotomy (ε r) (n - t r) r (hε r hr)) k).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro U hU
  have hsub := (Finset.mem_powersetCard.mp hU).1
  exact oriented_subset_transform_bound p hcop S lam X U (fun r hr => hP r (hsub hr))
    ε t (fun r hr => hε r (hsub hr))

end Ostmann.QuadraticCenter

end

end OAI
