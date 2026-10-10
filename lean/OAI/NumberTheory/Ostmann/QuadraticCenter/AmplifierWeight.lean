import OAI.NumberTheory.Ostmann.QuadraticCenter.MomentWeight
import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedRepeat

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators FourierTransform

def amplifierWeight {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam X : ℝ) (n : ℤ) : ℝ :=
  (SchwartzCutoff.psi ((n : ℝ) / X)).re * amplifier p hcop S lam (n : ZMod (∏ i, p i))

theorem amplifierWeight_nonneg {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (X : ℝ) (n : ℤ) : 0 ≤ amplifierWeight p hcop S lam X n :=
  mul_nonneg (SchwartzCutoff.psi_nonneg _) (amplifier_pos p hcop S hlam hlam1 _).le

theorem amplifierWeight_summable {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) {lam X : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam < 1) (hX : 0 < X) :
    Summable (amplifierWeight p hcop S lam X) := by
  refine Summable.of_nonneg_of_le (amplifierWeight_nonneg p hcop S hlam hlam1 X) ?_
    ((summable_scaled_cutoff_norm hX).mul_right ((1 + lam) ^ Fintype.card ι))
  intro n
  exact mul_le_mul (Complex.re_le_norm _) (amplifier_le p hcop S hlam hlam1 _)
    (amplifier_pos p hcop S hlam hlam1 _).le (norm_nonneg _)

theorem amplifierWeight_total {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ)
    (X : ℝ) (hX : 0 < X) (hscale : (1 : ℝ) / 4 ≤ X / (∏ i, p i : ℕ)) :
    (∑' n : ℤ, amplifierWeight p hcop S lam X n) = X * (𝓕 SchwartzCutoff.psi 0).re := by
  have hc (n : ℤ) : (amplifierWeight p hcop S lam X n : ℂ) =
      (amplifier p hcop S lam (n : ZMod (∏ i, p i)) : ℂ) *
        SchwartzCutoff.psi ((n : ℝ) / X) := by
    apply Complex.ext <;>
      simp [amplifierWeight, Complex.mul_re, Complex.mul_im, SchwartzCutoff.psi_im]
    ring
  have hm := amplifier_cutoff_mass p hcop S lam X hX hscale
  have he : (((∑' n : ℤ, amplifierWeight p hcop S lam X n) : ℝ) : ℂ) =
      (X : ℂ) * 𝓕 SchwartzCutoff.psi 0 := by
    rw [Complex.ofReal_tsum]
    simpa only [hc] using hm
  have hr := congrArg Complex.re he
  simpa only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] using hr

theorem amplified_distinct_moment_error {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) {lam X : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam < 1) (hX : 0 < X)
    (P : Finset ℕ) (hP : 0 < P.card) (ε t : ℕ → ℤ)
    (hε : ∀ r ∈ P, ε r = -1 ∨ ε r = 1)
    {k : ℕ} (hk : 2 ≤ k) (heven : Even k) {τ : ℝ} (hτ : 0 < τ) :
    |(∑' n : ℤ, amplifierWeight p hcop S lam X n *
        distinctSignAverage P (fun r => ε r * jacobiSym (n - t r) r) k) -
      (∑' n : ℤ, amplifiedMomentTerm p hcop S lam X P ε t k n)| ≤
    (((k : ℝ) + 1) * (k : ℝ) ^ 2 / P.card) *
      (τ + (k : ℝ) / Real.sqrt (P.card : ℝ)) ^ (k - 2) *
      ((∑' n : ℤ, amplifierWeight p hcop S lam X n) +
        (∑' n : ℤ, amplifiedMomentTerm p hcop S lam X P ε t k n) / τ ^ k) := by
  exact weighted_distinct_moment_error (amplifierWeight p hcop S lam X)
    (amplifierWeight_nonneg p hcop S hlam hlam1 X)
    (amplifierWeight_summable p hcop S hlam hlam1 hX) P hP
    (fun n r => ε r * jacobiSym (n - t r) r)
    (fun n r hr => oriented_jacobi_trichotomy (ε r) (n - t r) r (hε r hr)) hk heven hτ

end Ostmann.QuadraticCenter

end

end OAI
