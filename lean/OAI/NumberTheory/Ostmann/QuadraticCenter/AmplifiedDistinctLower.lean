import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifierWeight

namespace OAI

namespace Ostmann.QuadraticCenter

theorem adaptive_repeat_retains_half {D I I₀ E T : ℝ}
    (hI : 0 ≤ I) (hE : 0 ≤ E) (hT : 0 < T)
    (hmass : I₀ * T ≤ I) (hsmall : 4 * E ≤ T)
    (herr : |D - I| ≤ E * (I₀ + I / T)) : I / 2 ≤ D := by
  have hmass' : I₀ ≤ I / T := (le_div_iff₀ hT).mpr hmass
  have hsmall' : E ≤ T / 4 := by linarith
  have he : E * (I₀ + I / T) ≤ I / 2 := by
    calc
      _ ≤ E * (I / T + I / T) :=
        mul_le_mul_of_nonneg_left (add_le_add hmass' le_rfl) hE
      _ ≤ (T / 4) * (I / T + I / T) :=
        mul_le_mul_of_nonneg_right hsmall' (by positivity)
      _ = I / 2 := by field_simp; ring
  have hh := (abs_le.mp (herr.trans he)).1
  linarith

theorem amplified_distinct_moment_retains_half {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) {lam X : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam < 1) (hX : 0 < X)
    (P : Finset ℕ) (hP : 0 < P.card) (ε t : ℕ → ℤ)
    (hε : ∀ r ∈ P, ε r = -1 ∨ ε r = 1)
    {k : ℕ} (hk : 2 ≤ k) (heven : Even k) {τ : ℝ} (hτ : 0 < τ)
    (hmass : (∑' n : ℤ, amplifierWeight p hcop S lam X n) * τ ^ k ≤
      ∑' n : ℤ, amplifiedMomentTerm p hcop S lam X P ε t k n)
    (hsmall : 4 * ((((k : ℝ) + 1) * (k : ℝ) ^ 2 / P.card) *
      (τ + (k : ℝ) / Real.sqrt (P.card : ℝ)) ^ (k - 2)) ≤ τ ^ k) :
    (∑' n : ℤ, amplifiedMomentTerm p hcop S lam X P ε t k n) / 2 ≤
      ∑' n : ℤ, amplifierWeight p hcop S lam X n *
        distinctSignAverage P (fun r => ε r * jacobiSym (n - t r) r) k := by
  apply adaptive_repeat_retains_half
    (tsum_nonneg (amplifiedMomentTerm_nonneg p hcop S hlam hlam1 X P ε t heven))
    (by positivity) (pow_pos hτ k) hmass hsmall
  exact amplified_distinct_moment_error p hcop S hlam hlam1 hX P hP ε t hε hk heven hτ

end Ostmann.QuadraticCenter

end OAI
