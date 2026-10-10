import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplificationWeight
import OAI.NumberTheory.Ostmann.Construction.PhysicalMomentLower
import OAI.NumberTheory.Ostmann.Arithmetic.ScaledPoisson

namespace OAI

/-! # The original physical-space amplified moment -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def physicalWeight (Q : Finset ℕ) (D : ∀ p : ℕ, Finset (ZMod p))
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (n : ℤ) : ℝ :=
  (ψ ((n : ℝ) / X)).re * amplificationWeight Q D n

noncomputable def orientedQuadraticValue (ε : ℕ → ℝ) (t : ℕ → ℤ) (n : ℤ) (p : ℕ) : ℝ :=
  ε p * (jacobiSym (n - t p) p : ℝ)

theorem orientedQuadraticValue_ternary (ε : ℕ → ℝ) (t : ℕ → ℤ) (n : ℤ) (p : ℕ)
    (hε : ε p = 1 ∨ ε p = -1) :
    orientedQuadraticValue ε t n p = 0 ∨ orientedQuadraticValue ε t n p = 1 ∨
      orientedQuadraticValue ε t n p = -1 := by
  rcases hε with h | h <;>
    rcases jacobiSym.trichotomy (n - t p) p with hχ | hχ | hχ <;>
    simp [orientedQuadraticValue, h, hχ]

theorem physicalWeight_nonneg (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re)
    (X : ℝ) (n : ℤ) : 0 ≤ physicalWeight Q D ψ X n :=
  mul_nonneg (hψ _) (amplificationWeight_pos Q hQ D n).le

theorem physicalWeight_summable (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (physicalWeight Q D ψ X) := by
  have hsn : Summable (fun n : ℤ => ‖ψ ((n : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  apply Summable.of_norm_bounded (hsn.mul_right ((17 / 16 : ℝ) ^ Q.card))
  intro n
  rw [physicalWeight, Real.norm_eq_abs, abs_mul,
    abs_of_pos (amplificationWeight_pos Q hQ D n)]
  exact mul_le_mul (Complex.abs_re_le_norm _) (amplificationWeight_le Q hQ D n)
    (amplificationWeight_pos Q hQ D n).le (norm_nonneg _)

theorem physicalWeight_lower (Q : Finset ℕ)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (X cψ : ℝ)
    (hX : 0 < X) (hcψ : 0 ≤ cψ) (hψ : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (n : ℤ) (hn0 : 0 ≤ (n : ℝ)) (hnX : (n : ℝ) ≤ X)
    (hD : ∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3)
    (hn : ∀ p ∈ Q, (n : ZMod p) ∈ D p) :
    cψ * Real.exp ((Q.card : ℝ) / 50) ≤ physicalWeight Q D ψ X n := by
  have hψ' := hψ ((n : ℝ) / X) ⟨div_nonneg hn0 hX.le, (div_le_one hX).mpr hnX⟩
  exact mul_le_mul hψ' (exp_le_amplificationWeight Q D n hD hn)
    (Real.exp_nonneg _) (hcψ.trans hψ')

theorem physical_moment_from_tail_bias
    (Q P : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hP : 0 < P.card)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (X cψ c : ℝ)
    (hX : 0 < X) (hcψ : 0 ≤ cψ) (hc : 0 ≤ c)
    (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (S : Finset ℤ) (hS : ∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X)
    (hD : ∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3)
    (hSD : ∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p)
    (ε : ℕ → ℝ) (t : ℕ → ℤ) (hε : ∀ p ∈ P, ε p = 1 ∨ ε p = -1)
    (hbias : ∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p)
    (k : ℕ) (heven : Even k) :
    (cψ * Real.exp ((Q.card : ℝ) / 50)) * S.card * c ^ k ≤
      ∑' n : ℤ, physicalWeight Q D ψ X n *
        ternaryMean (fun p : P => orientedQuadraticValue ε t n p) ^ k := by
  apply weighted_finite_bias_moment S (physicalWeight Q D ψ X)
    (fun n (p : P) => orientedQuadraticValue ε t n p) c
    (cψ * Real.exp ((Q.card : ℝ) / 50)) k heven (by simpa using hP) hc (by positivity)
    (physicalWeight_nonneg Q hQ D ψ hψ0 X)
    (fun n hn => physicalWeight_lower Q D ψ X cψ hX hcψ hψ1 n
      (hS n hn).1 (hS n hn).2 hD (hSD n hn))
    (physicalWeight_summable Q hQ D ψ X hX)
    (fun n p => orientedQuadraticValue_ternary ε t n p (hε p p.property))
    (fun p => hbias p p.property)

end Ostmann

end OAI
