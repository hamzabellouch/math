import OAI.NumberTheory.Ostmann.QuadraticSieveReciprocity

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def oddSquarefreeUpTo (U : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 U).filter (fun u => Odd u ∧ Squarefree u)

@[simp] theorem mem_oddSquarefreeUpTo {U u : ℕ} :
    u ∈ oddSquarefreeUpTo U ↔ 1 ≤ u ∧ u ≤ U ∧ Odd u ∧ Squarefree u := by
  classical
  simp only [oddSquarefreeUpTo, Finset.mem_filter, Finset.mem_Icc]
  tauto

noncomputable def coefficientEnergy (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ s ∈ S, ‖a s‖ ^ 2

noncomputable def jacobiEnergy (V S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ v ∈ V, ‖∑ s ∈ S, a s * (jacobiSym (s : ℤ) v : ℂ)‖ ^ 2

noncomputable def numeratorEnergy (c : ℤ) (V S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ v ∈ V, ‖∑ s ∈ S, a s * (jacobiSym (c * (v : ℤ)) s : ℂ)‖ ^ 2

noncomputable def twistedCoefficients (c : ℤ) (r : ℕ) (a : ℕ → ℂ) (s : ℕ) : ℂ :=
  a s * (jacobiSym c s : ℂ) * (reciprocityTwist r s : ℂ)

theorem coefficientEnergy_nonneg (S : Finset ℕ) (a : ℕ → ℂ) :
    0 ≤ coefficientEnergy S a := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem jacobiEnergy_nonneg (V S : Finset ℕ) (a : ℕ → ℂ) :
    0 ≤ jacobiEnergy V S a := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem coefficientEnergy_twisted_le (S : Finset ℕ) (a : ℕ → ℂ) (c : ℤ) (r : ℕ) :
    coefficientEnergy S (twistedCoefficients c r a) ≤ coefficientEnergy S a :=
  sum_norm_sq_jacobi_twist_le S a c r

theorem numeratorEnergy_le_two_twists (V S : Finset ℕ) (a : ℕ → ℂ) (c : ℤ)
    (hV : ∀ v ∈ V, Odd v) (hS : ∀ s ∈ S, Odd s) :
    numeratorEnergy c V S a ≤
      jacobiEnergy V S (twistedCoefficients c 1 a) +
      jacobiEnergy V S (twistedCoefficients c 3 a) := by
  unfold numeratorEnergy jacobiEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v hv
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp (hV v hv)) with hv1 | hv3
  · rw [sum_jacobi_mul_reciprocity_twist S a c (r := 1) (hV v hv) hS
        (by simpa using hv1.symm)]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · rw [sum_jacobi_mul_reciprocity_twist S a c (r := 3) (hV v hv) hS
        (by simpa using hv3.symm)]
    exact le_add_of_nonneg_left (sq_nonneg _)

theorem numeratorEnergy_le_of_unsigned (V S : Finset ℕ) (a : ℕ → ℂ) (c : ℤ)
    (hV : ∀ v ∈ V, Odd v) (hS : ∀ s ∈ S, Odd s) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ b : ℕ → ℂ, jacobiEnergy V S b ≤ K * coefficientEnergy S b) :
    numeratorEnergy c V S a ≤ 2 * K * coefficientEnergy S a := by
  calc
    numeratorEnergy c V S a ≤
        jacobiEnergy V S (twistedCoefficients c 1 a) +
        jacobiEnergy V S (twistedCoefficients c 3 a) :=
      numeratorEnergy_le_two_twists V S a c hV hS
    _ ≤ K * coefficientEnergy S (twistedCoefficients c 1 a) +
        K * coefficientEnergy S (twistedCoefficients c 3 a) :=
      add_le_add (hbound _) (hbound _)
    _ ≤ K * coefficientEnergy S a + K * coefficientEnergy S a :=
      add_le_add (mul_le_mul_of_nonneg_left (coefficientEnergy_twisted_le S a c 1) hK)
        (mul_le_mul_of_nonneg_left (coefficientEnergy_twisted_le S a c 3) hK)
    _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI
