import OAI.Combinatorics.Progressions.Fourier.UniformWeightTorusModel

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem singleParameter_affine_eval (P : MvPolynomial Unit ℝ)
    (hP : P ∈ weightedSupportLE (fun _ : Unit => 1) 1) :
    ∃ a b : ℝ, ∀ t : ℝ, MvPolynomial.aeval (fun _ : Unit => t) P = t * a + b := by
  let Q := MvPolynomial.uniqueAlgEquiv ℝ Unit P
  have hQ : Q.natDegree ≤ 1 := singleParameter_natDegree_le hP
  refine ⟨Q.coeff 1, Q.coeff 0, ?_⟩
  intro t
  rw [← singleParameter_eval]
  change Q.eval t = _
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hQ]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

namespace PolynomialPatch

theorem degree_one_density_increment {d N H : ℕ} (A : PolynomialPatch Unit 1 d)
    (hH : 0 < H) (hsize : H ^ (2 * d + 1) ≤ N) (f : ℕ → ℝ)
    (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    {b σ : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) (hσ : 0 < σ)
    (hsmall : 4 * ((A.kernel.lip : ℝ) * d) ≤ σ * H)
    (hscore : σ ≤ 𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) :
    ∃ q a len : ℕ, 0 < q ∧ q ≤ H ^ (2 * d) ∧
      σ * H / 4 ≤ len ∧ len ≤ H ∧ (∀ j < len, a + q * j < N) ∧
      b < 𝔼 j : Fin len, f (a + q * j.val) := by
  have hw : ∀ i, A.weight i = 1 := fun i => Nat.le_antisymm (A.weight_le i) (A.weight_pos i)
  obtain ⟨F, Q, hF, hF01, hperiod, hQ, heval⟩ :=
    A.exists_uniform_weight_torus_model (by decide : 0 < 1) hw
  have haffine : ∀ i, ∃ a b : ℝ, ∀ t : ℝ,
      MvPolynomial.aeval (fun _ : Unit => t) (Q i) = t * a + b :=
    fun i => singleParameter_affine_eval (Q i) (hQ i)
  choose alpha beta hab using haffine
  have hvalue (t : ℝ) : A.value (fun _ => t) = F (fun i => t * alpha i + beta i) := by
    rw [heval]
    congr 1
    funext i
    exact hab i t
  have hscore' : σ ≤ 𝔼 n : Fin N,
      (f n.val - b) * F (fun i => (n.val : ℝ) * alpha i + beta i) := by
    simpa only [hvalue] using hscore
  simpa only [Fintype.card_fin] using affine_torus_density_increment hH
    (by simpa only [Fintype.card_fin] using hsize) alpha beta f hF hperiod hF01 hf hb hσ
    (by simpa only [NNReal.coe_mul, NNReal.coe_natCast] using hsmall) hscore'

end PolynomialPatch
end Erdos3

end

end OAI
