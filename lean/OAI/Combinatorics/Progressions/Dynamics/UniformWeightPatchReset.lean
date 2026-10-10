import OAI.Combinatorics.Progressions.Fourier.PolynomialTorusDensityIncrement
import OAI.Combinatorics.Progressions.Fourier.UniformWeightTorusModel

namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem uniform_weight_patch_density_increment (h : ℕ) (hh : 0 < h) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧
      ∀ (s d N H : ℕ) (A : PolynomialPatch Unit s d), (∀ i, A.weight i = h) →
        0 < H → K * ((d : ℝ) + 1) ≤ H → H ^ (p * (d + 1) ^ (2 * h)) ≤ N →
        ∀ f : ℕ → ℝ, (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) →
        ∀ b σ : ℝ, b ∈ Set.Icc (0 : ℝ) 1 → 0 < σ →
        4 * (h : ℝ) * ((A.kernel.lip : ℝ) * d) ≤ σ * H →
        σ ≤ (𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ σ * H / (2 : ℝ) ^ (h + 2) ≤ len ∧
          (∀ n < len, a + q * n < N) ∧ b < 𝔼 n : Fin len, f (a + q * n.val) := by
  obtain ⟨K, p, hK, hp, hreset⟩ := polynomial_torus_density_increment.{0} h
  refine ⟨K, p, hK, hp, ?_⟩
  intro s d N H A hw hH hscale hsize f hf b σ hb hσ hsmall hscore
  obtain ⟨F, Q, hF, hF01, hperiod, hQ, heval⟩ := A.exists_uniform_weight_torus_model hh hw
  let P := fun i => MvPolynomial.uniqueAlgEquiv ℝ Unit (Q i)
  have hP : ∀ i, (P i).natDegree ≤ h := fun i => singleParameter_natDegree_le (hQ i)
  have hvalue (t : ℝ) : A.value (fun _ => t) = F (fun i => (P i).eval t) := by
    rw [heval]
    simp only [P, singleParameter_eval]
  have hscore' : σ ≤ 𝔼 n : Fin N, (f n.val - b) * F (fun i => (P i).eval (n.val : ℝ)) := by
    simpa only [hvalue] using hscore
  apply hreset (Fin d) P hP N H hH (by simpa using hscale) (by simpa using hsize)
    f F (A.kernel.lip * d) hF hperiod hF01 hf b σ hb hσ
    (by simpa only [NNReal.coe_mul, NNReal.coe_natCast] using hsmall) hscore'

end Erdos3

end

end OAI
