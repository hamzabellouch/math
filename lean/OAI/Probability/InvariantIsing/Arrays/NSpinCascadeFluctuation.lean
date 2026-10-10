import OAI.Probability.InvariantIsing.Arrays.NSpinCascade

namespace OAI

/-! Conditional cascade fluctuations for the actual Ising terminal. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

/-- The conditional cascade fluctuation is bounded uniformly in the Ising
terminal, rotation, external field, Gaussian root and number of spins. -/
theorem rotatedCascadeLog_centered_square {N : ℕ} (hN : 0 < N)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : IsingPerceptron.CascadeExponents n b)
    (eig : Fin N → ℝ) (U : Rotation N) (c z : Fin N → ℝ) :
    Integrable (fun T => (rotatedCascadeLog n eig U c z T -
      rotatedCascadeValue n b v eig U c z) ^ 2) (rotatedCascadeLaw N n b v) ∧
    (∫ T, (rotatedCascadeLog n eig U c z T - rotatedCascadeValue n b v eig U c z) ^ 2
      ∂rotatedCascadeLaw N n b v) ≤
      4 * ∫ T, (Real.log (IsingPerceptron.rawTreeTotal n T).toReal) ^ 2
        ∂(IsingPerceptron.rawCascadeLaw n b : Measure (IsingPerceptron.RawTree n)) := by
  have h := IsingPerceptron.linearGrowth_noiseCascade_recursion n b hb
    (fun i => vectorGaussianLaw N (v i)) (fun i _ => vectorGaussianLaw_moments hN (v i))
    (measurable_rotatedFieldTerminal eig U c) (rotatedFieldTerminal_linearGrowth eig U c) z
  have he := IsingPerceptron.noise_leaf_log_eq_ratio n b hb
    (fun i => vectorGaussianLaw N (v i))
    (fun _ => measurable_fst.add measurable_snd) (measurable_rotatedFieldTerminal eig U c) z
  let L := fun T => Real.log
    ((IsingPerceptron.terminalTreeFactor n b (fun i => vectorGaussianLaw N (v i))
      (fun _ p => p.1 + p.2) (rotatedFieldTerminal eig U c) z T).toReal /
      (IsingPerceptron.noiseTreeTotal (Fin N → ℝ) n T).toReal)
  have heq : (fun T => (rotatedCascadeLog n eig U c z T - rotatedCascadeValue n b v eig U c z) ^ 2)
      =ᵐ[rotatedCascadeLaw N n b v]
      (fun T => (L T - rotatedCascadeValue n b v eig U c z) ^ 2) := by
    filter_upwards [he] with T hT
    exact congrArg (fun x => (x - rotatedCascadeValue n b v eig U c z) ^ 2) hT
  exact ⟨h.2.2.2.1.congr (Filter.EventuallyEq.symm heq),
    (integral_congr_ae heq).trans_le h.2.2.2.2⟩

end InvariantIsing

end

end OAI
