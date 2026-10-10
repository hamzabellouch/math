import OAI.Probability.InvariantIsing.Fields.SpinPriorFlatLaw

namespace OAI

/-! The Gaussian/cascade-averaged logarithm has a rotation modulus uniform
in the normalized spin constraint. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

theorem spinPriorFlatMean_rotation_bound (hgauss : GaussianLipschitzVarianceInput)
    {N m k : ℕ} (hN : 0 < N) (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig c : Fin N → ℝ) (K : ℝ) (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (site : ℕ → ℝ≥0) (monomial : ℕ → Fin k → ℝ≥0) (U V : SpecialOrthogonal N) :
    |(∫ p, spinPriorFlatLog π eig (specialRotation U) c I degree amp n
        (fun i => tensorVarianceProfile I degree (site i) (monomial i)) p
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates)-
      ∫ p, spinPriorFlatLog π eig (specialRotation V) c I degree amp n
        (fun i => tensorVarianceProfile I degree (site i) (monomial i)) p
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates| ≤
      (K*N+2*(∑ i : Fin (n+1), ∑ j, (monomial i j : ℝ)*amp j^2*∑ a, (degree j a : ℝ))) *
        frobeniusDistance U V := by
  let F := fun W => spinPriorFlatLog π eig (specialRotation W) c I degree amp n
    (fun i => tensorVarianceProfile I degree (site i) (monomial i))
  have hi (W : SpecialOrthogonal N) := (spinPriorFlatLog_variance hgauss hN π eig (specialRotation W)
    c I degree amp n b site monomial hb).1.integrable (by norm_num)
  rw [integral_prod _ (hi U), integral_prod _ (hi V),
    ← integral_sub (hi U).integral_prod_left (hi V).integral_prod_left]
  have hh := norm_integral_le_of_norm_le_const
    (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (f := fun T => (∫ z, F U (T,z) ∂gaussianCoordinates)-∫ z, F V (T,z) ∂gaussianCoordinates)
    (C := (K*N+2*(∑ i : Fin (n+1), ∑ j, (monomial i j : ℝ)*amp j^2*∑ a, (degree j a : ℝ)))*frobeniusDistance U V)
    (ae_of_all _ fun T => by
      simpa only [Real.norm_eq_abs, F, spinPriorFlatLog] using
        tensorLeafLogMean_abs_sub_le hN eig c U V K hK heig I degree amp n
          (fun i => site i) (fun i => monomial i) (labeledSpinReference n π T))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

end InvariantIsing

end

end OAI
