import OAI.Probability.InvariantIsing.Cavity.CavityFullMoment
import OAI.Probability.InvariantIsing.Cavity.CavityRadiusRemoval

namespace OAI

/-! A total probability-kernel version of the full cavity Gibbs law.
Its fallback on a nonintegrable fiber is irrelevant on the proved full-measure set. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityRootedFullGibbs {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    Kernel (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
      ((EuclideanSpace ℝ (Fin d) ×
        (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d))) × Spin k) := by
  let ν := cavityRootedPriorKernel n R ×ₖ Kernel.const _ π
  let V : (EuclideanSpace ℝ (Fin d) × NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
      EuclideanSpace ℝ (Fin d)) × Spin k → ℝ :=
    fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2
  let W : (EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n) ×
      ((EuclideanSpace ℝ (Fin d) × NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
        EuclideanSpace ℝ (Fin d)) × Spin k) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Real.exp (V p.2))
  have hW : Measurable W :=
    (((measurable_cavityRootedLogFactor n K L C).comp measurable_snd).exp.ennreal_ofReal)
  have hm := measurable_normalizeMass.comp
    (measurable_random_withDensity (ν := ν) (W := W) ν.measurable hW)
  exact ⟨fun ω => normalizeMass ((ν ω).withDensity (fun z => W (ω, z))), hm⟩

instance cavityRootedFullGibbs_markov {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    IsMarkovKernel (cavityRootedFullGibbs n K R L C π) := by
  constructor
  intro ω
  exact normalizeMass_probability _

theorem cavityRootedFullGibbs_eq_tilted {d k : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (ω : EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (he : Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
      ((cavityRootedPriorKernel n R ω).prod π)) :
    cavityRootedFullGibbs n K R L C π ω =
      ((cavityRootedPriorKernel n R ω).prod π).tilted
        (fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2) := by
  change normalizeMass _ = _
  simp only [Kernel.prod_apply, Kernel.const_apply]
  exact normalizeMass_exp _ _ (measurable_cavityRootedLogFactor n K L C) he

end InvariantIsing

end

end OAI
