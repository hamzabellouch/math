import OAI.Probability.InvariantIsing.Fields.CascadeMarking
import OAI.Probability.IsingPerceptron.RetainedDisplacement

namespace OAI

/-! Gaussian `log cosh` marking preserves the unmarked cascade law. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

def gaussianCascadeMarks (v : ℕ → ℝ≥0) (i : ℕ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 (v i), inferInstance⟩

def gaussianCascadeUpdate (n : ℕ) : ℕ → ℝ × ℝ → ℝ :=
  IsingPerceptron.stoppedUpdate n (fun _ p => p.1 + p.2)

def gaussianCascadeBackward (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (i : ℕ) : ℝ → ℝ :=
  IsingPerceptron.backwardValue n b (gaussianCascadeMarks v)
    (fun _ p => p.1 + p.2) (fun x => Real.log (Real.cosh x)) i

def gaussianCascadeMultiplier (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (i : ℕ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (gaussianCascadeBackward n b v (i + 1) (gaussianCascadeUpdate n i p) -
    gaussianCascadeBackward n b v i p.1)

lemma measurable_gaussianCascadeUpdate (n i : ℕ) : Measurable (gaussianCascadeUpdate n i) :=
  IsingPerceptron.measurable_stoppedUpdate n (fun _ => measurable_fst.add measurable_snd) i

lemma measurable_gaussianCascadeBackward (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (i : ℕ) :
    Measurable (gaussianCascadeBackward n b v i) :=
  IsingPerceptron.measurable_backwardValue n b (gaussianCascadeMarks v)
    (fun _ => measurable_fst.add measurable_snd) IsingPerceptron.measurable_logCosh i

lemma measurable_gaussianCascadeMultiplier (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (i : ℕ) :
    Measurable (gaussianCascadeMultiplier n b v i) :=
  (((measurable_gaussianCascadeBackward n b v (i + 1)).comp
    (measurable_gaussianCascadeUpdate n i)).sub
    ((measurable_gaussianCascadeBackward n b v i).comp measurable_fst)).exp

lemma gaussianCascadeMultiplier_pos (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (i : ℕ) (x g : ℝ) : 0 < gaussianCascadeMultiplier n b v i (x, g) :=
  Real.exp_pos _

/-- Every edge multiplier is normalized under the exponent of its cascade level. -/
lemma gaussianCascadeMultiplier_moment (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (i : ℕ) (x : ℝ) :
    (∫⁻ g, ENNReal.ofReal (gaussianCascadeMultiplier n b v i (x, g) ^ b i)
      ∂gaussianReal 0 (v i)) = 1 := by
  have hadm := IsingPerceptron.backwardValue_linearGrowth_moments n b (gaussianCascadeMarks v)
    (fun j _ => IsingPerceptron.gaussianReal_exponentialNormMoments 0 (v j))
    IsingPerceptron.measurable_logCosh IsingPerceptron.logCosh_linearGrowth
    (fun j hj => (hb.1 j hj).1)
  exact IsingPerceptron.backwardValue_multiplier_moment_admissible n b
    (gaussianCascadeMarks v) (fun _ p => p.1 + p.2) (fun z => Real.log (Real.cosh z))
    (fun j hj => (hb.1 j hj).1) hadm i x

def gaussianCascadeDisplacement (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (x : ℝ) :
    IsingPerceptron.NoiseTree ℝ n → IsingPerceptron.RawTree n :=
  IsingPerceptron.noiseTreeDisplace n b (gaussianCascadeMarks v)
    (gaussianCascadeMultiplier n b v) (gaussianCascadeUpdate n) x

/-- The exact unmarked-law part of `arr:rpc` for Gaussian `log cosh` marks. -/
theorem gaussianCascadeDisplacement_law (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (x : ℝ) :
    (gaussianCascadeLaw n b v).map (gaussianCascadeDisplacement n b v x) =
      IsingPerceptron.rawCascadeLaw n b := by
  exact IsingPerceptron.noiseTreeDisplace_law n b (gaussianCascadeMarks v)
    (measurable_gaussianCascadeMultiplier n b v) (measurable_gaussianCascadeUpdate n)
    (gaussianCascadeMultiplier_pos n b v) (gaussianCascadeMultiplier_moment n b v hb) x

end InvariantIsing

end

end OAI
