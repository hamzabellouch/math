import OAI.Probability.FreeIsing.Conditioning.CenteredCopyDifference
import OAI.Probability.FreeIsing.Gaussian.BernoulliSpectral

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.CopyDifference

variable {d : ℕ} {B : Type*} [MeasurableSpace B] {ν : Measure B}
variable {p q : B → (TreeVertex d → ℝ)}

def bernoulliAverageOnDifferences
    (hp : MeasurePreserving p ν (labelMeasure d))
    (hq : MeasurePreserving q ν (labelMeasure d))
    (σ : Fin d → B → B) (hσ : ∀ c, MeasurePreserving (σ c) ν ν)
    (hpc : ∀ c, p ∘ σ c = TreeKoopman.reflection c ∘ p)
    (hqc : ∀ c, q ∘ σ c = TreeKoopman.reflection c ∘ q) :
    rangeClosure (operator hp hq) →L[ℝ] rangeClosure (operator hp hq) :=
  averageOnDifferences hp hq TreeKoopman.reflection σ
    TreeKoopman.reflection_measurePreserving hσ hpc hqc

theorem bernoulliAverageOnDifferences_isSelfAdjoint
    (hp : MeasurePreserving p ν (labelMeasure d))
    (hq : MeasurePreserving q ν (labelMeasure d))
    (σ : Fin d → B → B) (hσ : ∀ c, MeasurePreserving (σ c) ν ν)
    (hσinv : ∀ c, Function.Involutive (σ c))
    (hpc : ∀ c, p ∘ σ c = TreeKoopman.reflection c ∘ p)
    (hqc : ∀ c, q ∘ σ c = TreeKoopman.reflection c ∘ q) :
    IsSelfAdjoint (bernoulliAverageOnDifferences hp hq σ hσ hpc hqc) :=
  averageOnDifferences_isSelfAdjoint hp hq TreeKoopman.reflection σ
    TreeKoopman.reflection_measurePreserving hσ hσinv hpc hqc

theorem bernoulliAverageOnDifferences_norm_le (hd : 3 ≤ d)
    (hp : MeasurePreserving p ν (labelMeasure d))
    (hq : MeasurePreserving q ν (labelMeasure d))
    (σ : Fin d → B → B) (hσ : ∀ c, MeasurePreserving (σ c) ν ν)
    (hσinv : ∀ c, Function.Involutive (σ c))
    (hpc : ∀ c, p ∘ σ c = TreeKoopman.reflection c ∘ p)
    (hqc : ∀ c, q ∘ σ c = TreeKoopman.reflection c ∘ q) :
    ‖bernoulliAverageOnDifferences hp hq σ hσ hpc hqc‖ ≤
      2 * Real.sqrt ((d : ℝ) - 1) / d := by
  apply norm_averageOnDifferences_le hp hq TreeKoopman.reflection σ
    TreeKoopman.reflection_measurePreserving hσ
    TreeKoopman.reflection_involutive hσinv hpc hqc
  · positivity
  · exact TreeKoopman.centeredAverage_norm_le hd

end Problem367.CopyDifference

end

end OAI
