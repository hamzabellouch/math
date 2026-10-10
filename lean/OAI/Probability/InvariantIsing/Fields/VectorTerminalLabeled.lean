import OAI.Probability.InvariantIsing.Fields.VectorTerminalNoise
import OAI.Probability.InvariantIsing.Pressure.GibbsMap
import OAI.Probability.InvariantIsing.Core.ReferenceInfiniteReplicas

namespace OAI

/-! Original labeled Gibbs laws for finite Gaussian vector terminals. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

abbrev VectorTerminalCoordinates (N n : ℕ) := LabeledTree n × (ForestVertex n → Fin N → ℝ)

def vectorTerminalCoordinateLaw (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) : Measure (VectorTerminalCoordinates N n) :=
  (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
    (Measure.infinitePi fun a : ForestVertex n => (vectorGaussianLaw N (v (forestVertexDepth n a)) : Measure (Fin N → ℝ)))

instance vectorTerminalCoordinateLaw_probability (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) :
    IsProbabilityMeasure (vectorTerminalCoordinateLaw N n b v) := by
  unfold vectorTerminalCoordinateLaw
  infer_instance

def vectorLabeledTerminalLaw (N n : ℕ) (F : (Fin N → ℝ) → ℝ)
    (z : Fin N → ℝ) (p : VectorTerminalCoordinates N n) : Measure (LabeledLeaf n) :=
  gibbsProbability (labeledLeafLaw n p.1)
    (fun α => F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z))

instance vectorLabeledTerminalLaw_probability (N n : ℕ) (F : (Fin N → ℝ) → ℝ)
    (z : Fin N → ℝ) (p : VectorTerminalCoordinates N n) :
    IsProbabilityMeasure (vectorLabeledTerminalLaw N n F z p) := by
  unfold vectorLabeledTerminalLaw
  infer_instance

lemma measurable_vectorLabeledTerminalLaw (N n : ℕ) (F : (Fin N → ℝ) → ℝ) (hF : Measurable F)
    (z : Fin N → ℝ) : Measurable (vectorLabeledTerminalLaw N n F z) := by
  unfold vectorLabeledTerminalLaw
  apply measurable_gibbsProbability (ν := fun p : VectorTerminalCoordinates N n => labeledLeafLaw n p.1)
    (H := fun p : VectorTerminalCoordinates N n × LabeledLeaf n =>
      F (labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.1.2) p.2 z))
    ((measurable_labeledLeafLaw n).comp measurable_fst)
  apply measurable_from_prod_countable_left
  intro α
  exact hF.comp ((measurable_labeledEnergy n α).comp
    (((measurable_markForestOfCoords _ n).comp measurable_snd).prodMk measurable_const))

lemma vectorLeafSum_labeled (N n : ℕ) (z : Fin N → ℝ) (p : VectorTerminalCoordinates N n)
    (α : LabeledLeaf n) :
    vectorLeafSum N n z (labeledNoiseLeaf (Fin N → ℝ) n (p.1,markForestOfCoords (Fin N → ℝ) n p.2) α) =
      labeledEnergy n (markForestOfCoords (Fin N → ℝ) n p.2) α z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    exact ih (z+p.2 (α.1.1,α.1.2,none))
      (p.1.2 α.1.1 α.1.2,fun a => p.2 (α.1.1,α.1.2,some a)) α.2

end InvariantIsing

end

end OAI
