import OAI.Probability.InvariantIsing.Cavity.CavityLabeledModel
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledRoot
import OAI.Probability.InvariantIsing.Cavity.CavityMarkDepthLaw

namespace OAI

/-! The independent labeled coordinates give the original common-root
noise-cascade disorder law exactly. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix ENNReal

namespace InvariantIsing

def cavityLabeledNoiseDisorderMap {d : ℕ} (n : ℕ) (ω : CavityLabeledDisorder d n) :
    EuclideanSpace ℝ (Fin d) × NoiseTree (EuclideanSpace ℝ (Fin d)) n :=
  (ω.2.1, labeledNoiseJoin _ n (ω.1, markForestOfCoords _ n ω.2.2))

lemma measurable_cavityLabeledNoiseDisorderMap {d : ℕ} (n : ℕ) :
    Measurable (cavityLabeledNoiseDisorderMap (d := d) n) := by
  unfold cavityLabeledNoiseDisorderMap
  fun_prop

theorem cavity_labeled_noise_disorder_law {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ) :
    MeasurePreserving (cavityLabeledNoiseDisorderMap n)
      (cavityLabeledDisorderLaw n b S₀ S)
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _)) := by
  let PT := (labeledCascadeLaw n b : Measure (LabeledTree n))
  let PS := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀
  let PG := Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
    (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v)))
  have hnoise : MeasurePreserving
      (fun p : LabeledTree n × (ForestVertex n → EuclideanSpace ℝ (Fin d)) =>
        labeledNoiseJoin _ n (p.1, markForestOfCoords _ n p.2))
      (PT.prod PG)
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _) :=
    ⟨by fun_prop, labeledNoiseCoordinates_law _ n b (cavityGaussianMarks S)⟩
  have h1 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc PT PS PG)
  have h2 := (Measure.measurePreserving_swap (μ := PT) (ν := PS)).prod (MeasurePreserving.id PG)
  have h3 := measurePreserving_prodAssoc PS PT PG
  have h4 := (MeasurePreserving.id PS).prod hnoise
  exact h4.comp (h3.comp (h2.comp h1))

lemma cavity_labeled_disorder_good {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hb : CascadeExponents n b) :
    ∀ᵐ ω ∂cavityLabeledDisorderLaw n b S₀ S,
      GoodNoiseTree _ n (cavityLabeledNoiseDisorderMap n ω).2 ∧
      (0 < noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 ∧
        noiseTreeTotal _ n (cavityLabeledNoiseDisorderMap n ω).2 < ∞) := by
  have hnoise := (noiseCascade_good (EuclideanSpace ℝ (Fin d)) n b hb
      (cavityGaussianMarks S)).and
    (cavity_noiseTreeTotal_pos_finite n b hb (cavityGaussianMarks S))
  let Q := (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b
    (cavityGaussianMarks S) : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n))
  have hsnd : MeasurePreserving Prod.snd
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod Q) Q :=
    measurePreserving_snd
  have hp := hsnd.quasiMeasurePreserving.ae hnoise
  exact (cavity_labeled_noise_disorder_law n b S₀ S).quasiMeasurePreserving.ae hp

lemma cavity_labeled_disorder_injective {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hAtom : ∀ i < n,
      NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i))) :
    ∀ᵐ ω ∂cavityLabeledDisorderLaw n b S₀ S, Function.Injective ω.2.2 := by
  have hg := cavity_atomless_marks_injective n (cavityGaussianMarks S) hAtom
  have hs := (measurePreserving_snd
    (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀)
    (ν := Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))).quasiMeasurePreserving.ae hg
  exact (measurePreserving_snd
    (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (ν := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v)))))).quasiMeasurePreserving.ae hs

end InvariantIsing

end

end OAI
