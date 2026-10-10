import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFrozenCGF
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorHaarFluctuation

namespace OAI

/-! The actual flat spin/leaf pressure and marked-cascade pressure have the same law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal ENNReal

namespace InvariantIsing

def tensorFlatToNoise {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (p : LabeledTree n × (ℕ → ℝ)) :
    (SpinTensorIndex I degree → ℝ) × NoiseTree (SpinTensorIndex I degree → ℝ) n :=
  let q := tensorFlatToCoordinates I degree n v p
  (q.1, labeledNoiseJoin (SpinTensorIndex I degree → ℝ) n
    (q.2.1, markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2.2))

theorem tensorFlatToNoise_measurePreserving {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorFlatToNoise I degree n v)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates)
      (tensorRootTreeLaw I degree n b (fun i => v (i + 1)) (v 0)) := by
  have hp : MeasurePreserving (fun q : TensorCoordinateData I degree n =>
      labeledNoiseJoin (SpinTensorIndex I degree → ℝ) n
        (q.1, markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2))
      (tensorCoordinateLaw I degree n b (fun i => v (i + 1)))
      (tensorCascadeLaw I degree n b (fun i => v (i + 1))) :=
    ⟨by fun_prop, labeledNoiseCoordinates_law (SpinTensorIndex I degree → ℝ) n b
      (fun i => tensorGaussianLaw I degree (v (i + 1)))⟩
  have h := ((MeasurePreserving.id (tensorGaussianLaw I degree (v 0) :
      Measure (SpinTensorIndex I degree → ℝ))).prod hp).comp
    (tensorFlatToCoordinates_measurePreserving I degree n b v)
  convert h using 1
  · rfl
  · rfl

private lemma spinTensorEnergy_labeled {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ)
    (G : ForestVertex n → SpinTensorIndex I degree → ℝ) (leaf : LabeledLeaf n) (σ : Spin N) :
    spinTensorEnergy U I degree amplitude
      (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n G) leaf z) σ =
      spinTensorEnergy U I degree amplitude z σ +
        ∑ i : Fin n, spinTensorEnergy U I degree amplitude (G (edgeAt n leaf i)) σ := by
  unfold spinTensorEnergy
  simp only [labeledEnergy_edge_sum, add_mul, Finset.sum_add_distrib]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma tensorCoordinateLog_eq_terminal {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (q : TensorCoordinateData I degree n) :
    Real.log (∫ x, Real.exp (tensorLabeledEnergy eig U c I degree amplitude n z
      (tensorEnergyCoordinates U I degree amplitude n q) x)
      ∂tensorLabeledReference N n (tensorEnergyCoordinates U I degree amplitude n q)) =
      Real.log (∫ leaf, Real.exp (spinTensorTerminal eig U c I degree amplitude
        (labeledEnergy n (markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2) leaf z))
        ∂labeledLeafLaw n q.1) := by
  let H := tensorSpinBaseEnergy eig U c I degree amplitude z
  let G := markForestOfCoords (Spin N → ℝ) n
    (fun w => spinTensorEnergy U I degree amplitude (q.2 w))
  have he (x : Spin N × LabeledLeaf n) : tensorLabeledEnergy eig U c I degree amplitude n z
      (tensorEnergyCoordinates U I degree amplitude n q) x = labeledEnergy n G x.2 H x.1 := by
    rw [labeledEnergy_edge_sum]
    rfl
  simp_rw [he]
  change labeledEnergyLog n (uniformSpinPrior N : Measure (Spin N)) H (q.1, G) = _
  rw [labeledEnergyLog_eq_leaf]
  apply congrArg Real.log
  apply integral_congr_ae
  refine ae_of_all _ fun leaf => ?_
  apply congrArg Real.exp
  rw [finiteLogIntegral_uniformSpinPrior]
  unfold spinTensorTerminal
  congr 1
  funext σ
  rw [spinTensorEnergy_labeled, labeledEnergy_edge_sum]
  change (rotatedEnergy eig U σ + fieldEnergy c σ + spinTensorEnergy U I degree amplitude z σ) + _ = _
  ring

/-- On every good marked tree the coordinate partition is exactly the
actual marked-cascade partition, uniformly in its rotation and root mark. -/
theorem tensorCoordinateLog_eq_noise {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ) (q : TensorCoordinateData I degree n)
    (hg : GoodNoiseTree (SpinTensorIndex I degree → ℝ) n
      (labeledNoiseJoin (SpinTensorIndex I degree → ℝ) n
        (q.1, markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2)))
    (ht : 0 < noiseTreeTotal (SpinTensorIndex I degree → ℝ) n
        (labeledNoiseJoin (SpinTensorIndex I degree → ℝ) n
          (q.1, markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2)) ∧
      noiseTreeTotal (SpinTensorIndex I degree → ℝ) n
        (labeledNoiseJoin (SpinTensorIndex I degree → ℝ) n
          (q.1, markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2)) < ∞) :
    Real.log (∫ x, Real.exp (tensorLabeledEnergy eig U c I degree amplitude n z
      (tensorEnergyCoordinates U I degree amplitude n q) x)
      ∂tensorLabeledReference N n (tensorEnergyCoordinates U I degree amplitude n q)) =
      tensorCascadeLog eig U c I degree amplitude n z
        (labeledNoiseJoin (SpinTensorIndex I degree → ℝ) n
          (q.1, markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2)) := by
  rw [tensorCoordinateLog_eq_terminal]
  have he := labeled_terminal_integral n q.1
    (markForestOfCoords (SpinTensorIndex I degree → ℝ) n q.2) hg ht
    (X := fun _ => spinTensorTerminal eig U c I degree amplitude) (u := fun _ p => p.1 + p.2)
    (fun _ => measurable_spinTensorTerminal eig U c I degree amplitude)
    (fun _ => measurable_fst.add measurable_snd) z
  simp only [labeledEnergy_terminal] at he
  exact congrArg Real.log he


/-- The good-tree event is independent of the terminal energy, so this
identity holds simultaneously for every rotation on one full-measure set. -/
theorem tensorFlatLog_eq_noise_ae {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (hb : CascadeExponents n b) :
    ∀ᵐ p : LabeledTree n × (ℕ → ℝ)
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates,
      ∀ U : Rotation N, tensorFlatLog eig U c I degree amplitude n v p =
        tensorCascadeLog eig U c I degree amplitude n (tensorFlatToNoise I degree n v p).1
          (tensorFlatToNoise I degree n v p).2 := by
  let M := (SpinTensorIndex I degree → ℝ)
  let ν := fun i => tensorGaussianLaw I degree (v (i + 1))
  let : IsProbabilityMeasure (tensorCascadeLaw I degree n b (fun i => v (i + 1))) :=
    (noiseCascadeLaw M n b ν).prop
  have hp := tensorFlatToNoise_measurePreserving I degree n b v
  have hg : ∀ᵐ T ∂tensorCascadeLaw I degree n b (fun i => v (i + 1)), GoodNoiseTree M n T :=
    noiseCascade_good M n b hb ν
  have ht : ∀ᵐ T ∂tensorCascadeLaw I degree n b (fun i => v (i + 1)),
      0 < noiseTreeTotal M n T ∧ noiseTreeTotal M n T < ∞ := by
    apply ae_of_ae_map (p := fun T : RawTree n => 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞)
      (measurable_noiseTreeForget M n).aemeasurable
    change ∀ᵐ T : RawTree n ∂(noiseCascadeLaw M n b ν : Measure (NoiseTree M n)).map
      (noiseTreeForget M n), 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞
    rw [noiseCascadeLaw_forget]
    exact (rawCascade_total_moments n b hb).1
  have hproj := measurePreserving_snd (μ := (tensorGaussianLaw I degree (v 0) : Measure M))
    (ν := tensorCascadeLaw I degree n b (fun i => v (i + 1)))
  have hg' := hp.quasiMeasurePreserving.ae (hproj.quasiMeasurePreserving.ae hg)
  have ht' := hp.quasiMeasurePreserving.ae (hproj.quasiMeasurePreserving.ae ht)
  filter_upwards [hg', ht'] with p hgp htp
  intro U
  let q := tensorFlatToCoordinates I degree n v p
  have he : tensorFlatLog eig U c I degree amplitude n v p =
      Real.log (∫ x, Real.exp (tensorLabeledEnergy eig U c I degree amplitude n q.1
        (tensorEnergyCoordinates U I degree amplitude n q.2) x)
        ∂tensorLabeledReference N n (tensorEnergyCoordinates U I degree amplitude n q.2)) := by
    apply congrArg Real.log
    apply integral_congr_ae
    exact ae_of_all _ fun x => congrArg Real.exp
      (tensorLabeledEnergy_flat_eq eig U c I degree amplitude n v p x).symm
  exact he.trans (tensorCoordinateLog_eq_noise eig U c I degree amplitude n q.1 q.2 hgp htp)

def tensorFlatToDisorder {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) :
    SpecialOrthogonal N × ((SpinTensorIndex I degree → ℝ) × NoiseTree (SpinTensorIndex I degree → ℝ) n) :=
  (p.1.1, tensorFlatToNoise I degree n v (p.1.2, p.2))

theorem tensorFlatToDisorder_measurePreserving {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorFlatToDisorder I degree n v)
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)
      (μ.prod (tensorRootTreeLaw I degree n b (fun i => v (i + 1)) (v 0))) := by
  have hp := ((MeasurePreserving.id μ).prod
    (tensorFlatToNoise_measurePreserving I degree n b v)).comp
    (measurePreserving_prodAssoc μ (labeledCascadeLaw n b : Measure (LabeledTree n)) gaussianCoordinates)
  convert hp using 1
  rfl

/-- Exact almost-everywhere pressure identification with the actual
three-disorder model, suitable for transporting moments and variance. -/
theorem tensorFlatPressure_eq_disorder_ae {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (hb : CascadeExponents n b) :
    (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
      (N : ℝ)⁻¹ * tensorFlatLog eig (specialRotation p.1.1) c I degree amplitude n v (p.1.2, p.2)) =ᵐ[
      (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates]
    (tensorDisorderPressure eig c I degree amplitude n ∘ tensorFlatToDisorder I degree n v) := by
  have hproj := (measurePreserving_snd (μ := μ)
    (ν := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates)).comp
    (measurePreserving_prodAssoc μ (labeledCascadeLaw n b : Measure (LabeledTree n)) gaussianCoordinates)
  have he := hproj.quasiMeasurePreserving.ae (tensorFlatLog_eq_noise_ae eig c I degree amplitude n b v hb)
  filter_upwards [he] with p hp
  exact congrArg ((N : ℝ)⁻¹ * ·) (hp (specialRotation p.1.1))

end InvariantIsing

end

end OAI
