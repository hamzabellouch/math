import OAI.Probability.InvariantIsing.Fields.SpinPriorRootVariance

namespace OAI

/-! Actual root/cascade fluctuations and their flat Gaussian realization,
uniformly over probability spin priors. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def spinPriorFlatLog {N m k : ℕ} (π : Measure (Spin N))
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (p : LabeledTree n × (ℕ → ℝ)) : ℝ :=
  Real.log (∫ x : Spin N × LabeledLeaf n,
    Real.exp (rotatedEnergy eig U x.1+fieldEnergy c x.1+
      cylinderField (tensorLeafCoefficients U I degree amp n (fun i => v i) x) p.2)
    ∂labeledSpinReference n π p.1)

lemma spinPriorFlatLog_eq_labeled {N m k : ℕ} (π : Measure (Spin N))
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (p : LabeledTree n × (ℕ → ℝ)) :
    spinPriorFlatLog π eig U c I degree amp n v p =
      spinPriorLabeledLog π eig U c I degree amp n
        (tensorFlatToLabeled U I degree amp n v p).1 (tensorFlatToLabeled U I degree amp n v p).2 := by
  apply congrArg Real.log
  apply integral_congr_ae
  exact ae_of_all _ fun x => congrArg Real.exp
    (tensorLabeledEnergy_flat_eq eig U c I degree amp n v p x).symm

lemma spinPriorLabeledLog_root_variance (hpub : GaussianLipschitzVarianceInput)
    {N m k : ℕ} (hN : 0 < N) (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
    let P := (tensorGaussianLaw I degree (tensorVarianceProfile I degree site monomial) : Measure _).prod
      (tensorLabeledLaw U I degree amp n b v)
    let F := fun q => spinPriorLabeledLog π eig U c I degree amp n q.1 q.2
    MemLp F 2 P ∧ variance F P ≤
      4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)))+
        (site : ℝ)*N+∑ j, (monomial j : ℝ)*amp j^2 := by
  intro P F
  have hr := spinPriorCascadeValue_root_memLp_variance hpub hN π eig U c I degree amp n b v hb site monomial
  have hc z := spinPriorLabeledLog_conditional hN π eig U c I degree amp n b v hb z
  have hs := variance_of_conditional_center
    (tensorGaussianLaw I degree (tensorVarianceProfile I degree site monomial) : Measure _)
    (tensorLabeledLaw U I degree amp n b v)
    (measurable_spinPriorLabeledLog_root π eig U c I degree amp n)
    hr.1 (fun z => (hc z).2.2.1) (fun z => (hc z).2.1) (fun z => (hc z).2.2.2)
  exact ⟨hs.1, hs.2.trans (by linarith [hr.2])⟩

theorem spinPriorFlatLog_variance (hpub : GaussianLipschitzVarianceInput)
    {N m k : ℕ} (hN : 0 < N) (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (site : ℕ → ℝ≥0) (monomial : ℕ → Fin k → ℝ≥0)
    (hb : CascadeExponents n b) :
    let v := fun i => tensorVarianceProfile I degree (site i) (monomial i)
    let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates
    let F := spinPriorFlatLog π eig U c I degree amp n v
    MemLp F 2 P ∧ variance F P ≤
      4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)))+
        (site 0 : ℝ)*N+∑ j, (monomial 0 j : ℝ)*amp j^2 := by
  intro v P F
  let G := fun q : (SpinTensorIndex I degree → ℝ) × TensorLabeledData N n => spinPriorLabeledLog π eig U c I degree amp n q.1 q.2
  have hp := tensorFlatToLabeled_measurePreserving U I degree amp n b v
  have hm := measurable_spinPriorLabeledLog_root π eig U c I degree amp n
  have he : F = G ∘ tensorFlatToLabeled U I degree amp n v :=
    funext (spinPriorFlatLog_eq_labeled π eig U c I degree amp n v)
  have hv := spinPriorLabeledLog_root_variance hpub hN π eig U c I degree amp n b
    (fun i => v (i+1)) hb (site 0) (monomial 0)
  rw [he]
  refine ⟨hv.1.comp_measurePreserving hp, ?_⟩
  exact (hp.variance_fun_comp hm.aemeasurable).trans_le hv.2

end InvariantIsing

end

end OAI
