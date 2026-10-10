import OAI.Probability.InvariantIsing.Arrays.NSpinTensorRootVariance

namespace OAI

/-! Gaussian-root and cascade fluctuations for the finite tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma measurable_tensorCascadeLog_joint {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (n : ℕ) :
    Measurable (fun p : (SpinTensorIndex I degree → ℝ) ×
      IsingPerceptron.NoiseTree (SpinTensorIndex I degree → ℝ) n =>
      tensorCascadeLog eig U c I degree amplitude n p.1 p.2) := by
  have hm := ((IsingPerceptron.measurable_noiseLeafTerminal n
    (fun _ => measurable_spinTensorTerminal eig U c I degree amplitude)
    (fun _ => measurable_fst.add measurable_snd)).comp
      (show Measurable (fun p : ((SpinTensorIndex I degree → ℝ) ×
          IsingPerceptron.NoiseTree (SpinTensorIndex I degree → ℝ) n) ×
          IsingPerceptron.NoiseLeaf (SpinTensorIndex I degree → ℝ) n => (p.1.1, p.2))
        from by fun_prop)).exp
  exact (hm.stronglyMeasurable.integral_kernel_prod_right'
    (κ := (IsingPerceptron.noiseLeafKernel (SpinTensorIndex I degree → ℝ) n).comap
      Prod.snd measurable_snd)).measurable.log

lemma tensorCascadeValue_root_memLp_two {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
    MemLp (tensorCascadeValue eig U c I degree amplitude n b v) 2
      (tensorGaussianLaw I degree (tensorVarianceProfile I degree site monomial) :
        Measure (SpinTensorIndex I degree → ℝ)) := by
  let F := fun g : TensorGaussianSpace I degree =>
    tensorCascadeValue eig U c I degree amplitude n b v
      (tensorRootMark I degree (tensorVarianceProfile I degree site monomial) g)
  have hLip := tensorCascadeValue_root_lipschitz hN eig U c I degree amplitude n b v hb site monomial 0
  simp only [zero_add] at hLip
  let B : ℝ≥0 := ⟨(site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2,
    add_nonneg (mul_nonneg (NNReal.coe_nonneg _) (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _j _ => mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))⟩
  have hLip0 : LipschitzWith (NNReal.sqrt B) (fun g => F g - F 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro g h
    simpa only [dist_sub_right] using hLip.dist_le_mul g h
  have hL := hLip0.comp_memLp (by simp)
    (IsGaussian.memLp_two_id : MemLp id 2 (stdGaussian (TensorGaussianSpace I degree)))
  have hF : MemLp F 2 (stdGaussian (TensorGaussianSpace I degree)) := by
    convert hL.add (memLp_const (F 0)) using 1
    ext g
    simp only [Pi.add_apply, Function.comp_apply, id_eq, sub_add_cancel]
  have hm : Measurable (tensorCascadeValue eig U c I degree amplitude n b v) :=
    IsingPerceptron.measurable_cascadeRecursion n b (fun i => tensorGaussianLaw I degree (v i))
      (fun _ => measurable_fst.add measurable_snd) (measurable_spinTensorTerminal eig U c I degree amplitude)
  have hmp := tensorRootMark_measurePreserving I degree (tensorVarianceProfile I degree site monomial)
  rw [← hmp.map_eq]
  exact (memLp_map_measure_iff hm.aestronglyMeasurable hmp.aemeasurable).mpr hF

/-- The actual log partition on the product of root marks and marked
cascade trees has variance bounded by the sum of the two contributions. -/
theorem tensorCascadeLog_root_tree_variance_le (hpub : GaussianLipschitzVarianceInput)
    {N m k : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
    let root := tensorGaussianLaw I degree (tensorVarianceProfile I degree site monomial)
    let P := (root : Measure (SpinTensorIndex I degree → ℝ)).prod (tensorCascadeLaw I degree n b v)
    let F := fun p : (SpinTensorIndex I degree → ℝ) ×
      IsingPerceptron.NoiseTree (SpinTensorIndex I degree → ℝ) n =>
      tensorCascadeLog eig U c I degree amplitude n p.1 p.2
    MemLp F 2 P ∧ variance F P ≤
      4 * (∫ T, (Real.log (IsingPerceptron.rawTreeTotal n T).toReal) ^ 2
        ∂(IsingPerceptron.rawCascadeLaw n b : Measure (IsingPerceptron.RawTree n))) +
      (site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2 := by
  intro root P F
  let : IsProbabilityMeasure (tensorCascadeLaw I degree n b v) :=
    (IsingPerceptron.noiseCascadeLaw (SpinTensorIndex I degree → ℝ) n b
      (fun i => tensorGaussianLaw I degree (v i))).prop
  have h := IsingPerceptron.variance_of_conditional_center
    (root : Measure (SpinTensorIndex I degree → ℝ)) (tensorCascadeLaw I degree n b v)
    (measurable_tensorCascadeLog_joint eig U c I degree amplitude n)
    (tensorCascadeValue_root_memLp_two hN eig U c I degree amplitude n b v hb site monomial)
    (fun z => (tensorCascadeLog_recursion hN eig U c I degree amplitude n b v hb z).2.2.1)
    (fun z => (tensorCascadeLog_recursion hN eig U c I degree amplitude n b v hb z).2.1)
    (fun z => (tensorCascadeLog_recursion hN eig U c I degree amplitude n b v hb z).2.2.2)
  refine ⟨h.1, ?_⟩
  have hv := tensorCascadeValue_root_variance_le hpub hN eig U c I degree amplitude n b v hb site monomial
  exact h.2.trans (by linarith)

/-- For pressure, the Gaussian-root and cascade contributions scale by
the square of the volume. The rotation remains fixed in this statement. -/
theorem normalized_tensorCascadeLog_root_tree_variance_le (hpub : GaussianLipschitzVarianceInput)
    {N m k : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
    let root := tensorGaussianLaw I degree (tensorVarianceProfile I degree site monomial)
    let P := (root : Measure (SpinTensorIndex I degree → ℝ)).prod (tensorCascadeLaw I degree n b v)
    let F := fun p : (SpinTensorIndex I degree → ℝ) ×
      IsingPerceptron.NoiseTree (SpinTensorIndex I degree → ℝ) n =>
      tensorCascadeLog eig U c I degree amplitude n p.1 p.2
    MemLp (fun p => (N : ℝ)⁻¹ * F p) 2 P ∧
      variance (fun p => (N : ℝ)⁻¹ * F p) P ≤
        (4 * (∫ T, (Real.log (IsingPerceptron.rawTreeTotal n T).toReal) ^ 2
          ∂(IsingPerceptron.rawCascadeLaw n b : Measure (IsingPerceptron.RawTree n))) +
        (site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2) / (N : ℝ) ^ 2 := by
  intro root P F
  have h := tensorCascadeLog_root_tree_variance_le hpub hN eig U c I degree amplitude n b v hb site monomial
  refine ⟨h.1.const_mul (N : ℝ)⁻¹, ?_⟩
  rw [variance_const_mul]
  have hbnd := mul_le_mul_of_nonneg_left h.2 (sq_nonneg (N : ℝ)⁻¹)
  convert hbnd using 1
  ring

end InvariantIsing

end

end OAI
