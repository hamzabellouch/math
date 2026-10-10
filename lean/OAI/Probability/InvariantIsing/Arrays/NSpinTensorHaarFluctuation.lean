import OAI.Probability.InvariantIsing.Arrays.NSpinTensorHaar
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFluctuation

namespace OAI

/-! Full Haar, Gaussian-root, and cascade fluctuations for the actual finite tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- Independent common Gaussian root and marked cascade. -/
def tensorRootTreeLaw {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (root : SpinTensorIndex I degree → ℝ≥0) :
    Measure ((SpinTensorIndex I degree → ℝ) × NoiseTree (SpinTensorIndex I degree → ℝ) n) :=
  (tensorGaussianLaw I degree root : Measure (SpinTensorIndex I degree → ℝ)).prod
    (tensorCascadeLaw I degree n b v)

instance tensorRootTreeLaw_probability {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → SpinTensorIndex I degree → ℝ≥0) (root : SpinTensorIndex I degree → ℝ≥0) :
    IsProbabilityMeasure (tensorRootTreeLaw I degree n b v root) := by
  let : IsProbabilityMeasure (tensorCascadeLaw I degree n b v) :=
    (noiseCascadeLaw (SpinTensorIndex I degree → ℝ) n b
      (fun i => tensorGaussianLaw I degree (v i))).prop
  unfold tensorRootTreeLaw
  infer_instance

/-- The normalized spin/leaf log partition retaining all three disorders. -/
def tensorDisorderPressure {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) (n : ℕ)
    (p : SpecialOrthogonal N × ((SpinTensorIndex I degree → ℝ) ×
      NoiseTree (SpinTensorIndex I degree → ℝ) n)) : ℝ :=
  (N : ℝ)⁻¹ * tensorCascadeLog eig (specialRotation p.1) c I degree amplitude n p.2.1 p.2.2

private lemma measurable_tensorLeafState {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) :
    Measurable (fun p : (SpinTensorIndex I degree → ℝ) × NoiseLeaf (SpinTensorIndex I degree → ℝ) n =>
      tensorLeafState I degree n p.1 p.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    exact ih.comp ((measurable_fst.add measurable_snd.snd.fst).prodMk measurable_snd.snd.snd)

lemma measurable_tensorDisorderPressure {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) (n : ℕ) :
    Measurable (tensorDisorderPressure eig c I degree amplitude n) := by
  let Ω := SpecialOrthogonal N × ((SpinTensorIndex I degree → ℝ) ×
    NoiseTree (SpinTensorIndex I degree → ℝ) n)
  have hs : Measurable (fun p : Ω × NoiseLeaf (SpinTensorIndex I degree → ℝ) n =>
      (p.1.1, tensorLeafState I degree n p.1.2.1 p.2)) :=
    measurable_fst.fst.prodMk ((measurable_tensorLeafState I degree n).comp
      (measurable_fst.snd.fst.prodMk measurable_snd))
  have ht := ((measurable_spinTensorTerminal_joint eig c I degree amplitude).comp hs).exp
  have hi := (ht.stronglyMeasurable.integral_kernel_prod_right'
    (κ := (noiseLeafKernel (SpinTensorIndex I degree → ℝ) n).comap
      (fun p : Ω => p.2.2) measurable_snd.snd)).measurable.log
  have hlog : Measurable (fun p : Ω => tensorCascadeLog eig (specialRotation p.1) c
      I degree amplitude n p.2.1 p.2.2) := by
    simpa only [tensorCascadeLog, noiseLeafTerminal_spinTensorTerminal, Function.comp_apply,
      Kernel.comap_apply] using hi
  exact hlog.const_mul (N : ℝ)⁻¹

lemma tensorDisorderPressure_conditional_mean (hpub : GaussianLipschitzVarianceInput)
    {N m k : ℕ} (hN : 0 < N) (eig c : Fin N → ℝ) (U : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
    (∫ q, tensorDisorderPressure eig c I degree amplitude n (U, q)
      ∂tensorRootTreeLaw I degree n b v (tensorVarianceProfile I degree site monomial)) =
      tensorEnrichedPressure eig (specialRotation U) c I degree amplitude n b v
        (tensorVarianceProfile I degree site monomial) := by
  let : IsProbabilityMeasure (tensorCascadeLaw I degree n b v) :=
    (noiseCascadeLaw (SpinTensorIndex I degree → ℝ) n b
      (fun i => tensorGaussianLaw I degree (v i))).prop
  have h := tensorCascadeLog_root_tree_variance_le hpub hN eig (specialRotation U) c
    I degree amplitude n b v hb site monomial
  unfold tensorDisorderPressure tensorEnrichedPressure tensorRootTreeLaw
  rw [integral_const_mul, integral_prod _ (h.1.integrable (by norm_num))]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun z =>
    (tensorCascadeLog_recursion hN eig (specialRotation U) c I degree amplitude n b v hb z).2.1

/-- The full pressure variance is the sum of the root/cascade conditional
contribution and the Haar variance of its conditional mean. -/
theorem tensorDisorderPressure_variance (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m k : ℕ, ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ degree : Fin k → Fin m → ℕ,
    ∀ amplitude : Fin k → ℝ, ∀ n : ℕ, ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ site : ℕ → ℝ≥0, ∀ monomial : ℕ → Fin k → ℝ≥0,
      let v := fun i => tensorVarianceProfile I degree (site i) (monomial i)
      let P := tensorRootTreeLaw I degree n b (fun i => v (i + 1)) (v 0)
      let F := tensorDisorderPressure eig c I degree amplitude n
      let L := K + 2 * (N : ℝ)⁻¹ *
        (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 * ∑ a, (degree j a : ℝ))
      MemLp F 2 (μ.prod P) ∧ variance F (μ.prod P) ≤
        (4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
          ∂(rawCascadeLaw n b : Measure (RawTree n))) +
          (site 0 : ℝ) * N + ∑ j, (monomial 0 j : ℝ) * amplitude j ^ 2) / (N : ℝ) ^ 2 +
        C * L ^ 2 / N := by
  obtain ⟨C, hC, hHaar⟩ := haar_tensorEnrichedPressure_variance hhaar
  refine ⟨C, hC, ?_⟩
  intro N hN μ hμ hμinv m k eig c K hK heig I degree amplitude n b hb site monomial v P F L
  let : IsProbabilityMeasure μ := hμ
  have hNm : 0 < N := by omega
  let X := fun U : SpecialOrthogonal N => tensorEnrichedPressure eig (specialRotation U) c
    I degree amplitude n b (fun i => v (i + 1)) (v 0)
  have hX := hHaar N hN μ hμ hμinv m k eig c K hK heig I degree amplitude n b hb site monomial
  have hsec (U : SpecialOrthogonal N) : MemLp (fun q => F (U, q)) 2 P ∧
      variance (fun q => F (U, q)) P ≤
        (4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
          ∂(rawCascadeLaw n b : Measure (RawTree n))) +
          (site 0 : ℝ) * N + ∑ j, (monomial 0 j : ℝ) * amplitude j ^ 2) / (N : ℝ) ^ 2 :=
    normalized_tensorCascadeLog_root_tree_variance_le hgauss hNm eig (specialRotation U) c
      I degree amplitude n b (fun i => v (i + 1)) hb (site 0) (monomial 0)
  have hc (U : SpecialOrthogonal N) : (∫ q, F (U, q) ∂P) = X U :=
    tensorDisorderPressure_conditional_mean hgauss hNm eig c U I degree amplitude n b
      (fun i => v (i + 1)) hb (site 0) (monomial 0)
  have hi (U : SpecialOrthogonal N) : Integrable (fun q => (F (U, q) - X U) ^ 2) P :=
    ((hsec U).1.sub (memLp_const (X U))).integrable_sq
  have hbnd (U : SpecialOrthogonal N) : (∫ q, (F (U, q) - X U) ^ 2 ∂P) ≤
        (4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
          ∂(rawCascadeLaw n b : Measure (RawTree n))) +
          (site 0 : ℝ) * N + ∑ j, (monomial 0 j : ℝ) * amplitude j ^ 2) / (N : ℝ) ^ 2 := by
    have he := variance_eq_integral (hsec U).1.aemeasurable
    rw [hc U] at he
    rw [← he]
    exact (hsec U).2
  have h := variance_of_conditional_center μ P
    (measurable_tensorDisorderPressure eig c I degree amplitude n) hX.1 hi hc hbnd
  exact ⟨h.1, h.2.trans (add_le_add_right hX.2 _)⟩

end InvariantIsing

end

end OAI
