import OAI.Probability.InvariantIsing.Arrays.NSpinCascadeFluctuation
import OAI.Probability.InvariantIsing.Arrays.PerturbationFeatures

namespace OAI

/-!
The finite spectral-monomial enriched Ising model. Gaussian marks have a
separate variance at every site/tensor coordinate and every cascade level.
The spectral coefficients retain their actual dependence on the rotation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

abbrev SpinTensorIndex {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) :=
  Fin N ⊕ Sigma (fun j : Fin k => SpectralTensorIndex I (degree j))

def spinTensorFeature {N m k : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) (σ : Spin N) :
    SpinTensorIndex I degree → ℝ
  | Sum.inl i => spinValue (σ i)
  | Sum.inr v => amplitude v.1 * spectralMonomialFeature U I (degree v.1) σ v.2

lemma measurable_spinTensorFeature {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) (σ : Spin N)
    (i : SpinTensorIndex I degree) :
    Measurable (fun U : SpecialOrthogonal N =>
      spinTensorFeature (specialRotation U) I degree amplitude σ i) := by
  cases i with
  | inl i => exact measurable_const
  | inr v => exact (measurable_spectralMonomialFeature I (degree v.1) σ v.2).const_mul _

/-- Variances shared by the coordinates of each spectral monomial. -/
def tensorVarianceProfile {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
    SpinTensorIndex I degree → ℝ≥0
  | Sum.inl _ => site
  | Sum.inr v => monomial v.1

/-- The concrete Gaussian covariance is the linear spin-field kernel plus
the required finite sum of spectral-overlap monomials. -/
theorem spinTensorFeature_covariance {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : ℝ≥0) (monomial : Fin k → ℝ≥0) (σ τ : Spin N) :
    (∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
      spinTensorFeature U I degree amplitude σ i * spinTensorFeature U I degree amplitude τ i) =
      (site : ℝ) * (∑ i, spinValue (σ i) * spinValue (τ i)) +
        ∑ j, (monomial j : ℝ) * amplitude j ^ 2 *
          ∏ a, projectedOverlap U (I a) σ τ ^ degree j a := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [tensorVarianceProfile, spinTensorFeature]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (monomial j : ℝ) * amplitude j ^ 2 *
          ∑ v : SpectralTensorIndex I (degree j),
            spectralMonomialFeature U I (degree j) σ v * spectralMonomialFeature U I (degree j) τ v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by rw [spectralMonomialFeature_cross]

theorem spinTensorFeature_variance_le {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : ℝ≥0) (monomial : Fin k → ℝ≥0) (σ : Spin N) :
    (∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
      spinTensorFeature U I degree amplitude σ i ^ 2) ≤
      (site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2 := by
  have he : (∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
      spinTensorFeature U I degree amplitude σ i ^ 2) =
      ∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
        spinTensorFeature U I degree amplitude σ i * spinTensorFeature U I degree amplitude σ i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, spinTensorFeature_covariance]
  simp only [← sq, spinValue_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  have hp : (∏ a, projectedOverlap U (I a) σ σ ^ degree j a) ≤ 1 :=
    (le_abs_self _).trans (spectralMonomial_abs_le_one U I (degree j) σ σ)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
    (mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))

def spinTensorEnergy {N m k : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (z : SpinTensorIndex I degree → ℝ) (σ : Spin N) : ℝ :=
  ∑ i, z i * spinTensorFeature U I degree amplitude σ i

def spinTensorTerminal {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (z : SpinTensorIndex I degree → ℝ) : ℝ :=
  logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ +
    spinTensorEnergy U I degree amplitude z σ)

lemma measurable_spinTensorTerminal {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) :
    Measurable (spinTensorTerminal eig U c I degree amplitude) := by
  unfold spinTensorTerminal logPartition spinTensorEnergy
  fun_prop

lemma measurable_spinTensorTerminal_joint {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) :
    Measurable (fun p : SpecialOrthogonal N × (SpinTensorIndex I degree → ℝ) =>
      spinTensorTerminal eig (specialRotation p.1) c I degree amplitude p.2) := by
  have hE (σ : Spin N) : Measurable
      (fun p : SpecialOrthogonal N × (SpinTensorIndex I degree → ℝ) =>
        rotatedEnergy eig (specialRotation p.1) σ + fieldEnergy c σ +
          spinTensorEnergy (specialRotation p.1) I degree amplitude p.2 σ) := by
    apply Measurable.add
    · exact ((Finset.measurable_sum _ fun i _ =>
        (((measurable_specialRotation_eval (spinVector σ) i).comp measurable_fst).pow_const 2).const_mul
          (eig i)).const_mul (1 / 2 : ℝ)).add_const _
    · exact Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp measurable_snd).mul
          ((measurable_spinTensorFeature I degree amplitude σ i).comp measurable_fst)
  unfold spinTensorTerminal logPartition
  exact ((Finset.measurable_sum _ fun σ _ => (hE σ).exp).const_mul
    (Fintype.card (Spin N) : ℝ)⁻¹).log

lemma spinTensorTerminal_linearGrowth {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) :
    IsingPerceptron.HasLinearGrowth (spinTensorTerminal eig U c I degree amplitude) := by
  classical
  let L : ℝ := ∑ σ : Spin N, ∑ i : SpinTensorIndex I degree,
    |spinTensorFeature U I degree amplitude σ i|
  have hL : 0 ≤ L := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hb (z : SpinTensorIndex I degree → ℝ) (σ : Spin N) :
      |spinTensorEnergy U I degree amplitude z σ| ≤ L * ‖z‖ := by
    have hσ : (∑ i : SpinTensorIndex I degree, |spinTensorFeature U I degree amplitude σ i|) ≤ L := by
      apply Finset.single_le_sum (f := fun τ : Spin N =>
        ∑ i : SpinTensorIndex I degree, |spinTensorFeature U I degree amplitude τ i|)
      · exact fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
      · exact Finset.mem_univ σ
    calc
      _ ≤ ∑ i, |z i * spinTensorFeature U I degree amplitude σ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ‖z‖ * |spinTensorFeature U I degree amplitude σ i| :=
        Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i)
            (abs_nonneg _)
      _ = ‖z‖ * ∑ i, |spinTensorFeature U I degree amplitude σ i| := (Finset.mul_sum _ _ _).symm
      _ ≤ ‖z‖ * L := mul_le_mul_of_nonneg_left hσ (norm_nonneg _)
      _ = _ := mul_comm _ _
  refine ⟨|spinTensorTerminal eig U c I degree amplitude 0|, L, abs_nonneg _, hL, fun z => ?_⟩
  have hcomp : |spinTensorTerminal eig U c I degree amplitude z -
      spinTensorTerminal eig U c I degree amplitude 0| ≤ L * ‖z‖ := by
    apply abs_logPartition_sub_le
    intro σ
    simpa [spinTensorEnergy] using hb z σ
  have ht := abs_add_le
    (spinTensorTerminal eig U c I degree amplitude z - spinTensorTerminal eig U c I degree amplitude 0)
    (spinTensorTerminal eig U c I degree amplitude 0)
  rw [sub_add_cancel] at ht
  linarith

def tensorGaussianLaw {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (v : SpinTensorIndex I degree → ℝ≥0) :
    ProbabilityMeasure (SpinTensorIndex I degree → ℝ) :=
  ⟨Measure.pi (fun i => gaussianReal 0 (v i)), inferInstance⟩

lemma tensorGaussianLaw_moments {N m k : ℕ} (hN : 0 < N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (v : SpinTensorIndex I degree → ℝ≥0) :
    IsingPerceptron.ExponentialNormMoments
      (tensorGaussianLaw I degree v : Measure (SpinTensorIndex I degree → ℝ)) := by
  let : Nonempty (SpinTensorIndex I degree) := ⟨Sum.inl ⟨0, hN⟩⟩
  have hm := IsingPerceptron.finite_gaussian_exponentialNormMoments
    (P := Measure.pi (fun i : SpinTensorIndex I degree => gaussianReal 0 (v i)))
    (X := fun z : SpinTensorIndex I degree → ℝ => z) measurable_id (fun _ => 0) v
    (fun i => (measurePreserving_eval (fun j : SpinTensorIndex I degree => gaussianReal 0 (v j)) i).map_eq)
  change IsingPerceptron.ExponentialNormMoments
    ((Measure.pi (fun i : SpinTensorIndex I degree => gaussianReal 0 (v i))).map id) at hm
  rw [Measure.map_id] at hm
  exact hm

def tensorCascadeLaw {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    Measure (IsingPerceptron.NoiseTree (SpinTensorIndex I degree → ℝ) n) :=
  IsingPerceptron.noiseCascadeLaw (SpinTensorIndex I degree → ℝ) n b
    (fun i => tensorGaussianLaw I degree (v i))

def tensorCascadeLog {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ)
    (T : IsingPerceptron.NoiseTree (SpinTensorIndex I degree → ℝ) n) : ℝ :=
  Real.log (∫ leaf, Real.exp (IsingPerceptron.noiseLeafTerminal n
    (fun _ => spinTensorTerminal eig U c I degree amplitude) (fun _ p => p.1 + p.2) z leaf)
    ∂IsingPerceptron.noiseLeafKernel (SpinTensorIndex I degree → ℝ) n T)

def tensorCascadeValue {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (z : SpinTensorIndex I degree → ℝ) : ℝ :=
  IsingPerceptron.cascadeRecursion n b (fun i => tensorGaussianLaw I degree (v i))
    (fun _ p => p.1 + p.2) (spinTensorTerminal eig U c I degree amplitude) z

/-- The actual sum of the root and all Gaussian marks on a sampled leaf. -/
def tensorLeafState {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) : (n : ℕ) → (SpinTensorIndex I degree → ℝ) →
    IsingPerceptron.NoiseLeaf (SpinTensorIndex I degree → ℝ) n → (SpinTensorIndex I degree → ℝ)
  | 0, z, _ => z
  | n + 1, z, leaf => tensorLeafState I degree n (z + leaf.2.1) leaf.2.2

lemma noiseLeafTerminal_spinTensorTerminal {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ)
    (leaf : IsingPerceptron.NoiseLeaf (SpinTensorIndex I degree → ℝ) n) :
    IsingPerceptron.noiseLeafTerminal n (fun _ => spinTensorTerminal eig U c I degree amplitude)
      (fun _ p => p.1 + p.2) z leaf =
      spinTensorTerminal eig U c I degree amplitude (tensorLeafState I degree n z leaf) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => exact ih (z + leaf.2.1) leaf.2.2

/-- The cascade logarithm is the actual spin/leaf joint partition, with
uniform Ising prior and the sampled cascade leaf law. -/
theorem tensorCascadeLog_eq_jointPartition {N m k : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (z : SpinTensorIndex I degree → ℝ)
    (T : IsingPerceptron.NoiseTree (SpinTensorIndex I degree → ℝ) n) :
    tensorCascadeLog eig U c I degree amplitude n z T =
      Real.log (∫ leaf, (Fintype.card (Spin N) : ℝ)⁻¹ * ∑ σ : Spin N,
        Real.exp (rotatedEnergy eig U σ + fieldEnergy c σ +
          spinTensorEnergy U I degree amplitude (tensorLeafState I degree n z leaf) σ)
        ∂IsingPerceptron.noiseLeafKernel (SpinTensorIndex I degree → ℝ) n T) := by
  unfold tensorCascadeLog
  congr 1
  apply integral_congr_ae
  refine ae_of_all _ fun leaf => ?_
  dsimp only
  rw [noiseLeafTerminal_spinTensorTerminal]
  unfold spinTensorTerminal logPartition
  apply Real.exp_log
  exact mul_pos (inv_pos.mpr (by exact_mod_cast Fintype.card_pos (α := Spin N))) (sum_exp_pos _)

/-- Exact leaf-law recursion and conditional centered fluctuation for the
finite spectral tensor perturbations. The Haar rotation is retained in every
coefficient; the statement holds separately for every rotation. -/
theorem tensorCascadeLog_recursion {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) :
    let P := tensorCascadeLaw I degree n b v
    let F := tensorCascadeLog eig U c I degree amplitude n z
    let V := tensorCascadeValue eig U c I degree amplitude n b v z
    Integrable F P ∧ (∫ T, F T ∂P) = V ∧
      Integrable (fun T => (F T - V) ^ 2) P ∧
      (∫ T, (F T - V) ^ 2 ∂P) ≤
        4 * ∫ T, (Real.log (IsingPerceptron.rawTreeTotal n T).toReal) ^ 2
          ∂(IsingPerceptron.rawCascadeLaw n b : Measure (IsingPerceptron.RawTree n)) := by
  have h := IsingPerceptron.linearGrowth_noiseCascade_recursion n b hb
    (fun i => tensorGaussianLaw I degree (v i)) (fun i _ => tensorGaussianLaw_moments hN I degree (v i))
    (measurable_spinTensorTerminal eig U c I degree amplitude)
    (spinTensorTerminal_linearGrowth eig U c I degree amplitude) z
  let L := fun T => Real.log
    ((IsingPerceptron.terminalTreeFactor n b (fun i => tensorGaussianLaw I degree (v i))
      (fun _ p => p.1 + p.2) (spinTensorTerminal eig U c I degree amplitude) z T).toReal /
      (IsingPerceptron.noiseTreeTotal (SpinTensorIndex I degree → ℝ) n T).toReal)
  have he : tensorCascadeLog eig U c I degree amplitude n z =ᵐ[tensorCascadeLaw I degree n b v] L :=
    IsingPerceptron.noise_leaf_log_eq_ratio n b hb (fun i => tensorGaussianLaw I degree (v i))
      (fun _ => measurable_fst.add measurable_snd) (measurable_spinTensorTerminal eig U c I degree amplitude) z
  have heq : (fun T => (tensorCascadeLog eig U c I degree amplitude n z T -
      tensorCascadeValue eig U c I degree amplitude n b v z) ^ 2)
      =ᵐ[tensorCascadeLaw I degree n b v]
      (fun T => (L T - tensorCascadeValue eig U c I degree amplitude n b v z) ^ 2) := by
    filter_upwards [he] with T hT
    exact congrArg (fun x => (x - tensorCascadeValue eig U c I degree amplitude n b v z) ^ 2) hT
  exact ⟨h.2.1.congr (Filter.EventuallyEq.symm he), (integral_congr_ae he).trans h.2.2.1,
    h.2.2.2.1.congr (Filter.EventuallyEq.symm heq), (integral_congr_ae heq).trans_le h.2.2.2.2⟩

lemma measurable_tensorCascadeValue_joint {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (fun p : SpecialOrthogonal N × (SpinTensorIndex I degree → ℝ) =>
      tensorCascadeValue eig (specialRotation p.1) c I degree amplitude n b v p.2) := by
  induction n generalizing b v with
  | zero => exact measurable_spinTensorTerminal_joint eig c I degree amplitude
  | succ n ih =>
    have hp : Measurable
        (fun p : (SpecialOrthogonal N × (SpinTensorIndex I degree → ℝ)) × (SpinTensorIndex I degree → ℝ) =>
          (p.1.1, p.1.2 + p.2)) :=
      measurable_fst.fst.prodMk (measurable_fst.snd.add measurable_snd)
    have hm := (((ih (fun i => b (i + 1)) (fun i => v (i + 1))).comp hp).const_mul (b 0)).exp
    exact hm.stronglyMeasurable.integral_prod_right.measurable.log.div_const (b 0)

lemma integrable_tensorCascadeValue_root {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (root : SpinTensorIndex I degree → ℝ≥0) :
    Integrable (tensorCascadeValue eig U c I degree amplitude n b v)
      (tensorGaussianLaw I degree root : Measure (SpinTensorIndex I degree → ℝ)) := by
  have hm := IsingPerceptron.measurable_cascadeRecursion n b
    (fun i => tensorGaussianLaw I degree (v i))
    (fun _ => measurable_fst.add measurable_snd) (measurable_spinTensorTerminal eig U c I degree amplitude)
  change Measurable (tensorCascadeValue eig U c I degree amplitude n b v) at hm
  have hg := IsingPerceptron.cascadeRecursion_linearGrowth n b
    (fun i => tensorGaussianLaw I degree (v i)) (fun i _ => tensorGaussianLaw_moments hN I degree (v i))
    (measurable_spinTensorTerminal eig U c I degree amplitude)
    (spinTensorTerminal_linearGrowth eig U c I degree amplitude) (fun i hi => (hb.1 i hi).1)
  obtain ⟨C, L, _, hL, hbound⟩ := hg
  have hi := (integrable_const C).add ((tensorGaussianLaw_moments hN I degree root 1).const_mul L)
  apply hi.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change |tensorCascadeValue eig U c I degree amplitude n b v z| ≤ C + L * Real.exp (1 * ‖z‖)
    rw [one_mul]
    exact (hbound z).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left
        ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp ‖z‖)) hL))

def tensorEnrichedPressure {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (root : SpinTensorIndex I degree → ℝ≥0) : ℝ :=
  (N : ℝ)⁻¹ * ∫ z, tensorCascadeValue eig U c I degree amplitude n b v z
    ∂(tensorGaussianLaw I degree root : Measure (SpinTensorIndex I degree → ℝ))

theorem tensorEnrichedPressure_eq_cascade_expectation {N m k : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b) (root : SpinTensorIndex I degree → ℝ≥0) :
    tensorEnrichedPressure eig U c I degree amplitude n b v root =
      (N : ℝ)⁻¹ * ∫ z, (∫ T, tensorCascadeLog eig U c I degree amplitude n z T
        ∂tensorCascadeLaw I degree n b v)
        ∂(tensorGaussianLaw I degree root : Measure (SpinTensorIndex I degree → ℝ)) := by
  unfold tensorEnrichedPressure
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun z =>
    (tensorCascadeLog_recursion hN eig U c I degree amplitude n b v hb z).2.1.symm

end InvariantIsing

end

end OAI
