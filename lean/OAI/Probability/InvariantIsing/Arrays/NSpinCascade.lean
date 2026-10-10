import OAI.Probability.InvariantIsing.Fields.CascadeMarking
import OAI.Probability.InvariantIsing.Haar.Rotation
import OAI.Probability.IsingPerceptron.EnrichedFieldCap

namespace OAI

/-!
Gaussian cascade marking for the actual finite Ising partition function at
a fixed orthogonal rotation. The Haar variable is fixed in this result.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

def rotatedFieldTerminal {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c z : Fin N → ℝ) : ℝ :=
  logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy (c + z) σ)

lemma measurable_rotatedFieldTerminal {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) : Measurable (rotatedFieldTerminal eig U c) := by
  unfold rotatedFieldTerminal logPartition fieldEnergy
  fun_prop

lemma abs_rotatedFieldTerminal_sub_le {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c z w : Fin N → ℝ) :
    |rotatedFieldTerminal eig U c z - rotatedFieldTerminal eig U c w| ≤
      (N : ℝ) * ‖z - w‖ := by
  have he (σ : Spin N) :
      |(rotatedEnergy eig U σ + fieldEnergy (c + z) σ) -
        (rotatedEnergy eig U σ + fieldEnergy (c + w) σ)| ≤ (N : ℝ) * ‖z - w‖ := by
    rw [add_sub_add_left_eq_sub]
    calc
      _ ≤ ∑ i, |(c + z) i - (c + w) i| := abs_fieldEnergy_sub_le _ _ σ
      _ = ∑ i, |z i - w i| := by simp only [Pi.add_apply, add_sub_add_left_eq_sub]
      _ ≤ ∑ _ : Fin N, ‖z - w‖ := Finset.sum_le_sum fun i _ => by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (z - w) i
      _ = (N : ℝ) * ‖z - w‖ := by simp
  exact abs_logPartition_sub_le _ _ _ he

lemma rotatedFieldTerminal_linearGrowth {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) : IsingPerceptron.HasLinearGrowth (rotatedFieldTerminal eig U c) := by
  refine ⟨|rotatedFieldTerminal eig U c 0|, N, abs_nonneg _, Nat.cast_nonneg _, fun z => ?_⟩
  have hl := abs_rotatedFieldTerminal_sub_le eig U c z 0
  rw [sub_zero] at hl
  have ht := abs_add_le (rotatedFieldTerminal eig U c z - rotatedFieldTerminal eig U c 0)
    (rotatedFieldTerminal eig U c 0)
  rw [sub_add_cancel] at ht
  linarith

def vectorGaussianLaw (N : ℕ) (v : ℝ≥0) : ProbabilityMeasure (Fin N → ℝ) :=
  ⟨Measure.pi (fun _ : Fin N => gaussianReal 0 v), inferInstance⟩

lemma vectorGaussianLaw_moments {N : ℕ} (hN : 0 < N) (v : ℝ≥0) :
    IsingPerceptron.ExponentialNormMoments (vectorGaussianLaw N v : Measure (Fin N → ℝ)) := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hm := IsingPerceptron.finite_gaussian_exponentialNormMoments
    (P := Measure.pi (fun _ : Fin N => gaussianReal 0 v))
    (X := fun z : Fin N → ℝ => z) measurable_id (fun _ => 0) (fun _ => v)
    (fun i => (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 v) i).map_eq)
  change IsingPerceptron.ExponentialNormMoments
    ((Measure.pi (fun _ : Fin N => gaussianReal 0 v)).map id) at hm
  rw [Measure.map_id] at hm
  exact hm

def rotatedCascadeLaw (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) :
    Measure (IsingPerceptron.NoiseTree (Fin N → ℝ) n) :=
  IsingPerceptron.noiseCascadeLaw (Fin N → ℝ) n b (fun i => vectorGaussianLaw N (v i))

def rotatedCascadeLog {N : ℕ} (n : ℕ) (eig : Fin N → ℝ) (U : Rotation N)
    (c z : Fin N → ℝ) (T : IsingPerceptron.NoiseTree (Fin N → ℝ) n) : ℝ :=
  Real.log (∫ leaf, Real.exp (IsingPerceptron.noiseLeafTerminal n
    (fun _ => rotatedFieldTerminal eig U c) (fun _ p => p.1 + p.2) z leaf)
    ∂IsingPerceptron.noiseLeafKernel (Fin N → ℝ) n T)

def rotatedCascadeValue {N : ℕ} (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (eig : Fin N → ℝ) (U : Rotation N) (c z : Fin N → ℝ) : ℝ :=
  IsingPerceptron.cascadeRecursion n b (fun i => vectorGaussianLaw N (v i))
    (fun _ p => p.1 + p.2) (rotatedFieldTerminal eig U c) z

/-- The published Gaussian marking recursion specialized to the actual
finite rotated Ising terminal, with the Haar rotation held fixed. -/
theorem rotatedCascadeLog_recursion {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → ℝ≥0) (hb : IsingPerceptron.CascadeExponents n b)
    (eig : Fin N → ℝ) (U : Rotation N) (c z : Fin N → ℝ) :
    Integrable (rotatedCascadeLog n eig U c z) (rotatedCascadeLaw N n b v) ∧
      (∫ T, rotatedCascadeLog n eig U c z T ∂rotatedCascadeLaw N n b v) =
        rotatedCascadeValue n b v eig U c z := by
  have h := IsingPerceptron.linearGrowth_noiseCascade_recursion n b hb
    (fun i => vectorGaussianLaw N (v i)) (fun i _ => vectorGaussianLaw_moments hN (v i))
    (measurable_rotatedFieldTerminal eig U c) (rotatedFieldTerminal_linearGrowth eig U c) z
  have he := IsingPerceptron.noise_leaf_log_eq_ratio n b hb
    (fun i => vectorGaussianLaw N (v i))
    (fun _ => measurable_fst.add measurable_snd) (measurable_rotatedFieldTerminal eig U c) z
  refine ⟨h.2.1.congr (Filter.EventuallyEq.symm he), ?_⟩
  exact (integral_congr_ae he).trans h.2.2.1

lemma integrable_rotatedCascadeValue {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (v : ℕ → ℝ≥0) (hb : IsingPerceptron.CascadeExponents n b)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ) (root : ℝ≥0) :
    Integrable (rotatedCascadeValue n b v eig U c)
      (vectorGaussianLaw N root : Measure (Fin N → ℝ)) := by
  have hm := IsingPerceptron.measurable_cascadeRecursion n b
    (fun i => vectorGaussianLaw N (v i))
    (fun _ => measurable_fst.add measurable_snd) (measurable_rotatedFieldTerminal eig U c)
  change Measurable (rotatedCascadeValue n b v eig U c) at hm
  have hg := IsingPerceptron.cascadeRecursion_linearGrowth n b
    (fun i => vectorGaussianLaw N (v i)) (fun i _ => vectorGaussianLaw_moments hN (v i))
    (measurable_rotatedFieldTerminal eig U c) (rotatedFieldTerminal_linearGrowth eig U c)
    (fun i hi => (hb.1 i hi).1)
  obtain ⟨C, L, _, hL, hbound⟩ := hg
  have hi := (integrable_const C).add ((vectorGaussianLaw_moments hN root 1).const_mul L)
  apply hi.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change |rotatedCascadeValue n b v eig U c z| ≤ C + L * Real.exp (1 * ‖z‖)
    rw [one_mul]
    exact (hbound z).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left
        ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp ‖z‖)) hL))

def rotatedEnrichedPressure {N : ℕ} (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (root : ℝ≥0) (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∫ z, rotatedCascadeValue n b v eig U c z
    ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ))

/-- The fixed-rotation enriched pressure is the actual iterated Gaussian
root and cascade expectation of the finite Ising log partition. -/
theorem rotatedEnrichedPressure_eq_cascade_expectation {N : ℕ} (hN : 0 < N)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (root : ℝ≥0)
    (hb : IsingPerceptron.CascadeExponents n b)
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ) :
    rotatedEnrichedPressure n b v root eig U c =
      (N : ℝ)⁻¹ * ∫ z, (∫ T, rotatedCascadeLog n eig U c z T
        ∂rotatedCascadeLaw N n b v) ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ)) := by
  unfold rotatedEnrichedPressure
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun z => (rotatedCascadeLog_recursion hN n b v hb eig U c z).2.symm

end InvariantIsing

end

end OAI
