import OAI.Probability.InvariantIsing.Arrays.OverlapBounds
import OAI.Probability.InvariantIsing.Pressure.Concentration
import OAI.Probability.IsingPerceptron.ReplicaEnergyCovarianceBound

namespace OAI

/-! Actual finite tensor features for spectral-overlap GG perturbations. -/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

def spectralSpinFeature {N : ℕ} (U : Rotation N) (I : Finset (Fin N))
    (σ : Spin N) (i : I) : ℝ := U (spinVector σ) i / Real.sqrt (N : ℝ)

lemma spectralSpinFeature_cross {N : ℕ} (U : Rotation N) (I : Finset (Fin N)) (σ τ : Spin N) :
    (∑ i : I, spectralSpinFeature U I σ i * spectralSpinFeature U I τ i) =
      projectedOverlap U I σ τ := by
  simp only [spectralSpinFeature, div_mul_div_comm, ← pow_two,
    Real.sq_sqrt (Nat.cast_nonneg N), ← Finset.sum_div]
  rw [div_eq_mul_inv, mul_comm]
  unfold projectedOverlap
  congr 1
  exact Finset.sum_coe_sort I (fun i => U (spinVector σ) i * U (spinVector τ) i)

abbrev SpectralTensorIndex {N m : ℕ} (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) :=
  (a : Fin m) → Fin (d a) → I a

def spectralMonomialFeature {N m : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (d : Fin m → ℕ) (σ : Spin N) (v : SpectralTensorIndex I d) : ℝ :=
  ∏ a, IsingPerceptron.tensorFeature (d a) (spectralSpinFeature U (I a) σ) (v a)

/-- The Gaussian tensor coefficient covariance is exactly the required
monomial in the individual spectral overlaps. -/
theorem spectralMonomialFeature_cross {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ τ : Spin N) :
    (∑ v : SpectralTensorIndex I d,
      spectralMonomialFeature U I d σ v * spectralMonomialFeature U I d τ v) =
      ∏ a, projectedOverlap U (I a) σ τ ^ d a := by
  simp only [spectralMonomialFeature, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun a (v : Fin (d a) → I a) =>
    IsingPerceptron.tensorFeature (d a) (spectralSpinFeature U (I a) σ) v *
      IsingPerceptron.tensorFeature (d a) (spectralSpinFeature U (I a) τ) v)]
  simp_rw [IsingPerceptron.tensorFeature_cross, spectralSpinFeature_cross]

theorem spectralMonomial_posSemidef {N m r : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ : Fin r → Spin N) :
    Matrix.PosSemidef (fun i j => ∏ a, projectedOverlap U (I a) (σ i) (σ j) ^ d a) := by
  let A : Matrix (Fin r) (SpectralTensorIndex I d) ℝ := fun i v => spectralMonomialFeature U I d (σ i) v
  have hp := Matrix.posSemidef_self_mul_conjTranspose A
  have he : (fun i j : Fin r => ∏ a, projectedOverlap U (I a) (σ i) (σ j) ^ d a) = A * Aᴴ := by
    ext i j
    change _ = ∑ v, spectralMonomialFeature U I d (σ i) v * spectralMonomialFeature U I d (σ j) v
    exact (spectralMonomialFeature_cross U I d (σ i) (σ j)).symm
  rw [he]
  exact hp

theorem spectralMonomial_abs_le_one {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ τ : Spin N) :
    |∏ a, projectedOverlap U (I a) σ τ ^ d a| ≤ 1 := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
  intro a _
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (projectedOverlap_abs_le_one U (I a) σ τ)

lemma measurable_spectralMonomialFeature {N m : ℕ}
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ : Spin N) (v : SpectralTensorIndex I d) :
    Measurable (fun U : SpecialOrthogonal N => spectralMonomialFeature (specialRotation U) I d σ v) := by
  unfold spectralMonomialFeature IsingPerceptron.tensorFeature spectralSpinFeature
  apply Finset.measurable_prod
  intro a _
  apply Finset.measurable_prod
  intro k _
  exact (measurable_specialRotation_eval (spinVector σ) (v a k)).div_const _

lemma abs_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hf' : ∀ i ∈ s, |f i| ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' : ∀ i ∈ s, |g i| ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hp : |∏ i ∈ s, f i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) hf'
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      _ = |(f a - g a) * (∏ i ∈ s, f i) +
          g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := by congr 1; ring
      _ ≤ |f a - g a| * |∏ i ∈ s, f i| +
          |g a| * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| := by
        simpa only [abs_mul] using abs_add_le
          ((f a - g a) * (∏ i ∈ s, f i))
          (g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i))
      _ ≤ |f a - g a| * 1 + 1 * ∑ i ∈ s, |f i - g i| :=
        add_le_add (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
          (mul_le_mul (hg a (Finset.mem_insert_self a s)) (ih hf' hg')
            (abs_nonneg _) (by norm_num))
      _ = _ := by ring

lemma abs_pow_sub_pow_le_degree {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (d : ℕ) :
    |x ^ d - y ^ d| ≤ d * |x - y| := by
  have hp : max |x| |y| ^ (d - 1) ≤ 1 :=
    pow_le_one₀ (le_trans (abs_nonneg _) (le_max_left _ _)) (max_le hx hy)
  calc
    _ ≤ |x - y| * d * max |x| |y| ^ (d - 1) := abs_pow_sub_pow_le x y d
    _ ≤ |x - y| * d * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- The covariance, rather than individual Gaussian coefficients, has a
dimension-independent rotation modulus. -/
theorem abs_spectralMonomial_sub_rotation_le {N m : ℕ} (hN : 0 < N)
    (U V : SpecialOrthogonal N) (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (σ τ : Spin N) :
    |(∏ a, projectedOverlap (specialRotation U) (I a) σ τ ^ d a) -
      ∏ a, projectedOverlap (specialRotation V) (I a) σ τ ^ d a| ≤
      2 * (∑ a, (d a : ℝ)) * frobeniusDistance U V := by
  have hpow (W : SpecialOrthogonal N) (a : Fin m) :
      |projectedOverlap (specialRotation W) (I a) σ τ ^ d a| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (projectedOverlap_abs_le_one _ _ _ _)
  calc
    _ ≤ ∑ a, |projectedOverlap (specialRotation U) (I a) σ τ ^ d a -
        projectedOverlap (specialRotation V) (I a) σ τ ^ d a| :=
      abs_prod_sub_prod_le_sum Finset.univ _ _ (fun a _ => hpow U a) (fun a _ => hpow V a)
    _ ≤ ∑ a, (d a : ℝ) * (2 * frobeniusDistance U V) := by
      apply Finset.sum_le_sum
      intro a _
      exact (abs_pow_sub_pow_le_degree (projectedOverlap_abs_le_one _ _ _ _)
        (projectedOverlap_abs_le_one _ _ _ _) (d a)).trans
        (mul_le_mul_of_nonneg_left (abs_projectedOverlap_sub_rotation_le hN U V (I a) σ τ)
          (Nat.cast_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

def spectralMonomialCoefficients {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ : Spin N) : ℕ →₀ ℝ :=
  IsingPerceptron.featureCoefficients
    (fun v : SpectralTensorIndex I d => (Fintype.equivFin _ v).val)
    (spectralMonomialFeature U I d σ)

theorem spectralMonomialCoefficients_cross {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ τ : Spin N) :
    IsingPerceptron.cylinderCross (spectralMonomialCoefficients U I d σ)
      (spectralMonomialCoefficients U I d τ) =
      ∏ a, projectedOverlap U (I a) σ τ ^ d a := by
  unfold spectralMonomialCoefficients
  rw [IsingPerceptron.featureCoefficients_diagonal _ _
    (fun _ _ h => (Fintype.equivFin _).injective (Fin.ext h))]
  simp only [ite_true]
  exact spectralMonomialFeature_cross U I d σ τ

theorem spectralMonomialCoefficients_variance_le_one {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ : Spin N) :
    (spectralMonomialCoefficients U I d σ).sum (fun _ c => c ^ 2) ≤ 1 := by
  rw [← IsingPerceptron.cylinderCross_self, spectralMonomialCoefficients_cross]
  exact (le_abs_self _).trans (spectralMonomial_abs_le_one U I d σ σ)

/-- Independent tensor marks at the cascade levels realize the additional
tree-overlap power in the paper's joint perturbation kernels. -/
def jointSpectralMonomialCoefficients {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ)
    (x : Spin N × IsingPerceptron.LabeledLeaf n) : ℕ →₀ ℝ :=
  IsingPerceptron.treeFieldCoefficients n x.2
    (fun i => IsingPerceptron.pathAmplitude (IsingPerceptron.monomialPath n r) i)
    (spectralMonomialFeature U I d x.1)

theorem jointSpectralMonomialCoefficients_cross {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ)
    (x y : Spin N × IsingPerceptron.LabeledLeaf n) :
    IsingPerceptron.cylinderCross (jointSpectralMonomialCoefficients U I d n r x)
      (jointSpectralMonomialCoefficients U I d n r y) =
      (∏ a, projectedOverlap U (I a) x.1 y.1 ^ d a) *
        IsingPerceptron.treeOverlap n x.2 y.2 ^ r := by
  unfold jointSpectralMonomialCoefficients
  rw [IsingPerceptron.treeField_path_cross n x.2 y.2
    (IsingPerceptron.monomialPath_monotone n r)
    (IsingPerceptron.monomialPath_nonneg n r 0), spectralMonomialFeature_cross]
  exact mul_comm _ _

theorem jointSpectralMonomialCoefficients_variance_le_one {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ)
    (x : Spin N × IsingPerceptron.LabeledLeaf n) :
    (jointSpectralMonomialCoefficients U I d n r x).sum (fun _ c => c ^ 2) ≤ 1 := by
  rw [← IsingPerceptron.cylinderCross_self, jointSpectralMonomialCoefficients_cross]
  have ht : 0 ≤ IsingPerceptron.treeOverlap n x.2 x.2 ^ r := by
    unfold IsingPerceptron.treeOverlap
    positivity
  have htl : IsingPerceptron.treeOverlap n x.2 x.2 ^ r ≤ 1 := by
    simpa only [IsingPerceptron.treeOverlap, IsingPerceptron.labeledCommonDepth_self,
      IsingPerceptron.monomialPath] using IsingPerceptron.monomialPath_diag_le_one n r
  exact (mul_le_mul ((le_abs_self _).trans (spectralMonomial_abs_le_one U I d x.1 x.1))
    htl ht (by norm_num)).trans_eq (one_mul 1)

end InvariantIsing

end

end OAI
