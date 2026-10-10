import OAI.Probability.InvariantIsing.Core.MixedSpectralFeatures
import OAI.Probability.InvariantIsing.Arrays.TripleContractions
import OAI.Probability.InvariantIsing.Arrays.PerturbationWeights

namespace OAI

/-! Finite covariance derivative contractions in the tensor perturbation
error of the spectral Ward identity (manuscript, §3, lines 421--439). -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def projectedOverlapEndpointDerivative {N : ℕ} (U : Orthogonal N) (K : Finset (Fin N))
    (i j : Fin N) (σ τ : Spin N) : ℝ :=
  (N : ℝ)⁻¹ * ((if i ∈ K then spinCoordinate U σ j * spinCoordinate U τ i else 0) -
    (if j ∈ K then spinCoordinate U σ i * spinCoordinate U τ j else 0))

lemma hasDerivAt_mixedProjectedOverlap_plane {N : ℕ} (U : Orthogonal N)
    (K : Finset (Fin N)) (i j : Fin N) (σ τ : Spin N) :
    HasDerivAt (fun s => mixedProjectedOverlap (matrixRotation (planeRotation i j s * U))
      (matrixRotation U) K σ τ) (projectedOverlapEndpointDerivative U K i j σ τ) 0 := by
  have hd := (HasDerivAt.fun_sum (u := K) (fun k _ =>
    (hasDerivAt_planeRotation_coordinate i j k U (spinVector σ) 0).mul_const
      (matrixRotation U (spinVector τ) k))).const_mul (N : ℝ)⁻¹
  convert hd using 1
  · rfl
  · simp only [planeRotation_zero, one_mul, projectedOverlapEndpointDerivative, spinCoordinate,
      sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq']

def spectralMonomialEndpointCoefficient {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ τ : Spin N) (a : Fin m) : ℝ :=
  (∏ b ∈ Finset.univ.erase a, projectedOverlap (matrixRotation U) (I b) σ τ ^ d b) *
    ((d a : ℝ) * projectedOverlap (matrixRotation U) (I a) σ τ ^ (d a - 1))

def spectralMonomialEndpointDerivative {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (i j : Fin N) (σ τ : Spin N) : ℝ :=
  ∑ a, spectralMonomialEndpointCoefficient U I d σ τ a * projectedOverlapEndpointDerivative U (I a) i j σ τ

/-- This is the derivative in one tensor endpoint. The other endpoint and
all tree coordinates remain fixed during the plane rotation. -/
theorem hasDerivAt_spectralMonomial_mixed_plane {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (i j : Fin N) (σ τ : Spin N) :
    HasDerivAt (fun s => ∏ a,
      mixedProjectedOverlap (matrixRotation (planeRotation i j s * U)) (matrixRotation U) (I a) σ τ ^ d a)
      (spectralMonomialEndpointDerivative U I d i j σ τ) 0 := by
  have hd := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun a _ =>
    (hasDerivAt_mixedProjectedOverlap_plane U (I a) i j σ τ).pow (d a))
  have hs (a : Fin m) : mixedProjectedOverlap (matrixRotation (planeRotation i j 0 * U))
      (matrixRotation U) (I a) σ τ = projectedOverlap (matrixRotation U) (I a) σ τ := by
    simp only [planeRotation_zero, one_mul]
    rfl
  simpa only [Pi.pow_apply, hs, smul_eq_mul, spectralMonomialEndpointDerivative,
    spectralMonomialEndpointCoefficient, mul_assoc] using hd

theorem hasDerivAt_spectralTensor_cross_plane {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (i j : Fin N) (σ τ : Spin N) :
    HasDerivAt (fun s => ∑ v : SpectralTensorIndex I d,
      spectralMonomialFeature (matrixRotation (planeRotation i j s * U)) I d σ v *
        spectralMonomialFeature (matrixRotation U) I d τ v)
      (spectralMonomialEndpointDerivative U I d i j σ τ) 0 := by
  have hf : (fun s => ∑ v : SpectralTensorIndex I d,
      spectralMonomialFeature (matrixRotation (planeRotation i j s * U)) I d σ v *
        spectralMonomialFeature (matrixRotation U) I d τ v) =
      (fun s => ∏ a, mixedProjectedOverlap (matrixRotation (planeRotation i j s * U))
        (matrixRotation U) (I a) σ τ ^ d a) :=
    funext fun s => spectralMonomialFeature_mixed_cross _ _ I d σ τ
  rw [hf]
  exact hasDerivAt_spectralMonomial_mixed_plane U I d i j σ τ

lemma jointSpectralMonomialCoefficients_mixed_cross {N m : ℕ} (U V : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ)
    (x y : Spin N × LabeledLeaf n) :
    cylinderCross (jointSpectralMonomialCoefficients U I d n r x)
      (jointSpectralMonomialCoefficients V I d n r y) =
      (∏ a, mixedProjectedOverlap U V (I a) x.1 y.1 ^ d a) * treeOverlap n x.2 y.2 ^ r := by
  unfold jointSpectralMonomialCoefficients
  rw [treeField_path_cross n x.2 y.2 (monomialPath_monotone n r) (monomialPath_nonneg n r 0),
    spectralMonomialFeature_mixed_cross]
  simp only [monomialPath, treeOverlap]
  ring

theorem hasDerivAt_jointSpectralCoefficients_cross_plane {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ)
    (i j : Fin N) (x y : Spin N × LabeledLeaf n) :
    HasDerivAt (fun s => cylinderCross
      (jointSpectralMonomialCoefficients (matrixRotation (planeRotation i j s * U)) I d n r x)
      (jointSpectralMonomialCoefficients (matrixRotation U) I d n r y))
      (spectralMonomialEndpointDerivative U I d i j x.1 y.1 * treeOverlap n x.2 y.2 ^ r) 0 := by
  have hf : (fun s => cylinderCross
      (jointSpectralMonomialCoefficients (matrixRotation (planeRotation i j s * U)) I d n r x)
      (jointSpectralMonomialCoefficients (matrixRotation U) I d n r y)) =
      (fun s => (∏ a, mixedProjectedOverlap (matrixRotation (planeRotation i j s * U))
        (matrixRotation U) (I a) x.1 y.1 ^ d a) * treeOverlap n x.2 y.2 ^ r) :=
    funext fun s => jointSpectralMonomialCoefficients_mixed_cross _ _ I d n r x y
  rw [hf]
  exact (hasDerivAt_spectralMonomial_mixed_plane U I d i j x.1 y.1).mul_const _

lemma spectralMonomialEndpointCoefficient_abs_le {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ τ : Spin N) (a : Fin m) :
    |spectralMonomialEndpointCoefficient U I d σ τ a| ≤ d a := by
  have hpow (b : Fin m) (r : ℕ) : |projectedOverlap (matrixRotation U) (I b) σ τ ^ r| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (projectedOverlap_abs_le_one _ _ _ _)
  have hp : |∏ b ∈ Finset.univ.erase a, projectedOverlap (matrixRotation U) (I b) σ τ ^ d b| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun b _ => hpow b (d b))
  unfold spectralMonomialEndpointCoefficient
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (d a) : (0 : ℝ) ≤ (d a : ℝ))]
  calc
    _ ≤ 1 * ((d a : ℝ) * 1) :=
      mul_le_mul hp (mul_le_mul_of_nonneg_left (hpow a (d a - 1)) (Nat.cast_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) zero_le_one
    _ = _ := by ring

def projectedEndpointContraction {N : ℕ} (U : Orthogonal N)
    (I J K : Finset (Fin N)) (η θ σ τ : Spin N) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ I, ∑ j ∈ J,
    spinCoordinate U η i * spinCoordinate U θ j * projectedOverlapEndpointDerivative U K i j σ τ

/-- The two coordinate sums contract into products of normalized projected
inner products, with one remaining factor `1/N`. -/
theorem projectedEndpointContraction_eq {N : ℕ} (U : Orthogonal N)
    (I J K : Finset (Fin N)) (η θ σ τ : Spin N) :
    projectedEndpointContraction U I J K η θ σ τ =
      (N : ℝ)⁻¹ * (projectedOverlap (matrixRotation U) (I ∩ K) η τ *
        projectedOverlap (matrixRotation U) J θ σ -
        projectedOverlap (matrixRotation U) I η σ * projectedOverlap (matrixRotation U) (J ∩ K) θ τ) := by
  classical
  have hi : (∑ i ∈ I, if i ∈ K then spinCoordinate U η i * spinCoordinate U τ i else 0) =
      ∑ i ∈ I ∩ K, spinCoordinate U η i * spinCoordinate U τ i := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
  have hj : (∑ j ∈ J, if j ∈ K then spinCoordinate U θ j * spinCoordinate U τ j else 0) =
      ∑ j ∈ J ∩ K, spinCoordinate U θ j * spinCoordinate U τ j := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
  have hterm (i j : Fin N) : spinCoordinate U η i * spinCoordinate U θ j *
      projectedOverlapEndpointDerivative U K i j σ τ = (N : ℝ)⁻¹ *
      ((if i ∈ K then spinCoordinate U η i * spinCoordinate U τ i else 0) *
          (spinCoordinate U θ j * spinCoordinate U σ j) -
        (spinCoordinate U η i * spinCoordinate U σ i) *
          (if j ∈ K then spinCoordinate U θ j * spinCoordinate U τ j else 0)) := by
    unfold projectedOverlapEndpointDerivative
    split_ifs <;> ring
  simp_rw [projectedEndpointContraction, hterm]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hi, hj]
  simp only [projectedOverlap, spinCoordinate]
  ring

theorem projectedEndpointContraction_abs_le {N : ℕ} (U : Orthogonal N)
    (I J K : Finset (Fin N)) (η θ σ τ : Spin N) :
    |projectedEndpointContraction U I J K η θ σ τ| ≤ 2 * (N : ℝ)⁻¹ := by
  rw [projectedEndpointContraction_eq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)]
  have hab (K L : Finset (Fin N)) (s t u w : Spin N) :
      |projectedOverlap (matrixRotation U) K s t * projectedOverlap (matrixRotation U) L u w| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (projectedOverlap_abs_le_one _ _ _ _) (projectedOverlap_abs_le_one _ _ _ _)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hd : |projectedOverlap (matrixRotation U) (I ∩ K) η τ * projectedOverlap (matrixRotation U) J θ σ -
      projectedOverlap (matrixRotation U) I η σ * projectedOverlap (matrixRotation U) (J ∩ K) θ τ| ≤ 2 := by
    have h1 := hab (I ∩ K) J η τ θ σ
    have h2 := hab I (J ∩ K) η σ θ τ
    exact (abs_sub _ _).trans (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)]

def spectralMonomialEndpointContraction {N m : ℕ} (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (I J : Finset (Fin N)) (η θ σ τ : Spin N) : ℝ :=
  ∑ a, spectralMonomialEndpointCoefficient U groups d σ τ a *
    projectedEndpointContraction U I J (groups a) η θ σ τ

theorem spectralMonomialEndpointContraction_eq {N m : ℕ} (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (I J : Finset (Fin N)) (η θ σ τ : Spin N) :
    spectralMonomialEndpointContraction U groups d I J η θ σ τ =
      (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ I, ∑ j ∈ J, spinCoordinate U η i * spinCoordinate U θ j *
        spectralMonomialEndpointDerivative U groups d i j σ τ := by
  unfold spectralMonomialEndpointContraction projectedEndpointContraction spectralMonomialEndpointDerivative
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem spectralMonomialEndpointContraction_abs_le {N m : ℕ} (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (I J : Finset (Fin N)) (η θ σ τ : Spin N) :
    |spectralMonomialEndpointContraction U groups d I J η θ σ τ| ≤
      2 * (N : ℝ)⁻¹ * ∑ a, (d a : ℝ) := by
  unfold spectralMonomialEndpointContraction
  calc
    _ ≤ ∑ a, |spectralMonomialEndpointCoefficient U groups d σ τ a *
        projectedEndpointContraction U I J (groups a) η θ σ τ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, (d a : ℝ) * (2 * (N : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul (spectralMonomialEndpointCoefficient_abs_le U groups d σ τ a)
        (projectedEndpointContraction_abs_le U I J (groups a) η θ σ τ) (abs_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

def tensorWardPerturbationError {N m : ℕ} (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (treeDegree : Fin N → ℕ) (n : ℕ) (u : Fin N → ℝ)
    (I J : Finset (Fin N)) (η θ : Spin N) (x y : Spin N × LabeledLeaf n) : ℝ :=
  ∑ r, tensorPerturbationAmplitude N u r ^ 2 * treeOverlap n x.2 y.2 ^ treeDegree r *
    spectralMonomialEndpointContraction U groups (degree r) I J η θ x.1 y.1

theorem tensorWardPerturbationError_eq {N m : ℕ} (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (treeDegree : Fin N → ℕ) (n : ℕ) (u : Fin N → ℝ)
    (I J : Finset (Fin N)) (η θ : Spin N) (x y : Spin N × LabeledLeaf n) :
    tensorWardPerturbationError U groups degree treeDegree n u I J η θ x y =
      (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ I, ∑ j ∈ J, spinCoordinate U η i * spinCoordinate U θ j *
        ∑ r, tensorPerturbationAmplitude N u r ^ 2 * treeOverlap n x.2 y.2 ^ treeDegree r *
          spectralMonomialEndpointDerivative U groups (degree r) i j x.1 y.1 := by
  unfold tensorWardPerturbationError
  simp_rw [spectralMonomialEndpointContraction_eq]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem hasDerivAt_tensorPerturbation_cross_plane {N m : ℕ} (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (treeDegree : Fin N → ℕ) (n : ℕ) (u : Fin N → ℝ)
    (i j : Fin N) (x y : Spin N × LabeledLeaf n) :
    HasDerivAt (fun s => ∑ r, tensorPerturbationAmplitude N u r ^ 2 *
      treeOverlap n x.2 y.2 ^ treeDegree r *
        ∑ v : SpectralTensorIndex groups (degree r),
          spectralMonomialFeature (matrixRotation (planeRotation i j s * U)) groups (degree r) x.1 v *
            spectralMonomialFeature (matrixRotation U) groups (degree r) y.1 v)
      (∑ r, tensorPerturbationAmplitude N u r ^ 2 * treeOverlap n x.2 y.2 ^ treeDegree r *
        spectralMonomialEndpointDerivative U groups (degree r) i j x.1 y.1) 0 :=
  HasDerivAt.fun_sum (u := Finset.univ) fun r _ =>
    (hasDerivAt_spectralTensor_cross_plane U groups (degree r) i j x.1 y.1).const_mul _

theorem hasDerivAt_jointTensorPerturbation_cross_plane {N m : ℕ} (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (treeDegree : Fin N → ℕ) (n : ℕ) (u : Fin N → ℝ)
    (i j : Fin N) (x y : Spin N × LabeledLeaf n) :
    HasDerivAt (fun s => ∑ r, tensorPerturbationAmplitude N u r ^ 2 * cylinderCross
      (jointSpectralMonomialCoefficients (matrixRotation (planeRotation i j s * U)) groups (degree r) n (treeDegree r) x)
      (jointSpectralMonomialCoefficients (matrixRotation U) groups (degree r) n (treeDegree r) y))
      (∑ r, tensorPerturbationAmplitude N u r ^ 2 * treeOverlap n x.2 y.2 ^ treeDegree r *
        spectralMonomialEndpointDerivative U groups (degree r) i j x.1 y.1) 0 := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun r _ =>
    (hasDerivAt_jointSpectralCoefficients_cross_plane U groups (degree r) n (treeDegree r) i j x y).const_mul
      (tensorPerturbationAmplitude N u r ^ 2)
  convert hd using 1
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- One covariance contraction after Gaussian integration by parts, for
the actual finite geometric-weight perturbation. It is uniform in tree
depth, all four spin replicas, and the coordinate groups. -/
theorem tensorWardPerturbationError_abs_le {N m : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (treeDegree : Fin N → ℕ) (n : ℕ) (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2)
    (D : ℝ) (hD : 0 ≤ D) (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (I J : Finset (Fin N)) (η θ : Spin N) (x y : Spin N × LabeledLeaf n) :
    |tensorWardPerturbationError U groups degree treeDegree n u I J η θ x y| ≤
      8 * D * perturbationScale N ^ 2 := by
  have ht (r : Fin N) : |treeOverlap n x.2 y.2 ^ treeDegree r| ≤ 1 := by
    rw [abs_pow, abs_of_nonneg (treeOverlap_mem n x.2 y.2).1]
    exact pow_le_one₀ (treeOverlap_mem n x.2 y.2).1 (treeOverlap_mem n x.2 y.2).2
  unfold tensorWardPerturbationError
  calc
    _ ≤ ∑ r, |tensorPerturbationAmplitude N u r ^ 2 * treeOverlap n x.2 y.2 ^ treeDegree r *
        spectralMonomialEndpointContraction U groups (degree r) I J η θ x.1 y.1| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, tensorPerturbationAmplitude N u r ^ 2 *
        (2 * (N : ℝ)⁻¹ * ∑ a, (degree r a : ℝ)) := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
      have hcoef : tensorPerturbationAmplitude N u r ^ 2 * |treeOverlap n x.2 y.2 ^ treeDegree r| ≤
          tensorPerturbationAmplitude N u r ^ 2 :=
        mul_le_of_le_one_right (sq_nonneg _) (ht r)
      exact mul_le_mul hcoef
        (spectralMonomialEndpointContraction_abs_le U groups (degree r) I J η θ x.1 y.1)
        (abs_nonneg _) (sq_nonneg _)
    _ = 2 * (N : ℝ)⁻¹ * ∑ r, tensorPerturbationAmplitude N u r ^ 2 * ∑ a, (degree r a : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ ≤ 2 * (N : ℝ)⁻¹ * (4 * N * perturbationScale N ^ 2 * D) :=
      mul_le_mul_of_nonneg_left (tensorPerturbationAmplitude_degree_sum_le u hu degree D hD hdegree) (by positivity)
    _ = _ := by
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
      ring

theorem tensorWardPerturbationError_test_abs_le {N m : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (treeDegree : Fin N → ℕ) (n : ℕ) (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2)
    (D : ℝ) (hD : 0 ≤ D) (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (I J : Finset (Fin N)) (η θ : Spin N) (x y : Spin N × LabeledLeaf n)
    (F B : ℝ) (hB : 0 ≤ B) (hF : |F| ≤ B) :
    |F * tensorWardPerturbationError U groups degree treeDegree n u I J η θ x y| ≤
      8 * B * D * perturbationScale N ^ 2 := by
  rw [abs_mul]
  exact (mul_le_mul hF
    (tensorWardPerturbationError_abs_le hN U groups degree treeDegree n u hu D hD hdegree I J η θ x y)
    (abs_nonneg _) hB).trans_eq (by ring)

end InvariantIsing

end

end OAI
