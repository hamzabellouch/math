import OAI.Probability.InvariantIsing.Arrays.TensorFiniteWard
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFrozen

namespace OAI

/-! Coordinate-plane derivatives of the actual finite spectral tensor
coefficients, with uniform finite-dimensional bounds for Haar differentiation. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- A normalized spectral coordinate has a uniformly bounded plane derivative. -/
def spectralSpinPlaneDerivative {N : ℕ} (U : Orthogonal N) (σ : Spin N)
    (i j a : Fin N) : ℝ :=
  (if a = i then spinCoordinate U σ j / Real.sqrt (N : ℝ) else 0) -
    (if a = j then spinCoordinate U σ i / Real.sqrt (N : ℝ) else 0)

lemma abs_normalized_spinCoordinate_le_one {N : ℕ} (hN : 0 < N)
    (U : Orthogonal N) (σ : Spin N) (a : Fin N) :
    |spinCoordinate U σ a / Real.sqrt (N : ℝ)| ≤ 1 := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs := Real.sq_sqrt hN'.le
  have ha := spinCoordinate_sq_le U σ a
  have hx : |spinCoordinate U σ a| ≤ Real.sqrt (N : ℝ) := by
    nlinarith [abs_nonneg (spinCoordinate U σ a), Real.sqrt_nonneg (N : ℝ),
      sq_abs (spinCoordinate U σ a)]
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_one (Real.sqrt_pos.2 hN')).mpr hx

lemma spectralSpinFeature_abs_le_one {N : ℕ} (hN : 0 < N)
    (U : Orthogonal N) (I : Finset (Fin N)) (σ : Spin N) (a : I) :
    |spectralSpinFeature (matrixRotation U) I σ a| ≤ 1 :=
  abs_normalized_spinCoordinate_le_one hN U σ a

lemma spectralSpinPlaneDerivative_abs_le {N : ℕ} (hN : 0 < N)
    (U : Orthogonal N) (σ : Spin N) (i j a : Fin N) :
    |spectralSpinPlaneDerivative U σ i j a| ≤ 2 := by
  have hi : |if a = i then spinCoordinate U σ j / Real.sqrt (N : ℝ) else 0| ≤ 1 := by
    split_ifs
    · exact abs_normalized_spinCoordinate_le_one hN U σ j
    · norm_num
  have hj : |if a = j then spinCoordinate U σ i / Real.sqrt (N : ℝ) else 0| ≤ 1 := by
    split_ifs
    · exact abs_normalized_spinCoordinate_le_one hN U σ i
    · norm_num
  exact (abs_sub _ _).trans (by linarith)

lemma hasDerivAt_spectralSpinFeature_plane {N : ℕ} (U : Orthogonal N)
    (I : Finset (Fin N)) (σ : Spin N) (i j : Fin N) (a : I) (t : ℝ) :
    HasDerivAt (fun s => spectralSpinFeature (matrixRotation (planeRotation i j s * U)) I σ a)
      (spectralSpinPlaneDerivative (planeRotation i j t * U) σ i j a) t := by
  have hd := (hasDerivAt_planeRotation_coordinate i j a U (spinVector σ) t).div_const
    (Real.sqrt (N : ℝ))
  convert hd using 1
  · rfl
  · simp only [spectralSpinPlaneDerivative, spinCoordinate, sub_div, ite_div, zero_div]

/-- The ordinary product-rule derivative of one spectral tensor feature. -/
def spectralTensorPlaneDerivative {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ : Spin N)
    (i j : Fin N) (v : SpectralTensorIndex I d) : ℝ :=
  ∑ a, (∏ b ∈ Finset.univ.erase a,
      tensorFeature (d b) (spectralSpinFeature (matrixRotation U) (I b) σ) (v b)) *
    ∑ k : Fin (d a), (∏ l ∈ Finset.univ.erase k,
      spectralSpinFeature (matrixRotation U) (I a) σ (v a l)) *
        spectralSpinPlaneDerivative U σ i j (v a k)

lemma hasDerivAt_spectralMonomialFeature_plane {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ : Spin N)
    (i j : Fin N) (v : SpectralTensorIndex I d) (t : ℝ) :
    HasDerivAt (fun s => spectralMonomialFeature (matrixRotation (planeRotation i j s * U)) I d σ v)
      (spectralTensorPlaneDerivative (planeRotation i j t * U) I d σ i j v) t := by
  have hi (a : Fin m) := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun k _ => hasDerivAt_spectralSpinFeature_plane U (I a) σ i j (v a k) t)
  have hd := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun a _ => hi a)
  simpa only [spectralMonomialFeature, tensorFeature, spectralTensorPlaneDerivative,
    smul_eq_mul] using hd

lemma spectralTensorPlaneDerivative_abs_le {N m : ℕ} (hN : 0 < N)
    (U : Orthogonal N) (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ : Spin N)
    (i j : Fin N) (v : SpectralTensorIndex I d) :
    |spectralTensorPlaneDerivative U I d σ i j v| ≤ 2 * ∑ a, (d a : ℝ) := by
  have hp (a : Fin m) (s : Finset (Fin (d a))) :
      |∏ l ∈ s, spectralSpinFeature (matrixRotation U) (I a) σ (v a l)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
      (fun l _ => spectralSpinFeature_abs_le_one hN U (I a) σ (v a l))
  have ht (a : Fin m) :
      |tensorFeature (d a) (spectralSpinFeature (matrixRotation U) (I a) σ) (v a)| ≤ 1 := hp a Finset.univ
  have ho (a : Fin m) :
      |∏ b ∈ Finset.univ.erase a,
        tensorFeature (d b) (spectralSpinFeature (matrixRotation U) (I b) σ) (v b)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun b _ => ht b)
  have hk (a : Fin m) : |∑ k : Fin (d a),
      (∏ l ∈ Finset.univ.erase k, spectralSpinFeature (matrixRotation U) (I a) σ (v a l)) *
        spectralSpinPlaneDerivative U σ i j (v a k)| ≤ 2 * d a := by
    calc
      _ ≤ ∑ k : Fin (d a), |(∏ l ∈ Finset.univ.erase k,
          spectralSpinFeature (matrixRotation U) (I a) σ (v a l)) *
          spectralSpinPlaneDerivative U σ i j (v a k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin (d a), (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        simpa only [one_mul] using mul_le_mul (hp a _)
          (spectralSpinPlaneDerivative_abs_le hN U σ i j (v a k)) (abs_nonneg _) zero_le_one
      _ = _ := by simp; ring
  unfold spectralTensorPlaneDerivative
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ a, 1 * (2 * (d a : ℝ)) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul (ho a) (hk a) (abs_nonneg _) zero_le_one
    _ = _ := by simp only [one_mul, Finset.mul_sum]

lemma measurable_spectralSpinPlaneDerivative {N : ℕ} (σ : Spin N) (i j a : Fin N) :
    Measurable (fun U : Orthogonal N => spectralSpinPlaneDerivative U σ i j a) := by
  unfold spectralSpinPlaneDerivative
  split_ifs
  · exact ((measurable_spinCoordinate σ j).div_const _).sub ((measurable_spinCoordinate σ i).div_const _)
  · exact ((measurable_spinCoordinate σ j).div_const _).sub measurable_const
  · exact measurable_const.sub ((measurable_spinCoordinate σ i).div_const _)
  · exact measurable_const

lemma measurable_spectralTensorPlaneDerivative {N m : ℕ}
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ : Spin N)
    (i j : Fin N) (v : SpectralTensorIndex I d) :
    Measurable (fun U : Orthogonal N => spectralTensorPlaneDerivative U I d σ i j v) := by
  have hf (a : Fin m) (l : Fin (d a)) :
      Measurable (fun U : Orthogonal N => spectralSpinFeature (matrixRotation U) (I a) σ (v a l)) :=
    (measurable_spinCoordinate σ (v a l)).div_const _
  unfold spectralTensorPlaneDerivative tensorFeature
  exact Finset.measurable_sum _ fun a _ =>
    (Finset.measurable_prod _ fun b _ => Finset.measurable_prod _ fun l _ => hf b l).mul
      (Finset.measurable_sum _ fun k _ =>
        (Finset.measurable_prod _ fun l _ => hf a l).mul
          (measurable_spectralSpinPlaneDerivative σ i j (v a k)))

/-- The independent linear enrichment has zero rotation derivative. -/
def spinTensorPlaneDerivative {N m k : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (σ : Spin N) (i j : Fin N) : SpinTensorIndex I degree → ℝ
  | Sum.inl _ => 0
  | Sum.inr v => amplitude v.1 * spectralTensorPlaneDerivative U I (degree v.1) σ i j v.2

lemma hasDerivAt_spinTensorFeature_plane {N m k : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (σ : Spin N) (i j : Fin N) (a : SpinTensorIndex I degree) (t : ℝ) :
    HasDerivAt (fun s => spinTensorFeature (matrixRotation (planeRotation i j s * U)) I degree amplitude σ a)
      (spinTensorPlaneDerivative (planeRotation i j t * U) I degree amplitude σ i j a) t := by
  cases a with
  | inl a => exact hasDerivAt_const t _
  | inr a => exact (hasDerivAt_spectralMonomialFeature_plane U I (degree a.1) σ i j a.2 t).const_mul _

def spinTensorDerivativeCap {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) : SpinTensorIndex I degree → ℝ
  | Sum.inl _ => 0
  | Sum.inr v => |amplitude v.1| * (2 * ∑ a, (degree v.1 a : ℝ))

lemma spinTensorPlaneDerivative_abs_le {N m k : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (σ : Spin N) (i j : Fin N) (a : SpinTensorIndex I degree) :
    |spinTensorPlaneDerivative U I degree amplitude σ i j a| ≤
      spinTensorDerivativeCap I degree amplitude a := by
  cases a with
  | inl a => simp only [spinTensorPlaneDerivative, spinTensorDerivativeCap, abs_zero, le_refl]
  | inr a =>
    rw [spinTensorPlaneDerivative, spinTensorDerivativeCap, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (spectralTensorPlaneDerivative_abs_le hN U I (degree a.1) σ i j a.2) (abs_nonneg _)

lemma measurable_spinTensorPlaneDerivative {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (σ : Spin N) (i j : Fin N) (a : SpinTensorIndex I degree) :
    Measurable (fun U : Orthogonal N => spinTensorPlaneDerivative U I degree amplitude σ i j a) := by
  cases a with
  | inl a => exact measurable_const
  | inr a => exact (measurable_spectralTensorPlaneDerivative I (degree a.1) σ i j a.2).const_mul _

/-- The actual derivative coefficient map uses precisely the same Gaussian
namespaces and ancestor tags as the Hamiltonian. -/
def tensorNamespacedPlaneCoefficients {N m k : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (i j : Fin N) (x : Spin N × LabeledLeaf n) : ℕ →₀ ℝ :=
  featureCoefficients (fun a : Fin (n + 1) × SpinTensorIndex I degree =>
    tensorNamespaceTag I degree (a.1, (labeledAddress n x.2).take a.1, a.2))
    (fun a => (NNReal.sqrt (v a.1 a.2) : ℝ) *
      spinTensorPlaneDerivative U I degree amplitude x.1 i j a.2)

lemma hasDerivAt_tensorNamespacedCoefficient_plane {N m k : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (i j : Fin N) (x : Spin N × LabeledLeaf n) (q : ℕ) (t : ℝ) :
    HasDerivAt (fun s => tensorNamespacedCoefficients (matrixRotation (planeRotation i j s * U))
      I degree amplitude n v x q)
      (tensorNamespacedPlaneCoefficients (planeRotation i j t * U) I degree amplitude n v i j x q) t := by
  simp only [tensorNamespacedCoefficients, tensorNamespacedPlaneCoefficients, featureCoefficients_apply]
  apply HasDerivAt.fun_sum
  intro a _
  split_ifs
  · exact (hasDerivAt_spinTensorFeature_plane U I degree amplitude x.1 i j a.2 t).const_mul _
  · exact hasDerivAt_const t 0

lemma hasDerivAt_tensorNamespacedField_plane {N m k : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (i j : Fin N) (x : Spin N × LabeledLeaf n) (g : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (fun s => cylinderField (tensorNamespacedCoefficients
      (matrixRotation (planeRotation i j s * U)) I degree amplitude n v x) g)
      (cylinderField (tensorNamespacedPlaneCoefficients (planeRotation i j t * U)
        I degree amplitude n v i j x) g) t := by
  simp only [tensorNamespacedCoefficients, tensorNamespacedPlaneCoefficients, cylinderField_feature]
  exact HasDerivAt.fun_sum fun a _ =>
    ((hasDerivAt_spinTensorFeature_plane U I degree amplitude x.1 i j a.2 t).const_mul _).mul_const _

lemma measurable_tensorNamespacedPlaneCoefficient {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (i j : Fin N) (x : Spin N × LabeledLeaf n) (q : ℕ) :
    Measurable (fun U : Orthogonal N => tensorNamespacedPlaneCoefficients U I degree amplitude n v i j x q) := by
  simp only [tensorNamespacedPlaneCoefficients, featureCoefficients_apply]
  apply Finset.measurable_sum
  intro a _
  split_ifs
  · exact (measurable_spinTensorPlaneDerivative I degree amplitude x.1 i j a.2).const_mul _
  · exact measurable_const

def tensorNamespacedDerivativeCap {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) : ℝ :=
  ∑ a : Fin (n + 1) × SpinTensorIndex I degree,
    (NNReal.sqrt (v a.1 a.2) : ℝ) * spinTensorDerivativeCap I degree amplitude a.2

lemma tensorNamespacedPlaneCoefficient_abs_le {N m k : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (i j : Fin N) (x : Spin N × LabeledLeaf n) (q : ℕ) :
    |tensorNamespacedPlaneCoefficients U I degree amplitude n v i j x q| ≤
      tensorNamespacedDerivativeCap I degree amplitude n v := by
  simp only [tensorNamespacedPlaneCoefficients, featureCoefficients_apply, tensorNamespacedDerivativeCap]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  have hc : 0 ≤ spinTensorDerivativeCap I degree amplitude a.2 := by
    cases a.2 <;> simp only [spinTensorDerivativeCap] <;> positivity
  split_ifs
  · rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (spinTensorPlaneDerivative_abs_le hN U I degree amplitude x.1 i j a.2) (NNReal.coe_nonneg _)
  · simpa only [abs_zero] using mul_nonneg (NNReal.coe_nonneg _) hc

/-- Mixed endpoint covariance is invariant under the injective change of
Gaussian coordinate namespaces, not just at coinciding endpoints. -/
lemma tensorNamespacedCoefficients_mixed_cross_eq {N m k : ℕ} (U V : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorNamespacedCoefficients U I degree amplitude n v x)
      (tensorNamespacedCoefficients V I degree amplitude n v y) =
    cylinderCross (tensorLeafCoefficients U I degree amplitude n v x)
      (tensorLeafCoefficients V I degree amplitude n v y) := by
  rw [tensorNamespacedCoefficients, tensorNamespacedCoefficients, tensorLeafCoefficients,
    tensorLeafCoefficients, featureCoefficients_cross, featureCoefficients_cross]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have ht : (tensorNamespaceTag I degree (a.1, (labeledAddress n x.2).take a.1, a.2) =
      tensorNamespaceTag I degree (b.1, (labeledAddress n y.2).take b.1, b.2)) ↔
      treeFeatureTag n x.2 a = treeFeatureTag n y.2 b := by
    exact (tensorNamespaceTag_injective I degree).eq_iff.trans Encodable.encode_injective.eq_iff.symm
  simp only [ht]

/-- Coefficient differentiation commutes with the finite cross covariance. -/
lemma hasDerivAt_tensorNamespaced_cross_plane {N m k : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (i j : Fin N) (x y : Spin N × LabeledLeaf n) :
    HasDerivAt (fun s => cylinderCross
      (tensorNamespacedCoefficients (matrixRotation (planeRotation i j s * U)) I degree amplitude n v x)
      (tensorNamespacedCoefficients (matrixRotation U) I degree amplitude n v y))
      (cylinderCross (tensorNamespacedPlaneCoefficients U I degree amplitude n v i j x)
        (tensorNamespacedCoefficients (matrixRotation U) I degree amplitude n v y)) 0 := by
  simp only [tensorNamespacedCoefficients, tensorNamespacedPlaneCoefficients, featureCoefficients_cross]
  apply HasDerivAt.fun_sum
  intro a _
  apply HasDerivAt.fun_sum
  intro b _
  by_cases h : tensorNamespaceTag I degree (a.1, (labeledAddress n x.2).take a.1, a.2) =
      tensorNamespaceTag I degree (b.1, (labeledAddress n y.2).take b.1, b.2)
  · simp only [h, ite_true]
    simpa only [planeRotation_zero, one_mul] using
      ((hasDerivAt_spinTensorFeature_plane U I degree amplitude x.1 i j a.2 0).const_mul
        (NNReal.sqrt (v a.1 a.2) : ℝ)).mul_const
          ((NNReal.sqrt (v b.1 b.2) : ℝ) * spinTensorFeature (matrixRotation U) I degree amplitude y.1 b.2)
  · simp only [h, ite_false]
    exact hasDerivAt_const 0 0

lemma spinTensorFeature_mixed_rotation_cross {N m k : ℕ} (U V : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : ℝ≥0) (monomial : Fin k → ℝ≥0) (σ τ : Spin N) :
    (∑ a : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial a : ℝ) *
      spinTensorFeature U I degree amplitude σ a * spinTensorFeature V I degree amplitude τ a) =
      (site : ℝ) * (∑ a, spinValue (σ a) * spinValue (τ a)) +
        ∑ r, (monomial r : ℝ) * amplitude r ^ 2 *
          ∏ a, mixedProjectedOverlap U V (I a) σ τ ^ degree r a := by
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [tensorVarianceProfile, spinTensorFeature]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  · apply Finset.sum_congr rfl
    intro r _
    calc
      _ = (monomial r : ℝ) * amplitude r ^ 2 *
          ∑ a : SpectralTensorIndex I (degree r), spectralMonomialFeature U I (degree r) σ a *
            spectralMonomialFeature V I (degree r) τ a := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by rw [spectralMonomialFeature_mixed_cross]

private lemma tensorPrefix_weighted_sum (q : ℕ → ℝ) (n d : ℕ) (hd : d ≤ n) (c : ℝ) :
    (∑ i : Fin (n + 1), if i.1 ≤ d then pathIncrement q i * c else 0) = q d * c := by
  calc
    _ = (∑ i : Fin (n + 1), if i.1 ≤ d then pathIncrement q i else 0) * c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = _ := by rw [pathIncrement_prefix q n d hd]

private lemma tensorPrefix_linear_monomials {k : ℕ} (h : ℕ → ℝ)
    (q : Fin k → ℕ → ℝ) (n d : ℕ) (hd : d ≤ n) (a : ℝ) (b : Fin k → ℝ) :
    (∑ i : Fin (n + 1), if i.1 ≤ d then
      pathIncrement h i * a + ∑ j, pathIncrement (q j) i * b j else 0) =
      h d * a + ∑ j, q j d * b j := by
  calc
    _ = (∑ i : Fin (n + 1), ((if i.1 ≤ d then pathIncrement h i * a else 0) +
        ∑ j, if i.1 ≤ d then pathIncrement (q j) i * b j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_add_distrib, tensorPrefix_weighted_sum h n d hd a, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact tensorPrefix_weighted_sum (q j) n d hd (b j)

/-- The tensor covariance at two different rotations. -/
lemma tensorNamespacedPath_mixed_cross {N m k : ℕ} (U V : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorNamespacedCoefficients U I degree amplitude n
      (fun i => tensorPathProfile I degree n treeDegree h i) x)
      (tensorNamespacedCoefficients V I degree amplitude n
        (fun i => tensorPathProfile I degree n treeDegree h i) y) =
      h (labeledCommonDepth n x.2 y.2) * (∑ a, spinValue (x.1 a) * spinValue (y.1 a)) +
        ∑ r, amplitude r ^ 2 * (∏ a, mixedProjectedOverlap U V (I a) x.1 y.1 ^ degree r a) *
          treeOverlap n x.2 y.2 ^ treeDegree r := by
  rw [tensorNamespacedCoefficients_mixed_cross_eq, tensorLeafCoefficients_cross]
  simp_rw [tensorPathProfile, spinTensorFeature_mixed_rotation_cross, varianceIncrement_coe hh h0,
    varianceIncrement_coe (monomialPath_monotone n _) (monomialPath_nonneg n _ 0)]
  have he := tensorPrefix_linear_monomials h (fun r => monomialPath n (treeDegree r)) n
    (labeledCommonDepth n x.2 y.2) (labeledCommonDepth_le n x.2 y.2)
    (∑ a, spinValue (x.1 a) * spinValue (y.1 a))
    (fun r => amplitude r ^ 2 * ∏ a, mixedProjectedOverlap U V (I a) x.1 y.1 ^ degree r a)
  simp_rw [mul_assoc] at he ⊢
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  simp only [monomialPath, treeOverlap]
  ring

/-- The coefficient derivative is exactly the one-endpoint spectral/tree
covariance derivative used in the normalized Ward error estimate. -/
theorem tensorNamespacedPlaneCross_eq {N m k : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (i j : Fin N) (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorNamespacedPlaneCoefficients U I degree amplitude n
      (fun a => tensorPathProfile I degree n treeDegree h a) i j x)
      (tensorNamespacedCoefficients (matrixRotation U) I degree amplitude n
        (fun a => tensorPathProfile I degree n treeDegree h a) y) =
      ∑ r, amplitude r ^ 2 * treeOverlap n x.2 y.2 ^ treeDegree r *
        spectralMonomialEndpointDerivative U I (degree r) i j x.1 y.1 := by
  have hd := hasDerivAt_tensorNamespaced_cross_plane U I degree amplitude n
    (fun a => tensorPathProfile I degree n treeDegree h a) i j x y
  simp_rw [tensorNamespacedPath_mixed_cross _ _ I degree amplitude n treeDegree h hh h0 x y] at hd
  have he := (HasDerivAt.fun_sum (u := Finset.univ) (fun r _ =>
    ((hasDerivAt_spectralMonomial_mixed_plane U I (degree r) i j x.1 y.1).const_mul
      (amplitude r ^ 2)).mul_const (treeOverlap n x.2 y.2 ^ treeDegree r))).const_add
        (h (labeledCommonDepth n x.2 y.2) * (∑ a, spinValue (x.1 a) * spinValue (y.1 a)))
  have hu := hd.unique he
  calc
    _ = ∑ r, amplitude r ^ 2 * spectralMonomialEndpointDerivative U I (degree r) i j x.1 y.1 *
        treeOverlap n x.2 y.2 ^ treeDegree r := hu
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      ring

/-- A finite spin/leaf restriction has one Gaussian coordinate prefix
containing both the actual Hamiltonian coefficients and their plane
derivatives, uniformly in the rotation. -/
lemma finite_tensorNamespaced_support_bound {S : Type*} [Fintype S] {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (i j : Fin N) (x : S → Spin N × LabeledLeaf n) :
    ∃ d : ℕ,
      (∀ U : Orthogonal N, ∀ s q, q ∈ (tensorNamespacedCoefficients (matrixRotation U)
        I degree amplitude n v (x s)).support → q < d + 1) ∧
      (∀ U : Orthogonal N, ∀ s q, q ∈ (tensorNamespacedPlaneCoefficients U
        I degree amplitude n v i j (x s)).support → q < d + 1) := by
  classical
  let tag := fun s (a : Fin (n + 1) × SpinTensorIndex I degree) =>
    tensorNamespaceTag I degree (a.1, (labeledAddress n (x s).2).take a.1, a.2)
  let d := ∑ s : S, ∑ a : Fin (n + 1) × SpinTensorIndex I degree, (tag s a + 1)
  have ht (s : S) (a : Fin (n + 1) × SpinTensorIndex I degree) : tag s a < d + 1 := by
    have ha : tag s a + 1 ≤ ∑ b : Fin (n + 1) × SpinTensorIndex I degree, (tag s b + 1) :=
      Finset.single_le_sum (f := fun b : Fin (n + 1) × SpinTensorIndex I degree => tag s b + 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    have hs : (∑ b : Fin (n + 1) × SpinTensorIndex I degree, (tag s b + 1)) ≤ d :=
      Finset.single_le_sum
        (f := fun t : S => ∑ b : Fin (n + 1) × SpinTensorIndex I degree, (tag t b + 1))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    omega
  have hz (s : S) (q : ℕ) (hq : d + 1 ≤ q) (a : Fin (n + 1) × SpinTensorIndex I degree) :
      tag s a ≠ q := by have := ht s a; omega
  refine ⟨d, ?_, ?_⟩
  · intro U s q hq
    by_contra hn
    have he : tensorNamespacedCoefficients (matrixRotation U) I degree amplitude n v (x s) q = 0 := by
      simp only [tensorNamespacedCoefficients, featureCoefficients_apply]
      apply Finset.sum_eq_zero
      intro a _
      exact ite_eq_right (hz s q (Nat.le_of_not_gt hn) a)
    exact Finsupp.mem_support_iff.mp hq he
  · intro U s q hq
    by_contra hn
    have he : tensorNamespacedPlaneCoefficients U I degree amplitude n v i j (x s) q = 0 := by
      simp only [tensorNamespacedPlaneCoefficients, featureCoefficients_apply]
      apply Finset.sum_eq_zero
      intro a _
      exact ite_eq_right (hz s q (Nat.le_of_not_gt hn) a)
    exact Finsupp.mem_support_iff.mp hq he

lemma measurable_tensorNamespacedCoefficient {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x : Spin N × LabeledLeaf n) (q : ℕ) :
    Measurable (fun U : SpecialOrthogonal N =>
      tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v x q) := by
  simp only [tensorNamespacedCoefficients, featureCoefficients_apply]
  apply Finset.measurable_sum
  intro a _
  split_ifs
  · exact (measurable_spinTensorFeature I degree amplitude x.1 a.2).const_mul _
  · exact measurable_const

/-- The exact covariance appearing after finite Gaussian integration by
parts contracts to the tensor Ward error. -/
theorem tensorNamespacedPlane_contraction_eq {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (n : ℕ) (u : Fin N → ℝ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (η θ : Spin N) (x y : Spin N × LabeledLeaf n) :
    (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, spinCoordinate U η i * spinCoordinate U θ j *
      cylinderCross (tensorNamespacedPlaneCoefficients U I degree (tensorPerturbationAmplitude N u) n
        (fun a => tensorPathProfile I degree n treeDegree h a) i j x)
        (tensorNamespacedCoefficients (matrixRotation U) I degree (tensorPerturbationAmplitude N u) n
          (fun a => tensorPathProfile I degree n treeDegree h a) y) =
      tensorWardPerturbationError U I degree treeDegree n u J K η θ x y := by
  simp_rw [tensorNamespacedPlaneCross_eq U I degree (tensorPerturbationAmplitude N u) n treeDegree h hh h0]
  exact (tensorWardPerturbationError_eq U I degree treeDegree n u J K η θ x y).symm

end InvariantIsing

end

end OAI
