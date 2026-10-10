import OAI.Probability.InvariantIsing.Arrays.TensorWardMeasurability

namespace OAI

/-! Joint integrability for the actual finite diagonal Ward identity. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S : Type*} [Fintype S]

def tensorRestrictionDiagonalPrincipalVariation {N m k n : ℕ} (w : S → ℝ) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (z : SpecialOrthogonal N × (ℕ → ℝ)) : ℝ :=
  finiteGibbsVariation w (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
    (tensorRestrictionDiagonalObservable i j x z.1)
    (fun s => (eig i - eig j) * tensorRestrictionDiagonalObservable i j x z.1 s)
    (tensorRestrictionDiagonalVariation i j x z.1)

lemma measurable_tensorRestrictionDiagonalPrincipalVariation {N m k n : ℕ} (w : S → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x : S → Spin N × LabeledLeaf n) (i j : Fin N) :
    Measurable (tensorRestrictionDiagonalPrincipalVariation w eig c I degree amplitude v x i j) := by
  have hc (s : S) (a : Fin N) : Measurable (fun z : SpecialOrthogonal N × (ℕ → ℝ) =>
      spinCoordinate (specialToOrthogonal z.1) (x s).1 a) :=
    ((measurable_spinCoordinate (x s).1 a).comp measurable_specialToOrthogonal).comp measurable_fst
  apply measurable_finiteGibbsVariation
  · exact measurable_tensorRestrictionHamiltonian eig c I degree amplitude v x
  · intro s
    exact (hc s i).mul (hc s j)
  · intro s
    exact ((hc s i).mul (hc s j)).const_mul _
  · intro s
    exact ((hc s j).pow_const 2).sub ((hc s i).pow_const 2)

lemma integrable_tensorRestrictionDiagonalPrincipalVariation {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) :
    Integrable (tensorRestrictionDiagonalPrincipalVariation w eig c I degree amplitude v x i j)
      (μ.prod gaussianCoordinates) := by
  apply integrable_of_measurable_abs_le
    (measurable_tensorRestrictionDiagonalPrincipalVariation w eig c I degree amplitude v x i j)
    (c := N + 2 * (N : ℝ) * (|eig i - eig j| * N))
  intro z
  apply abs_gibbsVariation_le hw _ _ _ _ (Nat.cast_nonneg _)
  · intro s
    exact abs_coordinateProduct_le i j _ _
  · intro s
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_coordinateProduct_le i j _ _) (abs_nonneg _)
  · intro s
    exact abs_coordinateSquareDifference_le i j _ _

def tensorRestrictionDiagonalCorrection {N m k n : ℕ} (w : S → ℝ) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (z : SpecialOrthogonal N × (ℕ → ℝ)) : ℝ :=
  gaussianWardCorrection w (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
    (tensorRestrictionDiagonalObservable i j x z.1)
    (tensorRestrictionCovarianceDerivative I degree amplitude v x i j z.1)

lemma measurable_tensorRestrictionDiagonalCorrection {N m k n : ℕ} (w : S → ℝ) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) :
    Measurable (tensorRestrictionDiagonalCorrection w eig c I degree amplitude v x i j) := by
  have hO (s : S) : Measurable (fun z : SpecialOrthogonal N × (ℕ → ℝ) =>
      tensorRestrictionDiagonalObservable i j x z.1 s) :=
    ((measurable_spinCoordinate (x s).1 i).mul (measurable_spinCoordinate (x s).1 j)).comp
      (measurable_specialToOrthogonal.comp measurable_fst)
  have hK (s t : S) : Measurable (fun z : SpecialOrthogonal N × (ℕ → ℝ) =>
      tensorRestrictionCovarianceDerivative I degree amplitude v x i j z.1 s t) :=
    (measurable_tensorNamespacedPlaneCross I degree amplitude v i j (x s) (x t)).comp measurable_fst
  exact measurable_gaussianWardCorrection_joint _ _ _ _
    (measurable_tensorRestrictionHamiltonian eig c I degree amplitude v x) hO hK

lemma tensorRestrictionDiagonalCorrection_abs_le {N m n : ℕ} (hN : 0 < N)
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (z : SpecialOrthogonal N × (ℕ → ℝ)) :
    |tensorRestrictionDiagonalCorrection w eig c I degree (tensorPerturbationAmplitude N u)
      (fun a => tensorPathProfile I degree n treeDegree h a) x i j z| ≤
      (N : ℝ) ^ 2 * (48 * D * perturbationScale N ^ 2) := by
  let amp := tensorPerturbationAmplitude N u
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 := fun a => tensorPathProfile I degree n treeDegree h a
  have he := tensorRestriction_actualDiagonalWardCorrection_abs_le hN z.1 hw
    (tensorRestrictionHamiltonian eig c I degree amp v x z.1 z.2) I degree treeDegree u hu D hD hdegree
    h hh h0 {i} {j} x
  simp only [Finset.sum_singleton] at he
  have hn : (N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN)
  calc
    _ = (N : ℝ) ^ 2 * |(N : ℝ)⁻¹ ^ 2 * tensorRestrictionDiagonalCorrection w eig c I degree amp v x i j z| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg ((N : ℝ)⁻¹))]
      field_simp
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left he (sq_nonneg _)

lemma integrable_tensorRestrictionDiagonalCorrection {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) :
    Integrable (tensorRestrictionDiagonalCorrection w eig c I degree (tensorPerturbationAmplitude N u)
      (fun a => tensorPathProfile I degree n treeDegree h a) x i j) (μ.prod gaussianCoordinates) :=
  integrable_of_measurable_abs_le (measurable_tensorRestrictionDiagonalCorrection w eig c I degree
    (tensorPerturbationAmplitude N u) (fun a => tensorPathProfile I degree n treeDegree h a) x i j)
      (tensorRestrictionDiagonalCorrection_abs_le hN hw eig c I degree treeDegree u hu D hD hdegree h hh h0 x i j)

end InvariantIsing

end

end OAI
