import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFrozenFluctuation
import OAI.Probability.InvariantIsing.Spectral.SpectralDiagonalPerturbation
import OAI.Probability.InvariantIsing.Core.BoundedObservableMinimum

namespace OAI

/-! The actual spectral-diagonal coordinate as a bounded frozen tilt. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

abbrev TensorFlatDisorder (N n : ℕ) := (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)

def tensorNamespacedHamiltonian {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (p : TensorFlatDisorder N n) (x : Spin N × LabeledLeaf n) : ℝ :=
  rotatedEnergy eig (specialRotation p.1.1) x.1 + fieldEnergy c x.1 +
    cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1) I degree amplitude n
      (fun i => tensorPathProfile I degree n r h i) x) p.2

lemma measurable_tensorNamespacedHamiltonian {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (Function.uncurry (tensorNamespacedHamiltonian eig c I degree amplitude n r h)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n r h i
  have hf := (measurable_tensorNamespacedFields_joint I degree amplitude n v x).comp
    (measurable_fst.fst.prodMk measurable_snd :
      Measurable (fun p : TensorFlatDisorder N n => (p.1.1, p.2)))
  exact ((hr.comp measurable_fst.fst).add_const (fieldEnergy c x.1)).add hf

def tensorNamespacedReference {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) (p : TensorFlatDisorder N n) :
    Measure (Spin N × LabeledLeaf n) :=
  gibbsProbability (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2)
    (tensorNamespacedHamiltonian eig c I degree amplitude n r h p)

instance tensorNamespacedReference_probability {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) (p : TensorFlatDisorder N n) :
    IsProbabilityMeasure (tensorNamespacedReference eig c I degree amplitude n r h p) :=
  gibbsProbability_probability _ _

lemma measurable_tensorNamespacedReference {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (tensorNamespacedReference eig c I degree amplitude n r h) := by
  have : ∀ p : TensorFlatDisorder N n, IsProbabilityMeasure
      ((labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ∘
        fun p : TensorFlatDisorder N n => p.1.2) p) := fun p => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2)
    infer_instance
  exact measurable_gibbsProbability
    ((measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp
      measurable_fst.snd) (measurable_tensorNamespacedHamiltonian eig c I degree amplitude n r h)

def tensorDiagonalCGF {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) (v : Fin m → ℝ) (t : ℝ) (a : Fin m)
    (s : ℝ) (p : TensorFlatDisorder N n) : ℝ :=
  cgf (fun x : Spin N × LabeledLeaf n => projectedOverlap (specialRotation p.1.1) (I a) x.1 x.1)
    (tensorNamespacedReference (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
      c I degree amplitude n r h p) s

/-- At its true coefficient `N e_N w`, a frozen diagonal tilt is exactly
the actual perturbed partition difference. -/
theorem tensorDiagonalCGF_eq_log_difference {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w : ℝ) :
    tensorDiagonalCGF eig c I degree amplitude n r h v t a (N * perturbationScale N * w) =ᵐ[
      (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates]
      (fun p => tensorNamespacedLog (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude n r h p -
        tensorNamespacedLog (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
          c I degree amplitude n r h p) := by
  have he := tensorNamespaced_exp_integrable_ae μ
    (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude n b r h hh h0
  filter_upwards [he] with p hp
  let H := tensorNamespacedHamiltonian
    (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude n r h p
  let Y := fun x : Spin N × LabeledLeaf n => projectedOverlap (specialRotation p.1.1) (I a) x.1 x.1
  have hbnd : ∀ x, |(N * perturbationScale N * w) * Y x| ≤ |N * perturbationScale N * w| := by
    intro x
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (projectedOverlap_abs_le_one _ _ _ _) (abs_nonneg _)).trans_eq (mul_one _)
  have ht : Integrable (fun x => Real.exp (H x + (N * perturbationScale N * w) * Y x))
      (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2) := by
    simpa only [add_comm] using integrable_exp_bounded_add (H := H)
      (B := fun x => (N * perturbationScale N * w) * Y x) hp (measurable_of_countable _)
      (fun x => (le_abs_self _).trans (hbnd x))
  have heq : (fun x => H x + (N * perturbationScale N * w) * Y x) =
      tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude n r h p := by
    funext x
    dsimp only [H, Y, tensorNamespacedHamiltonian]
    rw [rotatedEnergy_diagonal_coordinate hN eig (specialRotation p.1.1) I v t a w x.1]
    ring
  change cgf Y (gibbsProbability _ H) _ = _
  rw [cgf_fold _ H Y _ hp ht, heq]
  rfl

/-- Actual full-disorder pressure moments give the diagonal CGF's mean
and concentration at every bounded coordinate value. -/
theorem tensorDiagonalCGF_statistics {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (hb : CascadeExponents n b) (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w B : ℝ)
    (hF : ∀ q : ℝ, q = w ∨ q = 0 →
      MemLp (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude n) 2 (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))))
    (hv : ∀ q : ℝ, q = w ∨ q = 0 →
      variance (tensorDisorderPressure (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude n) (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))) ≤ B) :
    let Q := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
    let R := μ.prod (tensorRootTreeLaw I degree n b
      (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))
    let M := fun q => ∫ p, tensorDisorderPressure
      (diagonalPerturbedEigenvalues eig I (Function.update v a q) t) c I degree amplitude n p ∂ R
    let Z := tensorDiagonalCGF eig c I degree amplitude n r h v t a (N * perturbationScale N * w)
    MemLp Z 2 Q ∧ (∫ p, Z p ∂Q) = N * (M w - M 0) ∧
      (∫ p, |Z p - ∫ p', Z p' ∂Q| ∂Q) ≤ 2 * N * Real.sqrt B := by
  intro Q R M Z
  let F := fun q => tensorNamespacedPressure
    (diagonalPerturbedEigenvalues eig I (Function.update v a q) t) c I degree amplitude n r h
  have hw : w = w ∨ w = 0 := Or.inl rfl
  have hz : (0 : ℝ) = w ∨ (0 : ℝ) = 0 := Or.inr rfl
  have hmw := tensorNamespacedPressure_moments μ
    (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude n b r h hb (hF w hw)
  have hmz := tensorNamespacedPressure_moments μ
    (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude n b r h hb (hF 0 hz)
  have he : Z =ᵐ[Q] fun p => (N : ℝ) * (F w p - F 0 p) := by
    filter_upwards [tensorDiagonalCGF_eq_log_difference hN μ eig c I degree amplitude n b r h hh h0 v t a w]
      with p hp
    dsimp only [Z]
    rw [hp]
    dsimp only [F, tensorNamespacedPressure]
    have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    field_simp
  have hc := centered_scaled_difference_L1_bound Q hmw.1 hmz.1
    (hmw.2.1.trans_le (hv w hw)) (hmz.2.1.trans_le (hv 0 hz)) he
  refine ⟨hc.1, ?_, ?_⟩
  · rw [integral_congr_ae he, integral_const_mul,
      integral_sub (hmw.1.integrable (by norm_num)) (hmz.1.integrable (by norm_num)),
      hmw.2.2, hmz.2.2]
  · simpa only [abs_of_nonneg (show (0 : ℝ) ≤ N from Nat.cast_nonneg N)] using hc.2

end InvariantIsing

end

end OAI
