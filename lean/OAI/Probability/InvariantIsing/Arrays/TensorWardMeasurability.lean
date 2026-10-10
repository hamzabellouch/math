import OAI.Probability.InvariantIsing.Arrays.TensorDiagonalWardCorrectionBound

namespace OAI

/-! Joint measurability and bounded integrability of the actual finite
principal Ward term and its Gaussian correction. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S Ω : Type*} [Fintype S] [MeasurableSpace Ω]

lemma measurable_finiteGibbs (w : S → ℝ) (H : Ω → S → ℝ)
    (hH : ∀ s, Measurable (fun ω => H ω s)) (s : S) :
    Measurable (fun ω => finiteGibbs w (H ω) s) := by
  unfold finiteGibbs finitePartition
  exact (measurable_const.mul (hH s).exp).div
    (Finset.measurable_sum _ fun t _ => measurable_const.mul (hH t).exp)

lemma measurable_gibbsPairAverage (w : S → ℝ) (H : Ω → S → ℝ) (O : Ω → S → S → ℝ)
    (hH : ∀ s, Measurable (fun ω => H ω s))
    (hO : ∀ s t, Measurable (fun ω => O ω s t)) :
    Measurable (fun ω => gibbsPairAverage w (H ω) (O ω)) := by
  unfold gibbsPairAverage
  exact Finset.measurable_sum _ fun s _ => Finset.measurable_sum _ fun t _ =>
    ((measurable_finiteGibbs w H hH s).mul (measurable_finiteGibbs w H hH t)).mul (hO s t)

lemma measurable_gibbsTripleAverage (w : S → ℝ) (H : Ω → S → ℝ) (O : Ω → S → S → S → ℝ)
    (hH : ∀ s, Measurable (fun ω => H ω s))
    (hO : ∀ s t u, Measurable (fun ω => O ω s t u)) :
    Measurable (fun ω => gibbsTripleAverage w (H ω) (O ω)) := by
  unfold gibbsTripleAverage
  exact Finset.measurable_sum _ fun s _ => Finset.measurable_sum _ fun t _ =>
    Finset.measurable_sum _ fun u _ =>
      (((measurable_finiteGibbs w H hH s).mul (measurable_finiteGibbs w H hH t)).mul
        (measurable_finiteGibbs w H hH u)).mul (hO s t u)

lemma measurable_gaussianWardCorrection_joint (w : S → ℝ) (H O : Ω → S → ℝ)
    (K : Ω → S → S → ℝ) (hH : ∀ s, Measurable (fun ω => H ω s))
    (hO : ∀ s, Measurable (fun ω => O ω s)) (hK : ∀ s t, Measurable (fun ω => K ω s t)) :
    Measurable (fun ω => gaussianWardCorrection w (H ω) (O ω) (K ω)) := by
  unfold gaussianWardCorrection
  exact (((measurable_gibbsAverage w H _ hH (fun s => (hO s).mul (hK s s))).sub
    (measurable_gibbsPairAverage w H _ hH (fun s t => (hO s).mul (hK s t)))).sub
    (measurable_gibbsPairAverage w H _ hH (fun s t => (hO s).mul ((hK t s).add (hK t t))))).add
    ((measurable_gibbsTripleAverage w H _ hH (fun s t u => (hO s).mul (hK t u))).const_mul 2)

omit [Fintype S] [MeasurableSpace Ω] in
lemma measurable_tensorRestrictionHamiltonian {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n) (s : S) :
    Measurable (fun z : SpecialOrthogonal N × (ℕ → ℝ) =>
      tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2 s) :=
  (((measurable_orbitHamiltonian eig c (x s).1).comp measurable_specialToOrthogonal).comp
    measurable_fst).add (measurable_tensorNamespacedFields_joint I degree amplitude n v (x s))

omit [Fintype S] [MeasurableSpace Ω] in
lemma measurable_tensorNamespacedPlaneCross {N m k n : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (i j : Fin N)
    (x y : Spin N × LabeledLeaf n) :
    Measurable (fun U : SpecialOrthogonal N => cylinderCross
      (tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j x)
      (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v y)) := by
  simp only [tensorNamespacedPlaneCoefficients, tensorNamespacedCoefficients, featureCoefficients_cross]
  apply Finset.measurable_sum
  intro a _
  apply Finset.measurable_sum
  intro b _
  split_ifs
  · exact (((measurable_spinTensorPlaneDerivative I degree amplitude x.1 i j a.2).comp
      measurable_specialToOrthogonal).const_mul _).mul
        ((measurable_spinTensorFeature I degree amplitude y.1 b.2).const_mul _)
  · exact measurable_const

omit [Fintype S] [MeasurableSpace Ω] in
lemma measurable_tensorRestrictionPairCovarianceDerivative {N m k n : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (p q : S × S) :
    Measurable (fun U => tensorRestrictionPairCovarianceDerivative I degree amplitude v x i j U p q) := by
  let C := fun (U : SpecialOrthogonal N) (a b : S) => cylinderCross
    (tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j (x a))
    (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x b))
  have hm (a b : S) : Measurable (fun U => C U a b) :=
    measurable_tensorNamespacedPlaneCross I degree amplitude v i j (x a) (x b)
  have he : (fun U => tensorRestrictionPairCovarianceDerivative I degree amplitude v x i j U p q) =
      fun U => (C U p.1 q.1 + C U p.1 q.2) + (C U p.2 q.1 + C U p.2 q.2) := by
    funext U
    simp only [tensorRestrictionPairCovarianceDerivative, cylinderCross_add_left, cylinderCross_add_right, C]
    ring
  rw [he]
  exact ((hm p.1 q.1).add (hm p.1 q.2)).add ((hm p.2 q.1).add (hm p.2 q.2))

omit [MeasurableSpace Ω] in
lemma measurable_tensorRestrictionOffVariation {N m k n : ℕ} (w : S → ℝ) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (F : Spin N → Spin N → ℝ) :
    Measurable (fun z : SpecialOrthogonal N × (ℕ → ℝ) => finiteGibbsVariation
      (fun p : S × S => w p.1 * w p.2)
      (tensorRestrictionPairHamiltonian eig c I degree amplitude v x z.1 z.2)
      (tensorRestrictionOffObservable i j F x z.1) (tensorRestrictionMainVariation eig i j x z.1)
      (tensorRestrictionOffVariation i j F x z.1)) := by
  have hc (s : S) (a : Fin N) : Measurable (fun z : SpecialOrthogonal N × (ℕ → ℝ) =>
      spinCoordinate (specialToOrthogonal z.1) (x s).1 a) :=
    ((measurable_spinCoordinate (x s).1 a).comp measurable_specialToOrthogonal).comp measurable_fst
  apply measurable_finiteGibbsVariation
  · intro p
    simp_rw [tensorRestrictionPairHamiltonian_eq]
    exact (measurable_tensorRestrictionHamiltonian eig c I degree amplitude v x p.1).add
      (measurable_tensorRestrictionHamiltonian eig c I degree amplitude v x p.2)
  · intro p
    exact ((hc p.1 i).mul (hc p.2 j)).mul_const _
  · intro p
    exact (((hc p.1 i).mul (hc p.1 j)).add ((hc p.2 i).mul (hc p.2 j))).const_mul _
  · intro p
    exact (((hc p.1 j).mul (hc p.2 j)).sub ((hc p.1 i).mul (hc p.2 i))).mul_const _

omit [MeasurableSpace Ω] in
lemma integrable_tensorRestrictionOffVariation {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ σ τ, |F σ τ| ≤ B) :
    Integrable (fun z : SpecialOrthogonal N × (ℕ → ℝ) => finiteGibbsVariation
      (fun p : S × S => w p.1 * w p.2)
      (tensorRestrictionPairHamiltonian eig c I degree amplitude v x z.1 z.2)
      (tensorRestrictionOffObservable i j F x z.1) (tensorRestrictionMainVariation eig i j x z.1)
      (tensorRestrictionOffVariation i j F x z.1)) (μ.prod gaussianCoordinates) := by
  apply integrable_of_measurable_abs_le (measurable_tensorRestrictionOffVariation w eig c I degree amplitude v x i j F)
    (c := 2 * N * B + 2 * (N * B) * (|eig i - eig j| * (2 * N)))
  intro z
  apply abs_gibbsVariation_le (GibbsReference_pair hw) _ _ _ _ (by positivity)
  · intro p
    change |spinCoordinate (specialToOrthogonal z.1) (x p.1).1 i *
      spinCoordinate (specialToOrthogonal z.1) (x p.2).1 j * F (x p.1).1 (x p.2).1| ≤ _
    rw [abs_mul]
    exact mul_le_mul (abs_crossCoordinateProduct_le i j _ _ _) (hF _ _) (abs_nonneg _) (Nat.cast_nonneg _)
  · intro p
    unfold tensorRestrictionMainVariation
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hh := (abs_add_le _ _).trans (add_le_add
      (abs_coordinateProduct_le i j (specialToOrthogonal z.1) (x p.1).1)
      (abs_coordinateProduct_le i j (specialToOrthogonal z.1) (x p.2).1))
    linarith
  · intro p
    unfold tensorRestrictionOffVariation offCoordinateVariation
    rw [abs_mul]
    apply mul_le_mul _ (hF _ _) (abs_nonneg _) (by positivity)
    have hh := (abs_sub _ _).trans (add_le_add
      (abs_crossCoordinateProduct_le j j (specialToOrthogonal z.1) (x p.1).1 (x p.2).1)
      (abs_crossCoordinateProduct_le i i (specialToOrthogonal z.1) (x p.1).1 (x p.2).1))
    linarith

omit [MeasurableSpace Ω] in
def tensorRestrictionOffCorrection {N m k n : ℕ} (w : S → ℝ) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (F : Spin N → Spin N → ℝ) (z : SpecialOrthogonal N × (ℕ → ℝ)) : ℝ :=
  gaussianWardCorrection (fun p : S × S => w p.1 * w p.2)
    (tensorRestrictionPairHamiltonian eig c I degree amplitude v x z.1 z.2)
    (tensorRestrictionOffObservable i j F x z.1)
    (tensorRestrictionPairCovarianceDerivative I degree amplitude v x i j z.1)

omit [MeasurableSpace Ω] in
lemma measurable_tensorRestrictionOffCorrection {N m k n : ℕ} (w : S → ℝ) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (F : Spin N → Spin N → ℝ) :
    Measurable (tensorRestrictionOffCorrection w eig c I degree amplitude v x i j F) := by
  have hH (p : S × S) : Measurable (fun z : SpecialOrthogonal N × (ℕ → ℝ) =>
      tensorRestrictionPairHamiltonian eig c I degree amplitude v x z.1 z.2 p) := by
    simp_rw [tensorRestrictionPairHamiltonian_eq]
    exact (measurable_tensorRestrictionHamiltonian eig c I degree amplitude v x p.1).add
      (measurable_tensorRestrictionHamiltonian eig c I degree amplitude v x p.2)
  have hO (p : S × S) : Measurable (fun z : SpecialOrthogonal N × (ℕ → ℝ) =>
      tensorRestrictionOffObservable i j F x z.1 p) :=
    (((measurable_spinCoordinate (x p.1).1 i).mul
      (measurable_spinCoordinate (x p.2).1 j)).mul_const _).comp
        (measurable_specialToOrthogonal.comp measurable_fst)
  have hK (p q : S × S) : Measurable (fun z : SpecialOrthogonal N × (ℕ → ℝ) =>
      tensorRestrictionPairCovarianceDerivative I degree amplitude v x i j z.1 p q) :=
    (measurable_tensorRestrictionPairCovarianceDerivative I degree amplitude v x i j p q).comp measurable_fst
  exact measurable_gaussianWardCorrection_joint _ _ _ _ hH hO hK

omit [MeasurableSpace Ω] in
lemma tensorRestrictionOffCorrection_abs_le {N m n : ℕ} (hN : 0 < N)
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ σ τ, |F σ τ| ≤ B)
    (z : SpecialOrthogonal N × (ℕ → ℝ)) :
    |tensorRestrictionOffCorrection w eig c I degree (tensorPerturbationAmplitude N u)
      (fun a => tensorPathProfile I degree n treeDegree h a) x i j F z| ≤
      (N : ℝ) ^ 2 * (192 * B * D * perturbationScale N ^ 2) := by
  let amp := tensorPerturbationAmplitude N u
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 := fun a => tensorPathProfile I degree n treeDegree h a
  have he := tensorRestriction_actualWardCorrection_abs_le hN z.1 hw
    (tensorRestrictionPairHamiltonian eig c I degree amp v x z.1 z.2) I degree treeDegree u hu D hD hdegree
    h hh h0 {i} {j} F B hB hF x
  simp only [Finset.sum_singleton] at he
  have hn : (N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN)
  calc
    _ = (N : ℝ) ^ 2 * |(N : ℝ)⁻¹ ^ 2 * gaussianWardCorrection
        (fun p : S × S => w p.1 * w p.2) (tensorRestrictionPairHamiltonian eig c I degree amp v x z.1 z.2)
        (tensorRestrictionOffObservable i j F x z.1)
        (tensorRestrictionPairCovarianceDerivative I degree amp v x i j z.1)| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg ((N : ℝ)⁻¹))]
      field_simp
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left he (sq_nonneg _)

omit [MeasurableSpace Ω] in
lemma integrable_tensorRestrictionOffCorrection {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ σ τ, |F σ τ| ≤ B) :
    Integrable (tensorRestrictionOffCorrection w eig c I degree (tensorPerturbationAmplitude N u)
      (fun a => tensorPathProfile I degree n treeDegree h a) x i j F) (μ.prod gaussianCoordinates) :=
  integrable_of_measurable_abs_le (measurable_tensorRestrictionOffCorrection w eig c I degree
    (tensorPerturbationAmplitude N u) (fun a => tensorPathProfile I degree n treeDegree h a) x i j F)
      (tensorRestrictionOffCorrection_abs_le hN hw eig c I degree treeDegree u hu D hD hdegree h hh h0 x i j F B hB hF)

end InvariantIsing

end

end OAI
