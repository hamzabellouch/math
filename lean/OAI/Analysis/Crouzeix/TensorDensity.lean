import Mathlib
import OAI.Analysis.Crouzeix.Compression
import OAI.Analysis.Crouzeix.DiskCalculus
import OAI.Analysis.Crouzeix.MatrixContours

namespace OAI

/-! Tensor Density. -/

noncomputable section

open MeasureTheory Set Filter

open scoped Topology InnerProductSpace TensorProduct Matrix.Norms.L2Operator

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local instance tensorDensityOperatorRealNormedSpace (size : ℕ) :
    NormedSpace ℝ (Operator (Amplification H size)) :=
  NormedSpace.restrictScalars ℝ ℂ _

local instance tensorDensityOperatorCompleteSpace (size : ℕ) :
    CompleteSpace (Operator (Amplification H size)) := by
  let : ContinuousSMul ℂ (Amplification H size) := IsBoundedSMul.continuousSMul
  exact ContinuousLinearMap.instCompleteSpace

@[simp] theorem tensorOperator_one (m : ℕ) :
    tensorOperator (1 : Operator H) (1 : Coeff m) = 1 := by
  ext x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (tensorOperator 1 (1 : Coeff m)).continuous continuous_id) ?_
  intro v
  simp only [tensorOperator, ContinuousLinearMap.completion_apply_coe, map_one]
  congr 1
  change TensorProduct.mapL (ContinuousLinearMap.id ℂ H)
    (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m))) v = v
  simp

theorem tensorOperator_mul (A D : Operator H) {m : ℕ} (B C : Coeff m) :
    tensorOperator (A * D) (B * C) = tensorOperator A B * tensorOperator D C := by
  ext x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (tensorOperator (A * D) (B * C)).continuous
      ((tensorOperator A B).continuous.comp (tensorOperator D C).continuous)) ?_
  intro v
  simp only [tensorOperator, map_mul, mul_apply_eq_comp,
    ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_mul]

variable [CompleteSpace H]

theorem tensorOperator_star (A : Operator H) {m : ℕ} (B : Coeff m) :
    tensorOperator (star A) (star B) = star (tensorOperator A B) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq ((tensorOperator (star A) (star B)).continuous.inner continuous_const)
      (continuous_id.inner continuous_const)) ?_
  intro a
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner (tensorOperator A B).continuous)) ?_
  intro b
  simp only [tensorOperator, ContinuousLinearMap.completion_apply_coe,
    UniformSpace.Completion.inner_coe, map_star]
  induction a using TensorProduct.inductionOn with
  | tmul x u =>
    induction b using TensorProduct.inductionOn with
    | tmul y v => simp [ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    | add b c hb hc => simp only [inner_add_right, map_add, hb, hc]
  | add a c ha hc => simp only [inner_add_left, map_add, ha, hc]

section PositiveDensity

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] [SecondCountableTopology α] {μ : Measure α} [IsFiniteMeasure μ]

def amplifiedRoot (Λ : C(α, Operator H)) (hΛ : ∀ t, 0 ≤ Λ t) (m : ℕ) :
    C(α, Operator (Amplification H m)) :=
  ⟨fun t => tensorOperator (Compression.densityRoot Λ hΛ t) (1 : Coeff m),
    (tensorOperatorCLM (1 : Coeff m)).continuous.comp
      (Compression.densityRoot Λ hΛ).continuous⟩

def coefficientField {m : ℕ} (F : C(α, Coeff m)) :
    C(α, Operator (Amplification H m)) :=
  ⟨fun t => tensorOperator (1 : Operator H) (F t),
    (tensorCoefficientCLM (1 : Operator H) m).continuous.comp F.continuous⟩

omit [MeasurableSpace α] [BorelSpace α] [CompactSpace α] [SecondCountableTopology α] in
theorem amplifiedRoot_star_mul (Λ : C(α, Operator H)) (hΛ : ∀ t, 0 ≤ Λ t)
    (m : ℕ) (t : α) :
    star (amplifiedRoot Λ hΛ m t) * amplifiedRoot Λ hΛ m t = tensorOperator (Λ t) (1 : Coeff m) := by
  change star (tensorOperator _ _) * tensorOperator _ _ = _
  rw [← tensorOperator_star, ← tensorOperator_mul, star_one, one_mul,
    Compression.densityRoot_star_mul]

omit [SecondCountableTopology α] in
theorem amplifiedRoot_mass (Λ : C(α, Operator H)) (hΛ : ∀ t, 0 ≤ Λ t)
    (hmass : ∫ t, Λ t ∂μ = 1) (m : ℕ) :
    ∫ t, star (amplifiedRoot Λ hΛ m t) * amplifiedRoot Λ hΛ m t ∂μ = 1 := by
  simp only [amplifiedRoot_star_mul, ← tensorOperatorCLM_apply]
  rw [(tensorOperatorCLM (H := H) (1 : Coeff m)).integral_comp_comm,
    hmass, tensorOperatorCLM_apply, tensorOperator_one]
  exact Λ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [MeasurableSpace α] [BorelSpace α] [CompactSpace α] [SecondCountableTopology α] in
theorem amplifiedRoot_sandwich (Λ : C(α, Operator H)) (hΛ : ∀ t, 0 ≤ Λ t)
    {m : ℕ} (F : C(α, Coeff m)) (t : α) :
    star (amplifiedRoot Λ hΛ m t) * coefficientField (H := H) F t *
      amplifiedRoot Λ hΛ m t = tensorOperator (Λ t) (F t) := by
  change star (tensorOperator _ _) * tensorOperator _ _ * tensorOperator _ _ = _
  rw [← tensorOperator_star, ← tensorOperator_mul, ← tensorOperator_mul,
    star_one, one_mul, mul_one, mul_one, Compression.densityRoot_star_mul]

theorem norm_integral_tensor_density_le (Λ : C(α, Operator H)) (hΛ : ∀ t, 0 ≤ Λ t)
    (hmass : ∫ t, Λ t ∂μ = 1) {m : ℕ} (F : C(α, Coeff m))
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀ t, ‖F t‖ ≤ C) :
    ‖∫ t, tensorOperator (Λ t) (F t) ∂μ‖ ≤ C := by
  simp_rw [← amplifiedRoot_sandwich Λ hΛ F]
  apply Compression.norm_integral_le _ _ (amplifiedRoot_mass Λ hΛ hmass m) C hC
  intro t
  change ‖tensorOperator (1 : Operator H) (F t)‖ ≤ C
  calc
    ‖tensorOperator (1 : Operator H) (F t)‖ ≤ ‖(1 : Operator H)‖ * ‖F t‖ := norm_tensorOperator_le _ _
    _ ≤ 1 * ‖F t‖ := mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ ≤ C := by simpa only [one_mul] using hF t

end PositiveDensity

end CrouzeixHilbert

namespace CrouzeixHilbert.Disk

attribute [local instance] tensorDensityOperatorRealNormedSpace
attribute [local instance] tensorDensityOperatorCompleteSpace

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integral_matrixPolynomial (D : Operator H) (hD : spectralRadius ℂ D < 1)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    (∫ t : CircleSpace, tensorOperator (phi D t)
      (matrixPolynomial B (fourier 1 t)) ∂σ) = polynomialEval D B := by
  have he (t : CircleSpace) : tensorOperator (phi D t)
      (matrixPolynomial B (fourier 1 t)) =
        ∑ k : Fin (d + 1), tensorOperator (fourier (k : ℤ) t • phi D t) (B k) := by
    change tensorCoefficientCLM (phi D t) m (∑ k : Fin (d + 1), (fourier 1 t) ^ (k : ℕ) • B k) = _
    simp only [map_sum, map_smul, tensorCoefficientCLM_apply, ← tensorOperatorCLM_apply,
      map_smul, fourier_one_pow]
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    change (∫ t : CircleSpace, tensorOperatorCLM (B k)
      (fourier (k : ℤ) t • phi D t) ∂σ) = tensorOperator (D ^ (k : ℕ)) (B k)
    rw [(tensorOperatorCLM (H := H) (B k)).integral_comp_comm,
      integral_moment D hD]
    · rfl
    · exact ((fourier _).continuous.smul (continuous_phi D hD)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · intro k _
    exact ((tensorOperatorCLM (H := H) (B k)).continuous.comp
      ((fourier _).continuous.smul (continuous_phi D hD))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

theorem polynomial_bound_spectralRadius_lt_one (D : Operator H) (hN : ‖D‖ ≤ 1)
    (hD : spectralRadius ℂ D < 1) {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    ‖polynomialEval D B‖ ≤ supNorm (Metric.sphere (0 : ℂ) 1) (matrixPolynomial B) := by
  let Λ : C(CircleSpace, Operator H) := ⟨phi D, continuous_phi D hD⟩
  have hΛ : ∀ t, 0 ≤ Λ t := fun t =>
    ContinuousLinearMap.nonneg_iff_isPositive.mpr (phi_isPositive D hN hD t)
  let F : C(CircleSpace, Coeff m) :=
    ⟨fun t => matrixPolynomial B (fourier 1 t), (continuous_matrixPolynomial B).comp
      (fourier 1).continuous⟩
  have hb := supNorm_bddAbove (isCompact_sphere (0 : ℂ) 1)
    (continuous_matrixPolynomial B).continuousOn
  rw [← integral_matrixPolynomial D hD B]
  exact norm_integral_tensor_density_le Λ hΛ (integral_phi D hD) F _
    (supNorm_nonneg hb) (fun t => norm_le_supNorm hb (by
      simpa only [Metric.mem_sphere, dist_zero_right] using norm_fourier 1 t))

theorem continuous_polynomialEval {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    Continuous (fun D : Operator H => polynomialEval D B) := by
  apply continuous_finsetSum
  intro k _
  exact (tensorOperatorCLM (B k)).continuous.comp (continuous_id.pow (k : ℕ))

theorem radial_tendsto_polynomialEval (D : Operator H)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    Tendsto (fun r : ℝ => ‖polynomialEval ((r : ℂ) • D) B‖)
      (𝓝[<] (1 : ℝ)) (𝓝 ‖polynomialEval D B‖) := by
  have hr : Tendsto (fun r : ℝ => (r : ℂ) • D) (𝓝[<] (1 : ℝ)) (𝓝 D) := by
    have hc : Continuous (fun r : ℝ => (r : ℂ) • D) :=
      Complex.continuous_ofReal.smul continuous_const
    have ht := hc.tendsto (1 : ℝ)
    rw [Complex.ofReal_one, one_smul] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  exact ((continuous_polynomialEval (H := H) B).norm.tendsto D).comp hr

lemma spectralRadius_lt_one_of_norm_lt_one [Nontrivial H]
    (D : Operator H) (h : ‖D‖ < 1) : spectralRadius ℂ D < 1 := by
  apply (spectralRadius_le_nnnorm D).trans_lt
  exact_mod_cast h

theorem polynomial_bound_nontrivial [Nontrivial H] (D : Operator H) (hN : ‖D‖ ≤ 1)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    ‖polynomialEval D B‖ ≤ supNorm (Metric.sphere (0 : ℂ) 1) (matrixPolynomial B) := by
  apply le_of_tendsto (radial_tendsto_polynomialEval D B)
  have hp : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp, self_mem_nhdsWithin] with r hr0 hr1
  have hn : ‖(r : ℂ) • D‖ < 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact (mul_le_mul_of_nonneg_left hN hr0.le).trans_lt (by simpa using hr1)
  exact polynomial_bound_spectralRadius_lt_one _ hn.le
    (spectralRadius_lt_one_of_norm_lt_one _ hn) B

theorem polynomial_bound (D : Operator H) (hN : ‖D‖ ≤ 1)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    ‖polynomialEval D B‖ ≤ supNorm (Metric.sphere (0 : ℂ) 1) (matrixPolynomial B) := by
  rcases subsingleton_or_nontrivial H with h | h
  · have hb := supNorm_bddAbove (isCompact_sphere (0 : ℂ) 1)
      (continuous_matrixPolynomial B).continuousOn
    have he : polynomialEval D B = 0 := Subsingleton.elim _ _
    rw [he, norm_zero]
    exact supNorm_nonneg hb
  · exact polynomial_bound_nontrivial D hN B

end CrouzeixHilbert.Disk

end

end OAI
