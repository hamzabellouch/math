import Mathlib
import OAI.Analysis.Crouzeix.RationalEvaluation

namespace OAI

/-! Resolvent Bounds. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace Topology

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuousOn_resolvent [CompleteSpace H] (A : Operator H) :
    ContinuousOn (fun z : ℂ => Ring.inverse (algebraMap ℂ (Operator H) z - A))
      (numericalClosure A)ᶜ := by
  intro z hz
  have hr : z ∈ resolventSet ℂ A := by
    by_contra h
    exact hz (spectrum_subset_numericalClosure A h)
  exact (spectrum.hasDerivAt_resolvent_const_left hr).continuousAt.continuousWithinAt

def SmoothContour.trace (Γ : SmoothContour) : Set ℂ := Γ.path '' Icc (0 : ℝ) 1

theorem SmoothContour.isCompact_trace (Γ : SmoothContour) : IsCompact Γ.trace :=
  isCompact_Icc.image Γ.smooth.continuous

theorem SmoothContour.trace_nonempty (Γ : SmoothContour) : Γ.trace.Nonempty :=
  ⟨Γ.path 0, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩

def contourKernel (A : Operator H) (Γ : SmoothContour) (t : ℝ) : Operator H :=
  deriv Γ.path t • Ring.inverse (algebraMap ℂ (Operator H) (Γ.path t) - A)

theorem continuousOn_contourKernel [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) :
    ContinuousOn (contourKernel A Γ.toSmoothContour) (Icc (0 : ℝ) 1) := by
  apply Γ.smooth.continuous_deriv_one.continuousOn.smul
  exact (continuousOn_resolvent A).comp Γ.smooth.continuous.continuousOn
    (fun t ht => (Γ.avoids t ht).2)

theorem contourEval_eq_kernel (A : Operator H) (Γ : SmoothContour) (f : ℂ → ℂ) :
    contourEval A Γ f = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      ∫ t in (0 : ℝ)..1, f (Γ.path t) • contourKernel A Γ t := by
  unfold contourEval contourKernel
  simp only [smul_smul, mul_comm (f _)]

theorem intervalIntegrable_contourIntegrand [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace) :
    IntervalIntegrable (fun t => f (Γ.path t) • contourKernel A Γ.toSmoothContour t)
      MeasureTheory.volume (0 : ℝ) 1 := by
  have hfc : ContinuousOn (fun t => f (Γ.path t)) (Icc (0 : ℝ) 1) :=
    hf.comp Γ.smooth.continuous.continuousOn (fun t ht => mem_image_of_mem _ ht)
  have hcont := hfc.smul (continuousOn_contourKernel A Γ)
  rw [← uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hcont
  exact hcont.intervalIntegrable

theorem tendsto_contourEval [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {f : ℂ → ℂ} {fs : ℕ → ℂ → ℂ}
    (hc : ∀ n, ContinuousOn (fs n) Γ.toSmoothContour.trace)
    (hu : TendstoUniformlyOn fs f atTop Γ.toSmoothContour.trace) :
    Tendsto (fun n => contourEval A Γ.toSmoothContour (fs n)) atTop
      (𝓝 (contourEval A Γ.toSmoothContour f)) := by
  let k := contourKernel A Γ.toSmoothContour
  have hk : ContinuousOn k (Icc (0 : ℝ) 1) := continuousOn_contourKernel A Γ
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hk.norm
  let M := max C 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hkb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖k t‖ ≤ M :=
    (hC (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  have huc : TendstoUniformlyOn (fun n t => fs n (Γ.path t) • k t)
      (fun t => f (Γ.path t) • k t) atTop (Icc (0 : ℝ) 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (ε / M) (div_pos hε hM)]
      with n hn
    intro t ht
    have hn' := hn (Γ.path t) (mem_image_of_mem _ ht)
    calc
      dist (f (Γ.path t) • k t) (fs n (Γ.path t) • k t) =
          ‖f (Γ.path t) - fs n (Γ.path t)‖ * ‖k t‖ := by
            rw [dist_eq_norm, ← sub_smul, norm_smul]
      _ ≤ ‖f (Γ.path t) - fs n (Γ.path t)‖ * M :=
        mul_le_mul_of_nonneg_left (hkb t ht) (norm_nonneg _)
      _ < (ε / M) * M := mul_lt_mul_of_pos_right (by simpa only [dist_eq_norm] using hn') hM
      _ = ε := div_mul_cancel₀ _ hM.ne'
  have hcon (n : ℕ) : ContinuousOn (fun t => fs n (Γ.path t) • k t)
      (Icc (0 : ℝ) 1) :=
    ((hc n).comp Γ.smooth.continuous.continuousOn
      (fun t ht => mem_image_of_mem _ ht)).smul hk
  have hi : Tendsto (fun n => ∫ t in (0 : ℝ)..1, fs n (Γ.path t) • k t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f (Γ.path t) • k t)) := by
    apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    · exact Eventually.of_forall (fun n => by simpa only [uIcc_of_le zero_le_one] using hcon n)
    · simpa only [uIcc_of_le zero_le_one] using huc
  simpa only [contourEval_eq_kernel] using hi.const_smul ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)

theorem exists_contourEval_bound [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℂ → ℂ, ContinuousOn f Γ.toSmoothContour.trace →
      ‖contourEval A Γ.toSmoothContour f‖ ≤ C * supNorm Γ.toSmoothContour.trace f := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
    (continuousOn_contourKernel A Γ).norm
  let c := (2 * (Real.pi : ℂ) * Complex.I)⁻¹
  refine ⟨‖c‖ * max M 0, mul_nonneg (norm_nonneg _) (le_max_right _ _), ?_⟩
  intro f hf
  have hb := supNorm_bddAbove Γ.toSmoothContour.isCompact_trace hf
  have hbound : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖f (Γ.path t) • contourKernel A Γ.toSmoothContour t‖ ≤
        max M 0 * supNorm Γ.toSmoothContour.trace f := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using uIoc_subset_uIcc ht
    rw [norm_smul, mul_comm]
    exact mul_le_mul
      ((hM (mem_image_of_mem _ ht')).trans (le_max_left _ _))
      (norm_le_supNorm hb (mem_image_of_mem _ ht')) (norm_nonneg _) (le_max_right _ _)
  have hi : ‖∫ t in (0 : ℝ)..1, f (Γ.path t) • contourKernel A Γ.toSmoothContour t‖ ≤
      max M 0 * supNorm Γ.toSmoothContour.trace f := by
    simpa only [sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [contourEval_eq_kernel, norm_smul]
  exact (mul_le_mul_of_nonneg_left hi (norm_nonneg c)).trans_eq (mul_assoc _ _ _).symm

theorem contourEval_sub [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {f g : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace)
    (hg : ContinuousOn g Γ.toSmoothContour.trace) :
    contourEval A Γ.toSmoothContour (f - g) =
      contourEval A Γ.toSmoothContour f - contourEval A Γ.toSmoothContour g := by
  simp only [contourEval_eq_kernel, Pi.sub_apply, sub_smul]
  rw [intervalIntegral.integral_sub (intervalIntegrable_contourIntegrand A Γ hf)
    (intervalIntegrable_contourIntegrand A Γ hg), smul_sub]

def tensorOperatorCLM {m : ℕ} (B : Coeff m) :
    Operator H →L[ℂ] Operator (Amplification H m) := by
  let L : Operator H →ₗ[ℂ] Operator (Amplification H m) :=
    { toFun := fun A => tensorOperator A B
      map_add' := by
        intro A D
        apply ContinuousLinearMap.ext
        intro x
        refine UniformSpace.Completion.induction_on x
          (isClosed_eq (tensorOperator (A + D) B).continuous
            ((tensorOperator A B).continuous.add (tensorOperator D B).continuous)) ?_
        intro a
        simp only [tensorOperator, TensorProduct.mapL_add_left,
          ContinuousLinearMap.completion_apply_coe, add_apply,
          UniformSpace.Completion.coe_add]
      map_smul' := by
        intro c A
        apply ContinuousLinearMap.ext
        intro x
        refine UniformSpace.Completion.induction_on x
          (isClosed_eq (tensorOperator (c • A) B).continuous
            ((tensorOperator A B).continuous.const_smul c)) ?_
        intro a
        simp only [tensorOperator, TensorProduct.mapL_smul_left,
          ContinuousLinearMap.completion_apply_coe, smul_apply,
          UniformSpace.Completion.coe_smul, RingHom.id_apply] }
  exact L.mkContinuous ‖B‖ (fun A => (norm_tensorOperator_le A B).trans_eq (mul_comm _ _))

@[simp]
theorem tensorOperatorCLM_apply {m : ℕ} (A : Operator H) (B : Coeff m) :
    tensorOperatorCLM B A = tensorOperator A B := rfl

def matrixEntryCLM {m : ℕ} (i j : Fin m) : Coeff m →L[ℂ] ℂ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_apply j).comp (continuous_apply i)

def matrixContourEval (A : Operator H) {m : ℕ} (Γ : SmoothContour)
    (F : ℂ → Coeff m) : Operator (Amplification H m) :=
  ∑ i, ∑ j, tensorOperator (contourEval A Γ (fun z => F z i j)) (Matrix.single i j 1)

theorem tendsto_matrixContourEval [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {m : ℕ} {F : ℂ → Coeff m} {Fs : ℕ → ℂ → Coeff m}
    (hc : ∀ n, ContinuousOn (Fs n) Γ.toSmoothContour.trace)
    (hu : TendstoUniformlyOn Fs F atTop Γ.toSmoothContour.trace) :
    Tendsto (fun n => matrixContourEval A Γ.toSmoothContour (Fs n)) atTop
      (𝓝 (matrixContourEval A Γ.toSmoothContour F)) := by
  unfold matrixContourEval
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  have hsc : ∀ n, ContinuousOn (fun z => Fs n z i j) Γ.toSmoothContour.trace :=
    fun n => (matrixEntryCLM i j).continuous.comp_continuousOn (hc n)
  have hsu : TendstoUniformlyOn (fun n z => Fs n z i j) (fun z => F z i j)
      atTop Γ.toSmoothContour.trace :=
    (matrixEntryCLM i j).uniformContinuous.comp_tendstoUniformlyOn hu
  exact (tensorOperatorCLM (H := H) (Matrix.single i j 1)).continuous.continuousAt.tendsto.comp
    (tendsto_contourEval A Γ hsc hsu)

theorem supNorm_le_add_of_dist_le {E : Type*} [NormedAddCommGroup E]
    {S : Set ℂ} {F G : ℂ → E} {ε : ℝ} (hε : 0 ≤ ε)
    (hG : BddAbove (insert 0 ((fun z => ‖G z‖) '' S)))
    (hFG : ∀ z ∈ S, dist (F z) (G z) ≤ ε) :
    supNorm S F ≤ supNorm S G + ε := by
  apply supNorm_le (add_nonneg (supNorm_nonneg hG) hε)
  intro z hz
  have h₁ := norm_sub_norm_le (F z) (G z)
  have h₂ : ‖F z - G z‖ ≤ ε := by simpa only [dist_eq_norm] using hFG z hz
  have h₃ := norm_le_supNorm hG hz
  linarith

theorem abs_supNorm_sub_le_of_dist_le {E : Type*} [NormedAddCommGroup E]
    {S : Set ℂ} {F G : ℂ → E} {ε : ℝ} (hε : 0 ≤ ε)
    (hF : BddAbove (insert 0 ((fun z => ‖F z‖) '' S)))
    (hG : BddAbove (insert 0 ((fun z => ‖G z‖) '' S)))
    (hFG : ∀ z ∈ S, dist (F z) (G z) ≤ ε) :
    |supNorm S F - supNorm S G| ≤ ε := by
  have h₁ := supNorm_le_add_of_dist_le hε hG hFG
  have h₂ := supNorm_le_add_of_dist_le hε hF
    (fun z hz => (dist_comm (G z) (F z)).trans_le (hFG z hz))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem tendsto_supNorm_of_uniform {E : Type*} [NormedAddCommGroup E]
    {S : Set ℂ} (hS : IsCompact S) {F : ℂ → E} {Fs : ℕ → ℂ → E}
    (hc : ∀ n, ContinuousOn (Fs n) S) (hF : ContinuousOn F S)
    (hu : TendstoUniformlyOn Fs F atTop S) :
    Tendsto (fun n => supNorm S (Fs n)) atTop (𝓝 (supNorm S F)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (ε / 2) (half_pos hε)]
    with n hn
  have h := abs_supNorm_sub_le_of_dist_le (half_pos hε).le
    (supNorm_bddAbove hS (hc n)) (supNorm_bddAbove hS hF)
    (fun z hz => (dist_comm (Fs n z) (F z)).trans_le (hn z hz).le)
  have hd : dist (supNorm S (Fs n)) (supNorm S F) ≤ ε / 2 := by
    simpa only [Real.dist_eq] using h
  exact hd.trans_lt (by linarith)

theorem contour_bound_of_polynomial_approximation [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {m : ℕ}
    (F : ℂ → Coeff m)
    (hF : ContinuousOn F (numericalClosure A))
    (hpoly : ∀ (d : ℕ) (B : Fin (d + 1) → Coeff m),
      ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B))
    (hcalc : ∀ (d : ℕ) (B : Fin (d + 1) → Coeff m),
      matrixContourEval A Γ.toSmoothContour (matrixPolynomial B) = polynomialEval A B)
    (degrees : ℕ → ℕ) (B : (n : ℕ) → Fin (degrees n + 1) → Coeff m)
    (happrox : TendstoUniformlyOn (fun n => matrixPolynomial (B n)) F atTop
      (numericalClosure A ∪ Γ.toSmoothContour.trace)) :
    ‖matrixContourEval A Γ.toSmoothContour F‖ ≤ 2 * supNorm (numericalClosure A) F := by
  have hev := tendsto_matrixContourEval A Γ
    (fun n => (continuous_matrixPolynomial (B n)).continuousOn)
    (happrox.mono subset_union_right)
  have hmax := tendsto_supNorm_of_uniform (isCompact_numericalClosure A)
    (fun n => (continuous_matrixPolynomial (B n)).continuousOn) hF
    (happrox.mono subset_union_left)
  have htwo : Tendsto (fun n => 2 * supNorm (numericalClosure A) (matrixPolynomial (B n)))
      atTop (𝓝 (2 * supNorm (numericalClosure A) F)) := tendsto_const_nhds.mul hmax
  apply le_of_tendsto_of_tendsto hev.norm htwo
  filter_upwards [] with n
  rw [hcalc]
  have heq : supNorm (numericalRange A) (matrixPolynomial (B n)) =
      supNorm (numericalClosure A) (matrixPolynomial (B n)) :=
    supNorm_closure (isCompact_numericalClosure A) (continuous_matrixPolynomial (B n)).continuousOn
  rw [← heq]
  exact hpoly _ _

theorem norm_inverse_le_of_inner_lower_bound [CompleteSpace H] (T : Operator H)
    {δ : ℝ} (hδ : 0 < δ) (hb : ∀ x : H, ‖x‖ = 1 → δ ≤ ‖⟪x, T x⟫_ℂ‖) :
    ‖Ring.inverse T‖ ≤ δ⁻¹ := by
  have hu := isUnit_of_inner_lower_bound T hδ hb
  apply (Ring.inverse T).opNorm_le_bound (inv_nonneg.mpr hδ.le)
  intro x
  have hl := operator_lower_bound_of_inner T hb ((Ring.inverse T) x)
  have he : T ((Ring.inverse T) x) = x := by
    change (T * Ring.inverse T) x = x
    rw [Ring.mul_inverse_cancel T hu]
    rfl
  rw [he] at hl
  have hh := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hδ.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul] using hh

theorem norm_resolvent_le_inv_infDist [CompleteSpace H] [Nontrivial H]
    (A : Operator H) {z : ℂ} (hz : z ∉ numericalClosure A) :
    ‖Ring.inverse (algebraMap ℂ (Operator H) z - A)‖ ≤
      (Metric.infDist z (numericalClosure A))⁻¹ := by
  have hδ : 0 < Metric.infDist z (numericalClosure A) :=
    IsClosed.notMem_iff_infDist_pos isClosed_closure (numericalClosure_nonempty A) |>.mp hz
  apply norm_inverse_le_of_inner_lower_bound _ hδ
  intro x hx
  have he : ⟪x, (algebraMap ℂ (Operator H) z - A) x⟫_ℂ = z - ⟪x, A x⟫_ℂ := by
    simp [ContinuousLinearMap.algebraMap_apply, inner_self_eq_norm_sq_to_K, hx]
  rw [he]
  simpa only [dist_eq_norm, numericalClosure] using
    Metric.infDist_le_dist_of_mem (x := z) (subset_closure (show ⟪x, A x⟫_ℂ ∈ numericalRange A from
      ⟨x, hx, rfl⟩))

end CrouzeixHilbert

end

end OAI
