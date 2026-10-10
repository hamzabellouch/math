import Mathlib

namespace OAI

open Matrix Polynomial

open scoped Topology

namespace TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def asMatrix (A : (V → ℝ) →L[ℝ] (V → ℝ)) : Matrix V V ℝ :=
  LinearMap.toMatrix' A.toLinearMap

@[simp] lemma asMatrix_apply (A : (V → ℝ) →L[ℝ] (V → ℝ)) (i j : V) :
    asMatrix A i j = A (Pi.single j 1) i := rfl

@[simp] lemma asMatrix_one : asMatrix (1 : (V → ℝ) →L[ℝ] (V → ℝ)) = 1 :=
  LinearMap.toMatrix'_one

@[simp] lemma asMatrix_add (A B : (V → ℝ) →L[ℝ] (V → ℝ)) :
    asMatrix (A + B) = asMatrix A + asMatrix B := by simp [asMatrix, map_add]

@[simp] lemma asMatrix_sub (A B : (V → ℝ) →L[ℝ] (V → ℝ)) :
    asMatrix (A - B) = asMatrix A - asMatrix B := by simp [asMatrix, map_sub]

@[simp] lemma asMatrix_smul (t : ℝ) (A : (V → ℝ) →L[ℝ] (V → ℝ)) :
    asMatrix (t • A) = t • asMatrix A := by simp [asMatrix, map_smul]

@[simp] lemma asMatrix_mul (A B : (V → ℝ) →L[ℝ] (V → ℝ)) :
    asMatrix (A * B) = asMatrix A * asMatrix B :=
  LinearMap.toMatrix'_mul _ _

lemma asMatrix_det (A : (V → ℝ) →L[ℝ] (V → ℝ)) : (asMatrix A).det = A.det :=
  LinearMap.det_toMatrix' _

noncomputable def detPoly (A : (V → ℝ) →L[ℝ] (V → ℝ)) : Polynomial ℝ :=
  Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • (asMatrix A).map Polynomial.C)

lemma detPoly_eval (A : (V → ℝ) →L[ℝ] (V → ℝ)) (t : ℝ) :
    (detPoly A).eval t = (1 + t • A).det := by
  rw [← asMatrix_det, asMatrix_add, asMatrix_one, asMatrix_smul]
  rw [detPoly, Polynomial.eval, ← Polynomial.coe_eval₂RingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp <;> ring

lemma detPoly_coeff_one (A : (V → ℝ) →L[ℝ] (V → ℝ)) :
    (detPoly A).coeff 1 = (asMatrix A).trace :=
  Matrix.coeff_det_one_add_X_smul_one _

lemma det_line_deriv_zero (A : (V → ℝ) →L[ℝ] (V → ℝ)) :
    HasDerivAt (fun t : ℝ => (1 + t • A).det) (asMatrix A).trace 0 := by
  have hd := (detPoly A).hasDerivAt 0
  have he : ((detPoly A).derivative).eval 0 = (asMatrix A).trace := by
    simpa [detPoly] using Matrix.derivative_det_one_add_X_smul (asMatrix A)
  simpa only [detPoly_eval, he] using hd

lemma det_add_line_deriv_zero (B A : (V → ℝ) →L[ℝ] (V → ℝ)) (hB : IsUnit B) :
    HasDerivAt (fun t : ℝ => (B + t • A).det)
      (B.det * (asMatrix (Ring.inverse B * A)).trace) 0 := by
  have he (t : ℝ) : B + t • A = B * (1 + t • (Ring.inverse B * A)) := by
    rw [mul_add, mul_one, mul_smul_comm, ← mul_assoc, Ring.mul_inverse_cancel B hB, one_mul]
  have hd := (det_line_deriv_zero (Ring.inverse B * A)).const_mul B.det
  convert hd using 1
  funext t
  rw [he]
  simp [ContinuousLinearMap.det, map_mul]

lemma det_line_deriv (A : (V → ℝ) →L[ℝ] (V → ℝ)) (t : ℝ)
    (hB : IsUnit (1 + t • A)) :
    HasDerivAt (fun r : ℝ => (1 + r • A).det)
      ((1 + t • A).det * (asMatrix (Ring.inverse (1 + t • A) * A)).trace) t := by
  have hd := det_add_line_deriv_zero (1 + t • A) A hB
  have hd' := HasDerivAt.comp_sub_const t t (by simpa only [sub_self] using hd)
  convert hd' using 1
  funext r
  congr 1
  module

noncomputable def traceCLM : ((V → ℝ) →L[ℝ] (V → ℝ)) →L[ℝ] ℝ :=
  ∑ i : V, (ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.apply ℝ (V → ℝ) (Pi.single i 1))

@[simp] lemma traceCLM_apply (A : (V → ℝ) →L[ℝ] (V → ℝ)) :
    traceCLM A = (asMatrix A).trace := by
  simp [traceCLM, Matrix.trace, Matrix.diag]

lemma asMatrix_neg (A : (V → ℝ) →L[ℝ] (V → ℝ)) :
    asMatrix (-A) = -asMatrix A := by ext; simp [asMatrix]

omit [DecidableEq V] in
lemma inverse_line_deriv_zero (A : (V → ℝ) →L[ℝ] (V → ℝ)) :
    HasDerivAt (fun t : ℝ => Ring.inverse (1 + t • A)) (-A) 0 := by
  have hline : HasDerivAt (fun t : ℝ => (1 : (V → ℝ) →L[ℝ] (V → ℝ)) + t • A) A 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : (V → ℝ) →L[ℝ] (V → ℝ))).add
      ((hasDerivAt_id (0 : ℝ)).smul_const A) using 1 <;> try rfl
    simp only [zero_add, one_smul]
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : ((V → ℝ) →L[ℝ] (V → ℝ))ˣ)
  have hh := (by simpa only [inv_one, Units.val_one, zero_smul, add_zero] using hi : HasFDerivAt Ring.inverse
    (-ContinuousLinearMap.mulLeftRight ℝ ((V → ℝ) →L[ℝ] (V → ℝ)) 1 1) (1 + (0 : ℝ) • A))
  convert hh.comp_hasDerivAt 0 hline using 1 <;> try rfl

lemma trace_inverse_line_deriv_zero (A : (V → ℝ) →L[ℝ] (V → ℝ)) :
    HasDerivAt (fun t : ℝ => (asMatrix (Ring.inverse (1 + t • A) * A)).trace)
      (-(asMatrix (A * A)).trace) 0 := by
  have hh := (traceCLM (V := V)).hasFDerivAt.comp_hasDerivAt 0
    ((inverse_line_deriv_zero A).mul_const A)
  convert hh using 1 <;> try rfl
  · funext t; exact (traceCLM_apply _).symm
  · simp [neg_mul, asMatrix_neg]

lemma detPoly_second_derivative (A : (V → ℝ) →L[ℝ] (V → ℝ)) :
    (detPoly A).derivative.derivative.eval 0 =
      (asMatrix A).trace ^ 2 - (asMatrix (A * A)).trace := by
  have hline : Continuous (fun t : ℝ => (1 : (V → ℝ) →L[ℝ] (V → ℝ)) + t • A) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hunit : ∀ᶠ t : ℝ in nhds 0, IsUnit (1 + t • A) := by
    have hh := hline.continuousAt.preimage_mem_nhds
      (Units.isOpen.mem_nhds (show IsUnit (1 + (0 : ℝ) • A) by simp))
    exact hh
  have he : (fun t : ℝ => (detPoly A).derivative.eval t) =ᶠ[nhds 0]
      (fun t => (1 + t • A).det * (asMatrix (Ring.inverse (1 + t • A) * A)).trace) := by
    filter_upwards [hunit] with t ht
    exact ((by simpa only [detPoly_eval] using (detPoly A).hasDerivAt t :
      HasDerivAt (fun r : ℝ => (1 + r • A).det) ((detPoly A).derivative.eval t) t).unique
      (det_line_deriv A t ht))
  have hd := (det_line_deriv_zero A).mul (trace_inverse_line_deriv_zero A)
  have hd' := hd.congr_of_eventuallyEq he
  have hp := (detPoly A).derivative.hasDerivAt 0
  convert hp.unique hd' using 1
  simp [ContinuousLinearMap.det, Ring.inverse_one]
  ring

lemma detPoly_coeff_two (A : (V → ℝ) →L[ℝ] (V → ℝ)) :
    (detPoly A).coeff 2 = ((asMatrix A).trace ^ 2 - (asMatrix (A * A)).trace) / 2 := by
  have hh := detPoly_second_derivative A
  simp only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative] at hh
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, mul_one] at hh
  linarith

lemma continuous_asMatrix_entry (i j : V) :
    Continuous (fun A : (V → ℝ) →L[ℝ] (V → ℝ) => asMatrix A i j) :=
  (continuous_apply i).comp (ContinuousLinearMap.apply ℝ (V → ℝ) (Pi.single j 1)).continuous

lemma detPoly_coeff_continuous (k : ℕ) :
    Continuous (fun A : (V → ℝ) →L[ℝ] (V → ℝ) => (detPoly A).coeff k) := by
  simp_rw [detPoly, Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  apply continuous_finsetSum
  intro s hs
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_asMatrix_entry (V := V) i.val j.val

lemma detPoly_degree_le (A : (V → ℝ) →L[ℝ] (V → ℝ)) :
    (detPoly A).natDegree ≤ Fintype.card V := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [detPoly, Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  have he : (Finset.univ : Finset V).powersetCard k = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simpa using hk)
  rw [he, Finset.sum_empty]

open MeasureTheory

lemma detPoly_eval_sum (A : (V → ℝ) →L[ℝ] (V → ℝ)) (t : ℝ) :
    (1 + t • A).det = ∑ k ∈ Finset.range (Fintype.card V + 3),
      (detPoly A).coeff k * t ^ k := by
  have he := congrArg (fun p : Polynomial ℝ => p.eval t)
    ((detPoly A).as_sum_range_C_mul_X_pow' (show (detPoly A).natDegree < Fintype.card V + 3 by
      have := detPoly_degree_le A; omega))
  simpa only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, detPoly_eval] using he

omit [DecidableEq V] in
lemma continuous_integrable_of_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (B : Ω → (V → ℝ) →L[ℝ] (V → ℝ)) (hB : Measurable B)
    (K : ℝ) (hK : ∀ x, ‖B x‖ ≤ K)
    (F : ((V → ℝ) →L[ℝ] (V → ℝ)) → ℝ) (hF : Continuous F) :
    Integrable (fun x => F (B x)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : (V → ℝ) →L[ℝ] (V → ℝ)) K).exists_bound_of_continuousOn hF.continuousOn
  apply Integrable.of_bound (hF.measurable.comp hB).aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun x => hC (B x) (by simpa using hK x)

lemma detPoly_coeff_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (B : Ω → (V → ℝ) →L[ℝ] (V → ℝ)) (hB : Measurable B)
    (K : ℝ) (hK : ∀ x, ‖B x‖ ≤ K) (k : ℕ) :
    Integrable (fun x => (detPoly (B x)).coeff k) μ := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : (V → ℝ) →L[ℝ] (V → ℝ)) K).exists_bound_of_continuousOn (detPoly_coeff_continuous (V := V) k).continuousOn
  apply Integrable.of_bound ((detPoly_coeff_continuous (V := V) k).measurable.comp hB).aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun x => hC (B x) (by simpa using hK x)

noncomputable def integratedDetPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : Ω → (V → ℝ) →L[ℝ] (V → ℝ)) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (Fintype.card V + 3),
    Polynomial.C (∫ x, (detPoly (B x)).coeff k ∂μ) * Polynomial.X ^ k

lemma integratedDetPoly_coeff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : Ω → (V → ℝ) →L[ℝ] (V → ℝ)) (k : ℕ) (hk : k < Fintype.card V + 3) :
    (integratedDetPoly μ B).coeff k = ∫ x, (detPoly (B x)).coeff k ∂μ := by
  simp [integratedDetPoly, Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.coeff_monomial, Finset.mem_range.mpr hk]

lemma integratedDetPoly_eval {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (B : Ω → (V → ℝ) →L[ℝ] (V → ℝ)) (hB : Measurable B)
    (K : ℝ) (hK : ∀ x, ‖B x‖ ≤ K) (t : ℝ) :
    (integratedDetPoly μ B).eval t = ∫ x, (1 + t • B x).det ∂μ := by
  simp_rw [detPoly_eval_sum]
  rw [integral_finsetSum _ (fun k _ => (detPoly_coeff_integrable μ B hB K hK k).mul_const _)]
  simp only [integratedDetPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, integral_mul_const]

lemma integratedDetPoly_eq_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (B : Ω → (V → ℝ) →L[ℝ] (V → ℝ)) (hB : Measurable B)
    (K : ℝ) (hK : ∀ x, ‖B x‖ ≤ K) (δ : ℝ) (hδ : 0 < δ)
    (hid : ∀ t ∈ Set.Ioo (-δ) δ, ∫ x, (1 + t • B x).det ∂μ = (μ Set.univ).toReal) :
    integratedDetPoly μ B = Polynomial.C (μ Set.univ).toReal := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioo_infinite (show -δ < δ by linarith)).mono
  intro t ht
  rw [Set.mem_ofPred_eq, integratedDetPoly_eval μ B hB K hK, Polynomial.eval_C]
  exact hid t ht

lemma trace_integral_zero_of_det_identity {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (B : Ω → (V → ℝ) →L[ℝ] (V → ℝ)) (hB : Measurable B)
    (K : ℝ) (hK : ∀ x, ‖B x‖ ≤ K) (δ : ℝ) (hδ : 0 < δ)
    (hid : ∀ t ∈ Set.Ioo (-δ) δ, ∫ x, (1 + t • B x).det ∂μ = (μ Set.univ).toReal) :
    ∫ x, (asMatrix (B x)).trace ∂μ = 0 := by
  have hh := congrArg (fun p : Polynomial ℝ => p.coeff 1)
    (integratedDetPoly_eq_const μ B hB K hK δ hδ hid)
  simpa only [integratedDetPoly_coeff μ B 1 (by omega), detPoly_coeff_one,
    Polynomial.coeff_C_succ] using hh

lemma trace_square_integral_of_det_identity {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (B : Ω → (V → ℝ) →L[ℝ] (V → ℝ)) (hB : Measurable B)
    (K : ℝ) (hK : ∀ x, ‖B x‖ ≤ K) (δ : ℝ) (hδ : 0 < δ)
    (hid : ∀ t ∈ Set.Ioo (-δ) δ, ∫ x, (1 + t • B x).det ∂μ = (μ Set.univ).toReal) :
    ∫ x, (asMatrix (B x)).trace ^ 2 ∂μ = ∫ x, (asMatrix (B x * B x)).trace ∂μ := by
  have hh := congrArg (fun p : Polynomial ℝ => p.coeff 2)
    (integratedDetPoly_eq_const μ B hB K hK δ hδ hid)
  simp only [integratedDetPoly_coeff μ B 2 (by omega), detPoly_coeff_two,
    Polynomial.coeff_C_succ] at hh
  have hcont : Continuous (fun A : (V → ℝ) →L[ℝ] (V → ℝ) => (asMatrix A).trace) := by
    simp_rw [← traceCLM_apply]
    exact (traceCLM (V := V)).continuous
  have hI1 : Integrable (fun x => (asMatrix (B x)).trace ^ 2) μ :=
    continuous_integrable_of_bounded μ B hB K hK (fun A => (asMatrix A).trace ^ 2) (hcont.pow 2)
  have hI2 : Integrable (fun x => (asMatrix (B x * B x)).trace) μ :=
    continuous_integrable_of_bounded μ B hB K hK (fun A => (asMatrix (A * A)).trace)
      (hcont.comp (continuous_id.mul continuous_id))
  rw [integral_div, integral_sub hI1 hI2] at hh
  linarith

end TangentialJacobian

end OAI
