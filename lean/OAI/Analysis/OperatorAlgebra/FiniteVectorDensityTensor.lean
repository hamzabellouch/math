import OAI.Analysis.OperatorAlgebra.ReducedDensityPredual
import OAI.Analysis.OperatorAlgebra.HypertraceFiniteDensity

namespace OAI

/-! The finite positive functionals obtained by separation have explicit
tensor-vector and positive Hilbert–Schmidt square-root realizations. -/

noncomputable section
open scoped InnerProductSpace TensorProduct ComplexOrder

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n : ℕ}

def finiteVectorDensityTensor (w : Fin n → ℝ) (x : Fin n → H) :
    EuclideanSpace ℂ (Fin n) ⊗[ℂ] H :=
  ∑ k, (EuclideanSpace.basisFun (Fin n) ℂ k) ⊗ₜ[ℂ] ((Real.sqrt (w k) : ℂ) • x k)

omit [CompleteSpace H] in
lemma finiteVectorDensityTensor_functional (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k)
    (x : Fin n → H) :
    finiteTensorDensity (finiteVectorDensityTensor w x) = finiteVectorDensity w x := by
  apply Subtype.ext
  ext T
  rw [finiteTensorDensity_apply]
  simp only [finiteVectorDensityTensor, map_sum, TensorProduct.mapL_tmul,
    ContinuousLinearMap.id_apply, sum_inner (𝕜 := ℂ), inner_sum (𝕜 := ℂ), TensorProduct.inner_tmul,
    (EuclideanSpace.basisFun (Fin n) ℂ).inner_eq_ite]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  change (∑ k, inner ℂ ((Real.sqrt (w k) : ℂ) • x k)
      (T ((Real.sqrt (w k) : ℂ) • x k))) = _
  simp only [map_smul, inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ),
    finiteVectorDensity, Submodule.coe_sum, Submodule.coe_smul, sum_apply, smul_apply]
  apply Finset.sum_congr rfl
  intro k _
  change star (Real.sqrt (w k) : ℂ) * ((Real.sqrt (w k) : ℂ) * inner ℂ (x k) (T (x k))) =
    (w k : ℂ) * inner ℂ (x k) (T (x k))
  rw [Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (hw k)]

omit [CompleteSpace H] in
lemma finiteVectorDensityTensor_norm_sq (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k)
    (x : Fin n → H) :
    ‖finiteVectorDensityTensor w x‖ ^ 2 = ∑ k, w k * ‖x k‖ ^ 2 := by
  have he := congrArg (fun ψ : finiteOperatorPredual (H := H) => (ψ.val 1).re)
    (finiteVectorDensityTensor_functional w hw x)
  rw [finiteTensorDensity_apply] at he
  change (inner ℂ (finiteVectorDensityTensor w x)
    (TensorProduct.mapL (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n)))
      (ContinuousLinearMap.id ℂ H) (finiteVectorDensityTensor w x))).re = _ at he
  rw [TensorProduct.mapL_id_id, ContinuousLinearMap.id_apply] at he
  have hn := inner_self_eq_norm_sq (𝕜 := ℂ) (finiteVectorDensityTensor w x)
  change (inner ℂ (finiteVectorDensityTensor w x) (finiteVectorDensityTensor w x)).re =
    ‖finiteVectorDensityTensor w x‖ ^ 2 at hn
  rw [hn] at he
  simpa [finiteVectorDensity, Submodule.coe_sum, Submodule.coe_smul, finiteOperatorCoefficient,
    operatorCoefficient_apply, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.mul_re] using he

omit [CompleteSpace H] in
lemma finiteVectorDensityTensor_norm_le_one (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hws : ∑ k, w k = 1) (x : Fin n → H) (hx : ∀ k, ‖x k‖ ≤ 1) :
    ‖finiteVectorDensityTensor w x‖ ≤ 1 := by
  have he : ‖finiteVectorDensityTensor w x‖ ^ 2 ≤ 1 := by
    rw [finiteVectorDensityTensor_norm_sq w hw x, ← hws]
    apply Finset.sum_le_sum
    intro k _
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) (hx k)) (hw k)).trans_eq
      (mul_one _)
  nlinarith [norm_nonneg (finiteVectorDensityTensor w x)]

/-- The hypertrace construction's norm-central finite functional yields an
actual positive finite-rank density root with the same centrality bound. -/
theorem finiteVectorDensity_root_central (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k)
    (x : Fin n → H) (U : H ≃ₗᵢ[ℂ] H) :
    ‖NuclearUltrapower.hsConjugation U
        (NuclearUltrapower.densityRoot (finiteVectorDensityTensor w x)) -
      NuclearUltrapower.densityRoot (finiteVectorDensityTensor w x)‖ ^ 2 ≤
      ‖finitePredualUnitary U (finiteVectorDensity w x) - finiteVectorDensity w x‖ := by
  simpa only [finiteVectorDensityTensor_functional w hw x] using
    densityRoot_unitary_predual_bound U (finiteVectorDensityTensor w x)

end WeakPureInfiniteness

end

end OAI
