import OAI.Analysis.LiebThirring.ActionPenalty

namespace OAI

universe u36

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u36} [Fintype n] [DecidableEq n]

omit [Fintype n] in
lemma quadraticMatrix_diagonal (c b : n → ℝ) (s : ℝ) :
    quadraticMatrix (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) s =
      diagonal (fun i ↦ (((s - b i) ^ 2 + (c i - b i ^ 2) : ℝ) : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [quadraticMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      diagonal_apply_eq, one_apply_eq, Complex.real_smul]
    push_cast
    ring
  · simp [quadraticMatrix, hij]

lemma fieldIntegrand_diagonal {δ : ℝ} (hδ : 0 < δ) (σ : ℝ) (c b : n → ℝ) (s : ℝ) :
    fieldIntegrand σ δ (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) s =
      diagonal (fun i ↦ ((regularizedPrimitive σ δ ((s - b i) ^ 2 + (c i - b i ^ 2)) -
        regularizedPrimitive σ δ (s ^ 2) : ℝ) : ℂ)) := by
  rw [fieldIntegrand, quadraticMatrix_diagonal,
    cfc_diagonal_real _ _ (primitive_differentiable σ hδ).continuous]
  ext i j
  by_cases hij : i = j <;> simp [hij, Complex.real_smul]

lemma hermitianField_diagonal {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (c b : n → ℝ) :
    hermitianField σ δ (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) =
      diagonal (fun i ↦ (scalarMu σ δ (c i - b i ^ 2) : ℂ)) := by
  have hC : (diagonal (fun i ↦ (c i : ℂ))).IsHermitian := isHermitian_diagonal_iff.2 (fun i ↦ by simp [IsSelfAdjoint])
  have hB : (diagonal (fun i ↦ (b i : ℂ))).IsHermitian := isHermitian_diagonal_iff.2 (fun i ↦ by simp [IsSelfAdjoint])
  apply tendsto_nhds_unique (hermitianField_cutoff_limit hσ hδ hC hB)
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  have hc := continuous_fieldIntegrand hδ σ hC hB
  have he (R : ℝ) := (entryCLM i j).intervalIntegral_comp_comm (μ := volume)
    (hc.intervalIntegrable (-R) R)
  simp only [entryCLM_apply] at he
  have he' (R : ℝ) :
      (fieldNormalization σ • ∫ s in -R..R, fieldIntegrand σ δ
        (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) s) i j =
      fieldNormalization σ • ∫ s in -R..R, fieldIntegrand σ δ
        (diagonal (fun i ↦ (c i : ℂ))) (diagonal (fun i ↦ (b i : ℂ))) s i j := by
    simp only [Matrix.smul_apply]
    rw [← he R]
  suffices ht : Tendsto (fun R : ℝ ↦ fieldNormalization σ • ∫ s in -R..R,
      fieldIntegrand σ δ (diagonal (fun i ↦ (c i : ℂ)))
        (diagonal (fun i ↦ (b i : ℂ))) s i j) atTop
      (𝓝 ((diagonal (fun i ↦ (scalarMu σ δ (c i - b i ^ 2) : ℂ))) i j)) by
    apply ht.congr
    intro R
    exact (he' R).symm
  simp only [fieldIntegrand_diagonal hδ]
  by_cases hij : i = j
  · subst j
    simp only [diagonal_apply_eq]
    have hs := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (primitive_shift_limit hσ hδ (c i - b i ^ 2) (b i))
    convert! hs using 1
    funext R
    rw [intervalIntegral.integral_ofReal]
    simp [Complex.real_smul]
  · simp only [diagonal_apply_ne _ hij, intervalIntegral.integral_zero, smul_zero]
    exact tendsto_const_nhds

lemma matrixField_diagonal {N : ℕ} {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k b : Fin N → ℝ) :
    matrixField σ δ k (diagonal b) = diagonal (fun i ↦ scalarMu σ δ (k i ^ 2 - b i ^ 2)) := by
  rw [matrixField_eq_realPart hσ hδ k (isHermitian_diagonal b),
    complexify_diagonal, complexify_diagonal, hermitianField_diagonal hσ hδ]
  ext i j
  by_cases hij : i = j <;> simp [realPartCLM, hij]

lemma continuous_scalarMu {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) :
    Continuous (scalarMu σ δ) :=
  continuous_iff_continuousAt.mpr (fun _ ↦ (mu_hasDerivAt_integral hσ hδ _).continuousAt)

lemma fieldPrimitive_diagonal {N : ℕ} {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k b : Fin N → ℝ) :
    fieldPrimitive σ δ k (diagonal b) =
      -(∑ i, ∫ s in (0 : ℝ)..b i, scalarMu σ δ (k i ^ 2 - s ^ 2)) := by
  have hc := continuous_scalarMu hσ hδ
  have he (t : ℝ) : trace (diagonal b * matrixField σ δ k (t • diagonal b)) =
      ∑ i, b i * scalarMu σ δ (k i ^ 2 - (t * b i) ^ 2) := by
    rw [← diagonal_smul, matrixField_diagonal hσ hδ]
    simp [trace, diag]
  unfold fieldPrimitive
  simp_rw [he]
  congr 1
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul]
    exact_mod_cast (by simpa using (intervalIntegral.smul_integral_comp_mul_right
      (fun s : ℝ ↦ scalarMu σ δ (k i ^ 2 - s ^ 2)) (a := 0) (b := 1) (b i)))
  · intro i _
    exact (by fun_prop : Continuous (fun t : ℝ ↦ b i * scalarMu σ δ (k i ^ 2 - (t * b i) ^ 2))).intervalIntegrable _ _

lemma fieldPrimitive_endpoint_jump {N : ℕ} {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) :
    fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k) =
      ∑ i, ∫ s in -(k i)..k i, scalarMu σ δ (k i ^ 2 - s ^ 2) := by
  rw [diagonal_neg, fieldPrimitive_diagonal hσ hδ, fieldPrimitive_diagonal hσ hδ]
  rw [neg_sub_neg, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hc : Continuous (fun s : ℝ ↦ scalarMu σ δ (k i ^ 2 - s ^ 2)) := by
    have := continuous_scalarMu hσ hδ
    fun_prop
  rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator Topology

lemma scalar_boundary_regularized {σ δ k : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (hk : 0 ≤ k) :
    (∫ s in -k..k, scalarMu σ δ (k ^ 2 - s ^ 2)) =
      ∫ s in -k..k, (k ^ 2 - s ^ 2 + δ) ^ σ - δ ^ σ := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le (by linarith : -k ≤ k)] at hs
  exact mu_eq_nonneg hσ hδ (by nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (show 0 ≤ k + s by linarith [hs.1])])

lemma scalar_boundary_limit {σ k : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hk : 0 ≤ k) :
    Tendsto (fun δ : ℝ ↦ ∫ s in -k..k, scalarMu σ δ (k ^ 2 - s ^ 2))
      (𝓝[>] 0) (𝓝 (∫ s in -k..k, (k ^ 2 - s ^ 2) ^ σ)) := by
  have hc : Continuous (fun δ : ℝ ↦ ∫ s in -k..k, (k ^ 2 - s ^ 2 + δ) ^ σ - δ ^ σ) := by
    simp_rw [intervalIntegral.integral_of_le (by linarith : -k ≤ k), ← integral_Icc_eq_integral_Ioc]
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact ((Real.continuous_rpow_const hσ₀.le).comp (by fun_prop)).sub
      ((Real.continuous_rpow_const hσ₀.le).comp (by fun_prop))
  have ht := (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [add_zero, Real.zero_rpow hσ₀.ne', sub_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (scalar_boundary_regularized hσ₁ hδ hk).symm

lemma fieldPrimitive_endpoint_limit {N : ℕ} {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (k : Fin N → ℝ) (hk : ∀ i, 0 ≤ k i) :
    Tendsto (fun δ : ℝ ↦ fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k))
      (𝓝[>] 0) (𝓝 (∑ i, ∫ s in -(k i)..k i, (k i ^ 2 - s ^ 2) ^ σ)) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ ↦ scalar_boundary_limit hσ₀ hσ₁ (hk i))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (fieldPrimitive_endpoint_jump hσ₁ hδ k).symm

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

local instance : SeminormedAddCommGroup (selfAdjoint (Matrix (Fin N) (Fin N) ℂ)) :=
  (inferInstance : NormedAddCommGroup (selfAdjoint (Matrix (Fin N) (Fin N) ℂ))).toSeminormedAddCommGroup
local instance : NormedSpace ℝ (selfAdjoint (Matrix (Fin N) (Fin N) ℂ)) := inferInstance

@[simp] lemma realHermitianComplexify_smul (t : ℝ)
    (B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) :
    realHermitianComplexify (t • B) = t • realHermitianComplexify B := by
  apply Subtype.ext
  exact map_smul complexify t (B : Matrix (Fin N) (Fin N) ℝ)

def realHermitianComplexifyCLM :
    selfAdjoint (Matrix (Fin N) (Fin N) ℝ) →L[ℝ] selfAdjoint (Matrix (Fin N) (Fin N) ℂ) :=
  { toFun := realHermitianComplexify
    map_add' := by
      intro A B
      apply Subtype.ext
      exact map_add complexify (A : Matrix (Fin N) (Fin N) ℝ) (B : Matrix (Fin N) (Fin N) ℝ)
    map_smul' := realHermitianComplexify_smul
    cont := realHermitianComplexify_continuous }

@[simp] lemma realHermitianComplexifyCLM_apply (B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) :
    realHermitianComplexifyCLM B = realHermitianComplexify B := rfl

def realK2SelfAdjoint (k : Fin N → ℝ) : selfAdjoint (Matrix (Fin N) (Fin N) ℂ) :=
  ⟨complexify (diagonal (fun i ↦ k i ^ 2)), complexify_hermitian (isHermitian_diagonal _)⟩

lemma fieldPrimitive_eq_hermitianPotential {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) (B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) :
    fieldPrimitive σ δ k B =
      -hermitianPotential σ δ (realK2SelfAdjoint k) (realHermitianComplexify B) := by
  rw [hermitianPotential_radial hσ hδ]
  unfold fieldPrimitive
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← realHermitianComplexify_smul]
  change trace ((B : Matrix (Fin N) (Fin N) ℝ) * matrixField σ δ k (t • B)) =
    (trace (complexify B * hermitianField σ δ (complexify (diagonal (fun i ↦ k i ^ 2)))
      (complexify (t • (B : Matrix (Fin N) (Fin N) ℝ))))).re
  have hf := complexify_matrixField hσ hδ k (t • B).prop
  change complexify (matrixField σ δ k (t • (B : Matrix (Fin N) (Fin N) ℝ))) =
    hermitianField σ δ (complexify (diagonal (fun i ↦ k i ^ 2)))
      (complexify (t • (B : Matrix (Fin N) (Fin N) ℝ))) at hf
  rw [← hf, ← map_mul, complexify_trace_real]

lemma fieldPrimitive_hasFDerivAt {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) (B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) :
    HasFDerivAt (fun B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) ↦ fieldPrimitive σ δ k B)
      ((-traceGradientMap (complexify (matrixField σ δ k B))).comp realHermitianComplexifyCLM) B := by
  have hh := ((hermitianPotential_hasFDerivAt hσ hδ (realK2SelfAdjoint k)
    (realHermitianComplexify B)).neg).comp B realHermitianComplexifyCLM.hasFDerivAt
  convert! hh using 1
  · funext A
    exact fieldPrimitive_eq_hermitianPotential hσ hδ k A
  · rw [complexify_matrixField hσ hδ k B.prop]
    rfl

lemma fieldPrimitive_path_derivative {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) {B : ℝ → selfAdjoint (Matrix (Fin N) (Fin N) ℝ)}
    {B' : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)} {x : ℝ} (hB : HasDerivAt B B' x) :
    HasDerivAt (fun x ↦ fieldPrimitive σ δ k (B x))
      (-trace (matrixField σ δ k (B x) * (B' : Matrix (Fin N) (Fin N) ℝ))) x := by
  convert! (fieldPrimitive_hasFDerivAt hσ hδ k (B x)).comp_hasDerivAt x hB using 1
  change -trace (matrixField σ δ k (B x) * (B' : Matrix (Fin N) (Fin N) ℝ)) =
    -(trace (complexify (matrixField σ δ k (B x)) * complexify (B' : Matrix (Fin N) (Fin N) ℝ))).re
  rw [← map_mul, complexify_trace_real]

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

lemma hermitian_integral {f : ℝ → Matrix (Fin N) (Fin N) ℂ}
    (hf : ∀ x, (f x).IsHermitian) : (∫ x, f x).IsHermitian := by
  change star (∫ x, f x) = ∫ x, f x
  have hh := (starL ℝ : Matrix (Fin N) (Fin N) ℂ ≃L[ℝ] Matrix (Fin N) (Fin N) ℂ).integral_comp_comm (μ := volume) f
  change (∫ x, star (f x)) = star (∫ x, f x) at hh
  rw [← hh]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x ↦ hf x)

lemma hermitianField_isHermitian (σ δ : ℝ) (C B : Matrix (Fin N) (Fin N) ℂ) :
    (hermitianField σ δ C B).IsHermitian := by
  apply Matrix.IsHermitian.smul _ (IsSelfAdjoint.all _)
  apply hermitian_integral
  intro s
  exact ((cfc_predicate (regularizedPrimitive σ δ) (quadraticMatrix C B s)).add
    (cfc_predicate (regularizedPrimitive σ δ) (quadraticMatrix C B (-s)))).sub
      (isHermitian_one.smul (IsSelfAdjoint.all _))

lemma matrixField_isHermitian {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian) :
    (matrixField σ δ k B).IsHermitian := by
  have hh := hermitianField_isHermitian σ δ
    (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B)
  rw [← complexify_matrixField hσ hδ k hB] at hh
  change star (matrixField σ δ k B) = matrixField σ δ k B
  ext i j
  have he := congrFun (congrFun hh i) j
  simpa [complexify, conjTranspose_apply] using congrArg Complex.re he

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
