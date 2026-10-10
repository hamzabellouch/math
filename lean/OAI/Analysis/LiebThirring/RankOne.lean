import OAI.Analysis.LiebThirring.FieldLimit

namespace OAI

universe u19 u20 u21 u22 u23 u24

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


namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u19} [Fintype n] [DecidableEq n]

lemma hermitianField_state_jensen {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (φ : Matrix n n ℂ →L[ℝ] ℝ) (hφ : ∀ A, A.PosSemidef → 0 ≤ φ A) (hφ₁ : φ 1 = 1)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) :
    φ (hermitianField σ δ C B) ≤ scalarMu σ δ (φ C - (φ B) ^ 2) := by
  have hlim := φ.continuous.continuousAt.tendsto.comp (hermitianField_cutoff_limit hσ₁ hδ hC hB)
  have hs := primitive_shift_limit hσ₁ hδ (φ C - (φ B) ^ 2) (φ B)
  apply le_of_tendsto_of_tendsto hlim hs
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  have hc := continuous_fieldIntegrand hδ σ hC hB
  dsimp only [Function.comp_apply]
  rw [map_smul, ← φ.intervalIntegral_comp_comm (hc.intervalIntegrable _ _), smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (normalization_pos hσ₀ hσ₁).le
  apply intervalIntegral.integral_mono (by linarith : -R ≤ R)
    ((φ.continuous.comp hc).intervalIntegrable _ _)
    ((by have hf := (primitive_differentiable σ hδ).continuous; fun_prop : Continuous
      (fun s : ℝ ↦ regularizedPrimitive σ δ ((s - φ B) ^ 2 + (φ C - (φ B) ^ 2)) -
        regularizedPrimitive σ δ (s ^ 2))).intervalIntegrable _ _)
  intro s
  have hp := primitive_state_jensen hσ₁ hδ φ.toLinearMap hφ hφ₁ (quadraticMatrix_hermitian hC hB s)
  have he : φ (quadraticMatrix C B s) = (s - φ B) ^ 2 + (φ C - (φ B) ^ 2) := by
    simp only [quadraticMatrix, map_add, map_sub, map_smul, hφ₁, smul_eq_mul, mul_one]
    ring
  change φ (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s)) ≤
    regularizedPrimitive σ δ (φ (quadraticMatrix C B s)) at hp
  rw [he] at hp
  simpa only [Function.comp_apply, fieldIntegrand, map_sub, map_smul, hφ₁, smul_eq_mul, mul_one] using
    sub_le_sub_right hp (regularizedPrimitive σ δ (s ^ 2))

/-- A diagonal entry after unitary conjugation is a positive unital state. -/
def unitaryState (U : unitary (Matrix n n ℂ)) (i : n) : Matrix n n ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ (conjStarAlgAut ℂ (Matrix n n ℂ) U A i i).re
      map_add' := by intros; simp only [map_add, Matrix.add_apply, Complex.add_re]
      map_smul' := by intros; simp }

@[simp] lemma unitaryState_apply (U : unitary (Matrix n n ℂ)) (i : n) (A : Matrix n n ℂ) :
    unitaryState U i A = (conjStarAlgAut ℂ (Matrix n n ℂ) U A i i).re := rfl

lemma unitaryState_positive (U : unitary (Matrix n n ℂ)) (i : n)
    {A : Matrix n n ℂ} (hA : A.PosSemidef) : 0 ≤ unitaryState U i A := by
  have hp := hA.mul_mul_conjTranspose_same (U : Matrix n n ℂ)
  have hd := hp.diag_nonneg (i := i)
  exact (Complex.nonneg_iff.1 hd).1

@[simp] lemma unitaryState_one (U : unitary (Matrix n n ℂ)) (i : n) :
    unitaryState U i 1 = 1 := by simp

lemma state_quadratic_nonneg {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (φ : Matrix n n ℂ →L[ℝ] ℝ) (hφ : ∀ A, A.PosSemidef → 0 ≤ φ A) (hφ₁ : φ 1 = 1)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hM : (hermitianField σ δ C B).PosSemidef) (s : ℝ) :
    0 ≤ φ (quadraticMatrix C B s) := by
  have hj := hermitianField_state_jensen hσ₀ hσ₁ hδ φ hφ hφ₁ hC hB
  have hn := (hφ _ hM).trans hj
  have hz : 0 ≤ φ C - (φ B) ^ 2 := by
    apply (mu_strictMono hσ₀ hσ₁ hδ).le_iff_le.1
    simpa only [mu_zero] using hn
  simp only [quadraticMatrix, map_add, map_sub, map_smul, hφ₁, smul_eq_mul, mul_one]
  nlinarith [sq_nonneg (s - φ B)]

lemma hermitianField_nonneg_implies_quadratic {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hM : (hermitianField σ δ C B).PosSemidef) (s : ℝ) :
    (quadraticMatrix C B s).PosSemidef := by
  let X := quadraticMatrix C B s
  have hX : X.IsHermitian := quadraticMatrix_hermitian hC hB s
  apply hX.posSemidef_iff_eigenvalues_nonneg.2
  intro i
  have hp := state_quadratic_nonneg hσ₀ hσ₁ hδ
    (unitaryState (star hX.eigenvectorUnitary) i)
    (fun A hA ↦ unitaryState_positive _ _ hA) (unitaryState_one _ _) hC hB hM s
  change 0 ≤ unitaryState (star hX.eigenvectorUnitary) i X at hp
  rw [unitaryState_apply, hX.conjStarAlgAut_star_eigenvectorUnitary] at hp
  simpa using hp

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u20} [Fintype n] [DecidableEq n]

def diagonalFieldIntegrand (σ δ d : ℝ) (z : n → ℝ) (s : ℝ) : Matrix n n ℂ :=
  diagonal (fun i ↦ ((regularizedPrimitive σ δ ((s - z i) ^ 2 + d) -
    regularizedPrimitive σ δ (s ^ 2) : ℝ) : ℂ))

omit [Fintype n] in
lemma continuous_diagonalFieldIntegrand {δ : ℝ} (hδ : 0 < δ) (σ d : ℝ) (z : n → ℝ) :
    Continuous (diagonalFieldIntegrand σ δ d z) := by
  have hf := (primitive_differentiable σ hδ).continuous
  unfold diagonalFieldIntegrand
  fun_prop

lemma diagonalField_cutoff_limit {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (d : ℝ) (z : n → ℝ) :
    Tendsto (fun R : ℝ ↦ fieldNormalization σ • ∫ s in -R..R, diagonalFieldIntegrand σ δ d z s)
      atTop (𝓝 (scalarMu σ δ d • (1 : Matrix n n ℂ))) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  have he (R : ℝ) := (entryCLM i j).intervalIntegral_comp_comm (μ := volume)
    ((continuous_diagonalFieldIntegrand hδ σ d z).intervalIntegrable (-R) R)
  simp only [entryCLM_apply] at he
  have he' (R : ℝ) : (fieldNormalization σ • ∫ s in -R..R, diagonalFieldIntegrand σ δ d z s) i j =
      fieldNormalization σ • ∫ s in -R..R, diagonalFieldIntegrand σ δ d z s i j := by
    simp only [Matrix.smul_apply]
    rw [← he R]
  simp only [he']
  by_cases hij : i = j
  · subst j
    simp only [diagonalFieldIntegrand, diagonal_apply_eq, Matrix.smul_apply, one_apply_eq]
    have hs := Complex.continuous_ofReal.continuousAt.tendsto.comp (primitive_shift_limit hσ hδ d (z i))
    convert! hs using 1
    · funext R
      rw [intervalIntegral.integral_ofReal]
      simp [Complex.real_smul]
    · simp
  · simp only [diagonalFieldIntegrand, diagonal_apply_ne _ hij, intervalIntegral.integral_zero,
      smul_zero, Matrix.smul_apply, one_apply_ne hij]
    exact tendsto_const_nhds

omit [Fintype n] in
lemma quadraticMatrix_sub_diagonal (C : Matrix n n ℂ) (z : n → ℝ) (s d : ℝ) :
    quadraticMatrix C (diagonal (fun i ↦ (z i : ℂ))) s -
      diagonal (fun i ↦ (((s - z i) ^ 2 + d : ℝ) : ℂ)) =
      C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ)) - d • 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [quadraticMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      diagonal_apply_eq, one_apply_eq, Complex.real_smul]
    push_cast
    ring
  · simp [quadraticMatrix, hij]

lemma fieldIntegrand_tangent {σ δ d : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hd : 0 ≤ d) (C : Matrix n n ℂ) (z : n → ℝ) (s : ℝ)
    (hX : (quadraticMatrix C (diagonal (fun i ↦ (z i : ℂ))) s).PosSemidef) :
    fieldIntegrand σ δ C (diagonal (fun i ↦ (z i : ℂ))) s ≤
      diagonalFieldIntegrand σ δ d z s +
        quadraticTangent σ δ d z (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ)) - d • 1) s := by
  have ht := primitive_diagonal_tangent hσ₀ hσ₁ hδ hd z s hX
  rw [quadraticMatrix_sub_diagonal, ← hX.isHermitian.cfc_eq,
    cfc_diagonal_real _ _ (primitive_differentiable σ hδ).continuous] at ht
  have hh := sub_le_sub_right ht (regularizedPrimitive σ δ (s ^ 2) • (1 : Matrix n n ℂ))
  convert! hh using 1
  unfold diagonalFieldIntegrand
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      diagonal_apply_eq, one_apply_eq, Complex.real_smul]
    push_cast
    ring
  · simp [hij]

lemma hermitianField_diagonal_tangent {σ δ d : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hd : 0 ≤ d) {C : Matrix n n ℂ} (hC : C.IsHermitian) (z : n → ℝ)
    (hX : ∀ s, (quadraticMatrix C (diagonal (fun i ↦ (z i : ℂ))) s).PosSemidef) :
    hermitianField σ δ C (diagonal (fun i ↦ (z i : ℂ))) ≤
      scalarMu σ δ d • 1 + (σ * (d + δ) ^ (σ - 1)) •
        tangentSchur σ (d + δ) z (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ)) - d • 1) := by
  have hB : (diagonal (fun i ↦ (z i : ℂ))).IsHermitian :=
    isHermitian_diagonal_iff.2 (fun i ↦ by simp [IsSelfAdjoint])
  let Z := C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ)) - d • 1
  have hiT := integrable_quadraticTangent hσ₁ hδ hd z Z
  have hlimT := (intervalIntegral_tendsto_integral hiT tendsto_neg_atTop_atBot tendsto_id).const_smul
    (fieldNormalization σ)
  rw [integral_quadraticTangent hσ₁ hδ hd] at hlimT
  have hlimY := diagonalField_cutoff_limit hσ₁ hδ d z
  apply le_of_tendsto_of_tendsto (hermitianField_cutoff_limit hσ₁ hδ hC hB) (hlimY.add hlimT)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  have hc := continuous_fieldIntegrand hδ σ hC hB
  have hy := continuous_diagonalFieldIntegrand hδ σ d z
  have hab : -R ≤ R := by linarith
  have hi := MeasureTheory.integral_mono (μ := volume.restrict (Ioc (-R) R))
    (hc.intervalIntegrable (-R) R).1
    (((hy.intervalIntegrable (-R) R).add (hiT.intervalIntegrable (a := -R) (b := R))).1)
    (fun s ↦ fieldIntegrand_tangent hσ₀ hσ₁ hδ hd C z s (hX s))
  rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab] at hi
  rw [intervalIntegral.integral_add (hy.intervalIntegrable _ _) hiT.intervalIntegrable] at hi
  simpa only [smul_add, id_eq] using smul_le_smul_of_nonneg_left hi (normalization_pos hσ₀ hσ₁).le

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u21} [Fintype n] [DecidableEq n]

lemma phaseUnitary_conj_diagonal (z x : n → ℝ) (t : ℝ) :
    conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) (diagonal (fun i ↦ (x i : ℂ))) =
      diagonal (fun i ↦ (x i : ℂ)) := by
  ext i j
  rw [phaseUnitary_conj_apply]
  by_cases hij : i = j
  · subst j; simp
  · simp [hij]

lemma trace_conjugate_difference_zero (U : unitary (Matrix n n ℂ)) (D : Matrix n n ℂ) :
    trace (2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) U D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star U) D) = 0 := by
  rw [trace_sub, trace_sub, trace_smul, trace_unitary_conjugate, trace_unitary_conjugate]
  simp only [two_smul]
  abel

lemma fieldIntegrand_trace_phase_nonneg {σ δ : ℝ} (hδ : 0 < δ)
    {C : Matrix n n ℂ} (hC : C.IsHermitian) (z : n → ℝ) (s t : ℝ) :
    0 ≤ (trace (fieldIntegrand σ δ C (diagonal (fun i ↦ (z i : ℂ))) s *
      (2 • (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t))
          (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ)))))).re := by
  let B := diagonal (fun i ↦ (z i : ℂ))
  let D := C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))
  let Y := diagonal (fun i ↦ (((s - z i) ^ 2 : ℝ) : ℂ))
  let H := 2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D -
    conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t)) D
  have hB : B.IsHermitian := isHermitian_diagonal_iff.2 (fun i ↦ by simp [IsSelfAdjoint])
  have he : quadraticMatrix C B s = D + Y := by
    have hh := quadraticMatrix_sub_diagonal C z s 0
    simp only [add_zero, zero_smul, sub_zero] at hh
    exact (sub_eq_iff_eq_add.1 hh)
  have hA : (D + Y).IsHermitian := he ▸ quadraticMatrix_hermitian hC hB s
  have hp := trace_unitary_comparison_sub_invariant hA (primitive_strictMono σ hδ).monotone
    (phaseUnitary z t) (phaseUnitary_conj_diagonal z (fun i ↦ (s - z i) ^ 2) t)
  rw [← hA.cfc_eq, ← he] at hp
  have hH : trace H = 0 := trace_conjugate_difference_zero _ _
  change 0 ≤ (trace ((cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
    regularizedPrimitive σ δ (s ^ 2) • 1) * H)).re
  rw [sub_mul, trace_sub, smul_mul_assoc, one_mul, trace_smul, hH, smul_zero, sub_zero]
  exact hp

lemma hermitianField_trace_phase_nonneg {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) {C : Matrix n n ℂ} (hC : C.IsHermitian) (z : n → ℝ) (t : ℝ) :
    0 ≤ (trace (hermitianField σ δ C (diagonal (fun i ↦ (z i : ℂ))) *
      (2 • (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t))
          (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ)))))).re := by
  have hB : (diagonal (fun i ↦ (z i : ℂ))).IsHermitian :=
    isHermitian_diagonal_iff.2 (fun i ↦ by simp [IsSelfAdjoint])
  apply trace_unitary_comparison_limit (hermitianField_cutoff_limit hσ₁ hδ hC hB) (phaseUnitary z t)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  let D := C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))
  let H := 2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D -
    conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t)) D
  have hc := continuous_fieldIntegrand hδ σ hC hB
  have hn : 0 ≤ ∫ s in -R..R, tracePairCLM H (fieldIntegrand σ δ C (diagonal (fun i ↦ (z i : ℂ))) s) := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro s hs
    rw [tracePairCLM_apply, trace_mul_comm]
    exact fieldIntegrand_trace_phase_nonneg hδ hC z s t
  rw [(tracePairCLM H).intervalIntegral_comp_comm (hc.intervalIntegrable _ _)] at hn
  change 0 ≤ (trace ((fieldNormalization σ • ∫ s in -R..R,
    fieldIntegrand σ δ C (diagonal (fun i ↦ (z i : ℂ))) s) * H)).re
  rw [smul_mul_assoc, trace_smul, Complex.real_smul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [tracePairCLM_apply, trace_mul_comm] at hn
  exact mul_nonneg (normalization_pos hσ₀ hσ₁).le hn

lemma hermitianField_tangentSchur_contraction {σ δ a : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (ha : 0 < a) {C : Matrix n n ℂ} (hC : C.IsHermitian) (z : n → ℝ) :
    (trace (hermitianField σ δ C (diagonal (fun i ↦ (z i : ℂ))) *
      tangentSchur σ a z (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))))).re ≤
      (trace (hermitianField σ δ C (diagonal (fun i ↦ (z i : ℂ))) *
        (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))))).re :=
  tangentSchur_trace_comparison hσ₁ ha z _ _ (hermitianField_trace_phase_nonneg hσ₀ hσ₁ hδ hC z)

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u22} [Fintype n] [DecidableEq n]

lemma tangentSchur_sub_smul_one (σ : ℝ) {a : ℝ} (ha : 0 < a)
    (z : n → ℝ) (D : Matrix n n ℂ) (d : ℝ) :
    tangentSchur σ a z (D - d • 1) = tangentSchur σ a z D - d • 1 := by
  calc
    _ = tangentSchur σ a z D - d • tangentSchur σ a z 1 := by
      ext i j
      simp only [tangentSchur_apply σ ha, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
      ring
    _ = _ := by rw [tangentSchur_one]

def vectorMass (a : n → ℂ) : ℝ := ∑ i, Complex.normSq (a i)

omit [DecidableEq n] in
lemma vectorMass_nonneg (a : n → ℂ) : 0 ≤ vectorMass a :=
  Finset.sum_nonneg (fun i _ ↦ Complex.normSq_nonneg (a i))

omit [DecidableEq n] in
lemma vectorMass_eq_zero {a : n → ℂ} : vectorMass a = 0 ↔ a = 0 := by
  rw [vectorMass, Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ Complex.normSq_nonneg (a i))]
  simp [funext_iff]

omit [DecidableEq n] in
lemma dot_star_self_vectorMass (a : n → ℂ) : star a ⬝ᵥ a = (vectorMass a : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    vectorMass, Complex.ofReal_sum]

omit [DecidableEq n] in
lemma rankone_trace (a : n → ℂ) : trace (vecMulVec a (star a)) = (vectorMass a : ℂ) := by
  rw [trace_vecMulVec, dotProduct_comm, dot_star_self_vectorMass]

omit [DecidableEq n] in
lemma rankone_square (a : n → ℂ) :
    vecMulVec a (star a) * vecMulVec a (star a) = vectorMass a • vecMulVec a (star a) := by
  rw [vecMulVec_mul_vecMulVec, dot_star_self_vectorMass, vecMulVec_smul]
  ext i j
  simp [Complex.real_smul]

lemma rankone_tracePair_positive (a : n → ℂ) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    0 ≤ tracePairCLM (vecMulVec a (star a)) A := by
  rw [tracePairCLM_apply, trace_mul_comm, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
  exact (Complex.nonneg_iff.1 (hA.dotProduct_mulVec_nonneg a)).1

lemma rankone_tracePair_monotone (a : n → ℂ) : Monotone (tracePairCLM (vecMulVec a (star a))) := by
  intro A B hAB
  have h := rankone_tracePair_positive a (le_iff.1 hAB)
  rw [map_sub] at h
  linarith

lemma rankone_tracePair_one (a : n → ℂ) : tracePairCLM (vecMulVec a (star a)) 1 = vectorMass a := by
  rw [tracePairCLM_apply, mul_one, rankone_trace, Complex.ofReal_re]

lemma rankone_tracePair_self (a : n → ℂ) :
    tracePairCLM (vecMulVec a (star a)) (vecMulVec a (star a)) = (vectorMass a) ^ 2 := by
  rw [tracePairCLM_apply, rankone_square, trace_smul, rankone_trace, Complex.real_smul]
  simp [pow_two]

/-- The rank-one comparison in an arbitrary eigenbasis of B. No positivity of
C - B² is assumed; its needed trace bound is obtained by contraction. -/
lemma rankone_diagonal_comparison {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    {C : Matrix n n ℂ} (hC : C.IsHermitian) (z : n → ℝ) (a : n → ℂ)
    (hM : hermitianField σ δ C (diagonal (fun i ↦ (z i : ℂ))) = vecMulVec a (star a)) :
    (vectorMass a) ^ (1 + 1 / σ) ≤
      (trace (vecMulVec a (star a) * (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))))).re := by
  by_cases ha : a = 0
  · subst a
    have hexp : (1 + 1 / σ : ℝ) ≠ 0 := by positivity
    have hz : vecMulVec (0 : n → ℂ) (star (0 : n → ℂ)) = 0 := by
      ext i j
      simp [vecMulVec]
    rw [hz, zero_mul, trace_zero, Complex.zero_re]
    simpa only [vectorMass, Pi.zero_apply, Complex.normSq_zero, Finset.sum_const_zero]
      using (le_of_eq (Real.zero_rpow hexp))
  have hm : 0 < vectorMass a := lt_of_le_of_ne (vectorMass_nonneg a)
    (Ne.symm (mt vectorMass_eq_zero.1 ha))
  let d := (vectorMass a + δ ^ σ) ^ (1 / σ) - δ
  have hd : 0 < d := inverse_mu_positive hσ₀ hδ hm
  have he : scalarMu σ δ d = vectorMass a := mu_inverse hσ₀ hσ₁ hδ hm
  have hB : (diagonal (fun i ↦ (z i : ℂ))).IsHermitian :=
    isHermitian_diagonal_iff.2 (fun i ↦ by simp [IsSelfAdjoint])
  have hMP : (hermitianField σ δ C (diagonal (fun i ↦ (z i : ℂ)))).PosSemidef := by
    rw [hM]
    exact posSemidef_vecMulVec_self_star a
  have ht := hermitianField_diagonal_tangent hσ₀ hσ₁ hδ hd.le hC z
    (hermitianField_nonneg_implies_quadratic hσ₀ hσ₁ hδ hC hB hMP)
  rw [hM, he, tangentSchur_sub_smul_one σ (by linarith) z _ d] at ht
  have hp := rankone_tracePair_monotone a ht
  rw [map_add, map_smul, map_smul, map_sub, map_smul, rankone_tracePair_one,
    rankone_tracePair_self] at hp
  simp only [smul_eq_mul] at hp
  have hc := hermitianField_tangentSchur_contraction hσ₀ hσ₁ hδ (show 0 < d + δ by linarith) hC z
  rw [hM] at hc
  have hk : 0 < σ * (d + δ) ^ (σ - 1) := mul_pos hσ₀ (Real.rpow_pos_of_pos (by linarith) _)
  have hpd : d * vectorMass a ≤ tracePairCLM (vecMulVec a (star a))
      (tangentSchur σ (d + δ) z (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ)))) := by
    nlinarith
  exact (rankone_scalar_power hσ₀ hσ₁ hδ hm hd.le he).trans (hpd.trans hc)

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u23} [Fintype n] [DecidableEq n]

def unitaryConjCLM (U : unitary (Matrix n n ℂ)) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := conjStarAlgAut ℂ (Matrix n n ℂ) U
      map_add' := by intros; exact map_add _ _ _
      map_smul' := by intros; simp }

@[simp] lemma unitaryConjCLM_apply (U : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    unitaryConjCLM U A = conjStarAlgAut ℂ (Matrix n n ℂ) U A := rfl

lemma quadraticMatrix_conj (U : unitary (Matrix n n ℂ)) (C B : Matrix n n ℂ) (s : ℝ) :
    quadraticMatrix (conjStarAlgAut ℂ (Matrix n n ℂ) U C)
      (conjStarAlgAut ℂ (Matrix n n ℂ) U B) s =
        conjStarAlgAut ℂ (Matrix n n ℂ) U (quadraticMatrix C B s) := by
  have hs (r : ℝ) (A : Matrix n n ℂ) :
      conjStarAlgAut ℂ (Matrix n n ℂ) U (r • A) =
        r • conjStarAlgAut ℂ (Matrix n n ℂ) U A := (unitaryConjCLM U).map_smul r A
  simp only [quadraticMatrix, map_add, map_sub, hs, map_one]

lemma cfc_unitary_conj {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℂ)) (f : ℝ → ℝ) :
    cfc f (conjStarAlgAut ℂ (Matrix n n ℂ) U A) = conjStarAlgAut ℂ (Matrix n n ℂ) U (cfc f A) := by
  have h := functional_unitary_conjugate hA U f
  rwa [← IsHermitian.cfc_eq, ← hA.cfc_eq] at h

lemma pairedFieldIntegrand_conj (σ δ : ℝ) {C B : Matrix n n ℂ}
    (hC : C.IsHermitian) (hB : B.IsHermitian) (U : unitary (Matrix n n ℂ)) (s : ℝ) :
    pairedFieldIntegrand σ δ (conjStarAlgAut ℂ (Matrix n n ℂ) U C)
      (conjStarAlgAut ℂ (Matrix n n ℂ) U B) s =
        unitaryConjCLM U (pairedFieldIntegrand σ δ C B s) := by
  simp only [pairedFieldIntegrand, quadraticMatrix_conj, unitaryConjCLM_apply,
    cfc_unitary_conj (quadraticMatrix_hermitian hC hB _), map_sub, map_add, map_smul, map_one]

lemma hermitianField_conj {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (U : unitary (Matrix n n ℂ)) :
    hermitianField σ δ (conjStarAlgAut ℂ (Matrix n n ℂ) U C)
      (conjStarAlgAut ℂ (Matrix n n ℂ) U B) =
        conjStarAlgAut ℂ (Matrix n n ℂ) U (hermitianField σ δ C B) := by
  change _ = unitaryConjCLM U (hermitianField σ δ C B)
  simp only [hermitianField, pairedFieldIntegrand_conj σ δ hC hB, map_smul]
  rw [(unitaryConjCLM U).integral_comp_comm (integrable_pairedFieldIntegrand hσ hδ hC hB)]

lemma unitary_conj_rankone (U : unitary (Matrix n n ℂ)) (a : n → ℂ) :
    conjStarAlgAut ℂ (Matrix n n ℂ) U (vecMulVec a (star a)) =
      vecMulVec ((U : Matrix n n ℂ) *ᵥ a) (star ((U : Matrix n n ℂ) *ᵥ a)) := by
  rw [conjStarAlgAut_apply, mul_vecMulVec, vecMulVec_mul, star_mulVec]
  rfl

lemma vectorMass_unitary (U : unitary (Matrix n n ℂ)) (a : n → ℂ) :
    vectorMass ((U : Matrix n n ℂ) *ᵥ a) = vectorMass a := by
  apply Complex.ofReal_injective
  rw [← rankone_trace, ← unitary_conj_rankone, trace_unitary_conjugate, rankone_trace]

/-- The complete complex Hermitian rank-one comparison, before identifying the
real symmetric field with its complexification. -/
lemma rankone_hermitian_comparison {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (a : n → ℂ)
    (hM : hermitianField σ δ C B = vecMulVec a (star a)) :
    (vectorMass a) ^ (1 + 1 / σ) ≤ (trace (vecMulVec a (star a) * (C - B ^ 2))).re := by
  let U := star hB.eigenvectorUnitary
  let C' := conjStarAlgAut ℂ (Matrix n n ℂ) U C
  let a' := (U : Matrix n n ℂ) *ᵥ a
  have hb : conjStarAlgAut ℂ (Matrix n n ℂ) U B =
      diagonal (fun i ↦ (hB.eigenvalues i : ℂ)) := hB.conjStarAlgAut_star_eigenvectorUnitary
  have hm : hermitianField σ δ C' (diagonal (fun i ↦ (hB.eigenvalues i : ℂ))) =
      vecMulVec a' (star a') := by
    rw [← hb, hermitianField_conj hσ₁ hδ hC hB, hM, unitary_conj_rankone]
  have hp := rankone_diagonal_comparison hσ₀ hσ₁ hδ (hermitian_unitary_conjugate hC U)
    hB.eigenvalues a' hm
  have hsq : conjStarAlgAut ℂ (Matrix n n ℂ) U (B ^ 2) =
      diagonal (fun i ↦ ((hB.eigenvalues i ^ 2 : ℝ) : ℂ)) := by
    rw [map_pow, hb, pow_two, diagonal_mul_diagonal]
    congr 1
    funext i
    simp [pow_two]
  rw [vectorMass_unitary U a] at hp
  have ht : trace (vecMulVec a' (star a') *
      (C' - diagonal (fun i ↦ ((hB.eigenvalues i ^ 2 : ℝ) : ℂ)))) =
      trace (vecMulVec a (star a) * (C - B ^ 2)) := by
    rw [← unitary_conj_rankone U a, ← hsq]
    change trace (conjStarAlgAut ℂ (Matrix n n ℂ) U (vecMulVec a (star a)) *
      (conjStarAlgAut ℂ (Matrix n n ℂ) U C - conjStarAlgAut ℂ (Matrix n n ℂ) U (B ^ 2))) = _
    rw [← map_sub, ← map_mul, trace_unitary_conjugate]
  rwa [ht] at hp

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u24} [Fintype n] [DecidableEq n]

def complexify : Matrix n n ℝ →⋆ₐ[ℝ] Matrix n n ℂ :=
  { (Algebra.ofId ℝ ℂ).mapMatrix with
    map_star' := by
      intro A
      ext i j
      simp [Matrix.star_apply] }

@[simp] lemma complexify_apply (A : Matrix n n ℝ) (i j : n) : complexify A i j = (A i j : ℂ) := rfl

def complexifyCLM : Matrix n n ℝ →L[ℝ] Matrix n n ℂ :=
  complexify.toLinearMap.toContinuousLinearMap

@[simp] lemma complexifyCLM_apply (A : Matrix n n ℝ) : complexifyCLM A = complexify A := rfl

def realPartCLM : Matrix n n ℂ →L[ℝ] Matrix n n ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ A.map Complex.re
      map_add' := by intros; ext i j; simp
      map_smul' := by intros; ext i j; simp }

@[simp] lemma realPartCLM_complexify (A : Matrix n n ℝ) : realPartCLM (complexify A) = A := by
  ext i j
  exact Complex.ofReal_re _

lemma complexify_hermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) : (complexify A).IsHermitian := by
  change star (complexify A) = complexify A
  rw [← map_star, hA.star_eq]

lemma complexify_cfc {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    complexify (cfc f A) = cfc f (complexify A) :=
  StarAlgHomClass.map_cfc complexify f A (A.finite_real_spectrum.continuousOn f)
    complexifyCLM.continuous hA (complexify_hermitian hA)

lemma complexify_diagonal (x : n → ℝ) :
    complexify (diagonal x) = diagonal (fun i ↦ (x i : ℂ)) := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

lemma complexify_vecMulVec (a : n → ℝ) :
    complexify (vecMulVec a a) = vecMulVec (fun i ↦ (a i : ℂ)) (star (fun i ↦ (a i : ℂ))) := by
  ext i j
  simp [vecMulVec]

omit [DecidableEq n] in
lemma vectorMass_ofReal (a : n → ℝ) : vectorMass (fun i ↦ (a i : ℂ)) = ∑ i, a i ^ 2 := by
  simp [vectorMass, Complex.normSq_ofReal, pow_two]

lemma complexify_trace_real (A : Matrix n n ℝ) : (trace (complexify A)).re = trace A := by
  simp only [trace, diag, complexify_apply, Complex.re_sum, Complex.ofReal_re]

lemma matrixX_hermitian {N : ℕ} (k : Fin N → ℝ) {B : Matrix (Fin N) (Fin N) ℝ}
    (hB : B.IsHermitian) (s : ℝ) : (matrixX k B s).IsHermitian := by
  exact ((isHermitian_diagonal (fun i ↦ k i ^ 2)).sub (hB.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (2 * s)))).add
    (isHermitian_one.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (s ^ 2)))

lemma complexify_matrixX {N : ℕ} (k : Fin N → ℝ) (B : Matrix (Fin N) (Fin N) ℝ) (s : ℝ) :
    complexify (matrixX k B s) = quadraticMatrix (complexify (diagonal (fun i ↦ k i ^ 2)))
      (complexify B) s := by
  simp only [matrixX, quadraticMatrix, map_add, map_sub, map_smul, map_one]
  abel

lemma complexify_truncatedField {N : ℕ} {σ δ : ℝ} (hδ : 0 < δ) (k : Fin N → ℝ)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian) (R : ℝ) :
    complexify (truncatedField σ δ k B R) = fieldNormalization σ • ∫ s in -R..R,
      fieldIntegrand σ δ (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B) s := by
  have hc : Continuous (fun s ↦ cfc (regularizedPrimitive σ δ) (matrixX k B s) -
      regularizedPrimitive σ δ (s ^ 2) • (1 : Matrix (Fin N) (Fin N) ℝ)) := by
    have hx : Continuous (fun s ↦ cfc (regularizedPrimitive σ δ) (matrixX k B s)) :=
      Continuous.cfc_of_mem_nhdsSet (s := Set.univ) _ Filter.univ_mem
        (by unfold matrixX; fun_prop) (matrixX_hermitian k hB)
        (primitive_differentiable σ hδ).continuous.continuousOn
    exact hx.sub (((primitive_differentiable σ hδ).continuous.comp (continuous_pow 2)).smul continuous_const)
  change complexifyCLM (truncatedField σ δ k B R) = _
  rw [truncatedField, map_smul, ← complexifyCLM.intervalIntegral_comp_comm (hc.intervalIntegrable _ _)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [complexifyCLM_apply, map_sub, map_smul, map_one,
    complexify_cfc (matrixX_hermitian k hB s), complexify_matrixX, fieldIntegrand]

lemma complexify_matrixField {N : ℕ} {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian) :
    complexify (matrixField σ δ k B) =
      hermitianField σ δ (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B) := by
  have hC := complexify_hermitian (isHermitian_diagonal (fun i ↦ k i ^ 2))
  have hl := hermitianField_cutoff_limit hσ hδ hC (complexify_hermitian hB)
  have ht : Tendsto (fun R ↦ complexify (truncatedField σ δ k B R)) atTop (𝓝
      (hermitianField σ δ (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B))) := by
    simpa only [complexify_truncatedField hδ k hB] using hl
  have hr := realPartCLM.continuous.continuousAt.tendsto.comp ht
  change Tendsto (fun R ↦ realPartCLM (complexify (truncatedField σ δ k B R))) atTop
    (𝓝 (realPartCLM (hermitianField σ δ
      (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B)))) at hr
  simp only [realPartCLM_complexify] at hr
  have he : matrixField σ δ k B = realPartCLM
      (hermitianField σ δ (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B)) := hr.limUnder_eq
  have hh := complexifyCLM.continuous.continuousAt.tendsto.comp hr
  change Tendsto (fun R ↦ complexify (truncatedField σ δ k B R)) atTop
    (𝓝 (complexify (realPartCLM (hermitianField σ δ
      (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B))))) at hh
  rw [he]
  exact tendsto_nhds_unique hh ht

/-- The rank-one comparison for the real field
with its symmetric-cutoff definition. -/
theorem source_rankone_comparison {N : ℕ} {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (k : Fin N → ℝ) {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian)
    (a : Fin N → ℝ) (hM : matrixField σ δ k B = vecMulVec a a) :
    (∑ i, a i ^ 2) ^ (1 + 1 / σ) ≤
      ∑ i, a i * ((diagonal (fun i ↦ k i ^ 2) - B ^ 2) *ᵥ a) i := by
  have hm : hermitianField σ δ (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B) =
      vecMulVec (fun i ↦ (a i : ℂ)) (star (fun i ↦ (a i : ℂ))) := by
    rw [← complexify_matrixField hσ₁ hδ k hB, hM, complexify_vecMulVec]
  have hp := rankone_hermitian_comparison hσ₀ hσ₁ hδ
    (complexify_hermitian (isHermitian_diagonal (fun i ↦ k i ^ 2))) (complexify_hermitian hB)
    (fun i ↦ (a i : ℂ)) hm
  rw [vectorMass_ofReal, ← complexify_vecMulVec, ← map_pow, ← map_sub, ← map_mul,
    complexify_trace_real, trace_mul_comm, mul_vecMulVec, trace_vecMulVec, dotProduct_comm] at hp
  exact hp

theorem rankOneClaim {N : ℕ} : @RankOneClaim N := by
  intro σ δ k B a hσ₀ hσ₁ hδ _ hB hM
  exact source_rankone_comparison hσ₀ hσ₁ hδ k hB a hM

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
