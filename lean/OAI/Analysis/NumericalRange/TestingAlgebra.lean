import OAI.Analysis.NumericalRange.DensityAdjoints

namespace OAI

universe u_249 u_250

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
variable {n : Type u_249} {m : Type u_250} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
lemma tensorTesting_star (X Y : Matrix n m ℂ) (M : Matrix (n × m) (n × m) ℂ) :
    tensorTesting X Y Mᴴ = conj (tensorTesting Y X M) := by
  change inner ℂ (vectorize Y) (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) Mᴴ (vectorize X)) = _
  have hs : Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) Mᴴ =
      (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) M).adjoint :=
    map_star (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ)) M
  rw [hs,ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) M (vectorize Y)) (vectorize X) =
    conj (inner ℂ (vectorize X) (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) M (vectorize Y)))
  rw [inner_conj_symm]
lemma tensorTesting_similarity {S : Matrix n n ℂ} (hS : S.IsHermitian) (hu : IsUnit S)
    {X Y : Matrix n m ℂ} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hX : S*X = (a:ℂ) • X) (hY : S*Y = (b:ℂ) • Y)
    (A : Matrix n n ℂ) (v : ℂ → Matrix m m ℂ) :
    tensorTesting X Y (completeAnalyticEval A v) = (a/b:ℝ) *
      tensorTesting X Y (completeAnalyticEval (S*A*S⁻¹) v) := by
  have hSS : S⁻¹*S=1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hu)
  have hXi : S⁻¹*X = ((a⁻¹:ℝ):ℂ) • X := by
    have hh := congrArg (fun Z : Matrix n m ℂ => S⁻¹*Z) hX
    rw [← Matrix.mul_assoc,hSS,Matrix.one_mul,Matrix.mul_smul] at hh
    calc
      _ = ((a⁻¹:ℝ):ℂ) • ((a:ℂ) • (S⁻¹*X)) := by
        rw [smul_smul,← Complex.ofReal_mul,inv_mul_cancel₀ ha,Complex.ofReal_one,one_smul]
      _ = _ := congrArg (fun Z : Matrix n m ℂ => ((a⁻¹:ℝ):ℂ) • Z) hh.symm
  have hBX : Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (S⁻¹ ⊗ₖ (1:Matrix m m ℂ))
      (vectorize X) = ((a⁻¹:ℝ):ℂ) • vectorize X := by
    rw [kronecker_vectorize,Matrix.transpose_one,Matrix.mul_one,hXi]
    exact vectorizeCLM.map_smul _ _
  have hBY : Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (S ⊗ₖ (1:Matrix m m ℂ))
      (vectorize Y) = (b:ℂ) • vectorize Y := by
    rw [kronecker_vectorize,Matrix.transpose_one,Matrix.mul_one,hY]
    exact vectorizeCLM.map_smul _ _
  have hBH : (S ⊗ₖ (1:Matrix m m ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian,Matrix.conjTranspose_kronecker,hS.eq,Matrix.conjTranspose_one]
  have he : tensorTesting X Y (completeAnalyticEval (S*A*S⁻¹) v) =
      (b/a:ℝ) * tensorTesting X Y (completeAnalyticEval A v) := by
    rw [completeAnalyticEval_similarity hu]
    change inner ℂ (vectorize Y) (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) _ (vectorize X)) = _
    rw [map_mul,map_mul,mul_apply_eq_comp,mul_apply_eq_comp,hBX,map_smul]
    have hs : (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (S ⊗ₖ (1:Matrix m m ℂ))).adjoint =
        Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (S ⊗ₖ (1:Matrix m m ℂ)) := by
      have hh : Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (S ⊗ₖ (1:Matrix m m ℂ))ᴴ =
          (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (S ⊗ₖ (1:Matrix m m ℂ))).adjoint :=
        map_star (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ)) _
      rw [hBH.eq] at hh
      exact hh.symm
    rw [← hs]
    rw [ContinuousLinearMap.adjoint_inner_right,hBY,inner_smul_left,inner_smul_right]
    simp only [Complex.conj_ofReal,ofReal_div,ofReal_inv]
    change (b:ℂ) * ((a:ℂ)⁻¹ * tensorTesting X Y (completeAnalyticEval A v)) = _
    ring
  rw [he]
  simp only [ofReal_div]
  field_simp [ha,hb]

def hermitianField (K : C(UnitAddCircle,Matrix n n ℂ)) : C(UnitAddCircle,Matrix n n ℂ) :=
  ⟨fun t => K t+(K t)ᴴ,by fun_prop⟩
lemma hermitianField_hermitian
    {n : Type u_249} [Fintype n] [DecidableEq n] (K : C(UnitAddCircle,Matrix n n ℂ))
    (t : UnitAddCircle) :
    (hermitianField K t).IsHermitian := by
  change (K t+(K t)ᴴ)ᴴ = K t+(K t)ᴴ
  rw [Matrix.conjTranspose_add,Matrix.conjTranspose_conjTranspose,add_comm]
lemma hermitianField_integral (K : C(UnitAddCircle,Matrix n n ℂ))
    (u : C(UnitAddCircle,Matrix m m ℂ)) :
    (∫ t, hermitianField K t ⊗ₖ u t ∂AddCircle.haarAddCircle) =
      (∫ t, K t ⊗ₖ u t ∂AddCircle.haarAddCircle) +
      (∫ t, K t ⊗ₖ (u t)ᴴ ∂AddCircle.haarAddCircle)ᴴ := by
  have hi : Integrable (fun t => K t ⊗ₖ u t) AddCircle.haarAddCircle :=
    (continuous_kron K.continuous u.continuous).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have his := (continuous_kron K.continuous u.continuous.matrix_conjTranspose).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have his' : Integrable (fun t => (K t ⊗ₖ (u t)ᴴ)ᴴ) AddCircle.haarAddCircle :=
    (continuous_kron K.continuous u.continuous.matrix_conjTranspose).matrix_conjTranspose.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (fun t => hermitianField K t ⊗ₖ u t) =
      (fun t => K t ⊗ₖ u t + (K t ⊗ₖ (u t)ᴴ)ᴴ) := by
    funext t
    simp only [hermitianField,ContinuousMap.coe_mk,Matrix.add_kronecker,
      Matrix.conjTranspose_kronecker,Matrix.conjTranspose_conjTranspose]
  rw [he,integral_add hi his',integral_conjTranspose his]
lemma densityField_testing_sum (K : C(UnitAddCircle,Matrix n n ℂ)) (X Y : Matrix n m ℂ)
    (u : C(UnitAddCircle,Matrix m m ℂ)) :
    inner ℂ (densityField (μ := AddCircle.haarAddCircle) (hermitianField K) X Y) (hsTraceLp u) =
      tensorTesting X Y (∫ t, K t ⊗ₖ u t ∂AddCircle.haarAddCircle) +
      conj (tensorTesting Y X (∫ t, K t ⊗ₖ (u t)ᴴ ∂AddCircle.haarAddCircle)) := by
  unfold hsTraceLp
  rw [densityField_testing (hermitianField K) (hermitianField_hermitian K),
    hermitianField_integral K u,map_add,tensorTesting_star]
lemma matrixFourierTrace_star
    {m : Type u_250} [Fintype m] [DecidableEq m] (ij : m × m) (k : ℤ) (t : UnitAddCircle) :
    (matrixFourierTrace ij k t)ᴴ = matrixFourierTrace ij.swap (-k) t := by
  ext i j
  by_cases h : ij.1 = j ∧ ij.2 = i
  · simp [matrixFourierTrace, Matrix.conjTranspose_apply,h.1,h.2]
  · have h' : ¬(ij.2 = i ∧ ij.1 = j) := by tauto
    simp [matrixFourierTrace, Matrix.conjTranspose_apply,h,h']
lemma hsTrace_matrixFourier_star (ij : m × m) (k : ℤ) :
    l2Star (hsTraceLp (matrixFourierTrace ij k)) = hsTraceLp (matrixFourierTrace ij.swap (-k)) := by
  rw [hsTraceLp_star]
  congr 1
  ext t i j
  exact congrArg (fun M : Matrix m m ℂ => M i j) (matrixFourierTrace_star ij k t)
end CompleteCrouzeix

end

end

end OAI
