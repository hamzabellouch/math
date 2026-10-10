import Mathlib

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix InnerProductSpace

namespace CriticalPercolation.HarmonicAnalysis
variable {ι : Type*} [Fintype ι]

def matrixQuadratic (M : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ M *ᵥ v

lemma hermitian_dot_comm (M : Matrix ι ι ℝ) (hM : M.IsHermitian) (x y : ι → ℝ) :
    x ⬝ᵥ M *ᵥ y = y ⬝ᵥ M *ᵥ x := by
  have ht : Mᵀ=M := Matrix.isHermitian_iff_isSymm.mp hM
  calc
    _ = Matrix.vecMul x M ⬝ᵥ y := Matrix.dotProduct_mulVec x M y
    _ = Matrix.vecMul x Mᵀ ⬝ᵥ y := by rw [ht]
    _ = _ := by rw [Matrix.vecMul_transpose,dotProduct_comm]

theorem generalized_gram_spectrum (A B : Matrix ι ι ℝ) (hA : A.PosDef)
    (hB : B.IsHermitian) (hmono : ∀ x, matrixQuadratic A x≤ matrixQuadratic B x) :
    ∃ (μ : Fin (Fintype.card ι) → ℝ) (b : Module.Basis (Fin (Fintype.card ι)) ℝ (ι → ℝ)),
      (∀ i, 1≤μ i) ∧ B.det=A.det*(∏ i, μ i) ∧
      (∀ x, matrixQuadratic A x=∑ i, (b.repr x i)^2) ∧
      (∀ x, matrixQuadratic B x=∑ i, μ i*(b.repr x i)^2) := by
  let := A.toNormedAddCommGroup hA
  let : SeminormedAddCommGroup (ι → ℝ) := (A.toNormedAddCommGroup hA).toSeminormedAddCommGroup
  let := A.toInnerProductSpace hA.posSemidef
  let T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := Matrix.toLin' (A⁻¹*B)
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hinner (x y : ι → ℝ) : ⟪x,y⟫_ℝ=x ⬝ᵥ A *ᵥ y := by
    change (A *ᵥ y) ⬝ᵥ star x = _
    simp only [star_trivial,dotProduct_comm]
  have hTinner (x y : ι → ℝ) : ⟪x,T y⟫_ℝ=x ⬝ᵥ B *ᵥ y := by
    rw [hinner]
    change x ⬝ᵥ A *ᵥ ((A⁻¹*B) *ᵥ y)=_
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv_cancel_left A B hdet]
  have hT : LinearMap.IsSymmetric (𝕜 := ℝ) (E := ι → ℝ) T := by
    intro x y
    rw [real_inner_comm y (T x),hTinner,hTinner]
    exact hermitian_dot_comm B hB y x
  have hn : Module.finrank ℝ (ι → ℝ)=Fintype.card ι := Module.finrank_fintype_fun_eq_card ℝ
  let b := hT.eigenvectorBasis hn
  let μ := hT.eigenvalues hn
  have hQa (x : ι → ℝ) : matrixQuadratic A x=⟪x,x⟫_ℝ := (hinner x x).symm
  have hQb (x : ι → ℝ) : matrixQuadratic B x=⟪x,T x⟫_ℝ := (hTinner x x).symm
  have hμ (i : Fin (Fintype.card ι)) : 1≤μ i := by
    have hh := hmono (b i)
    rw [hQa,hQb,hT.apply_eigenvectorBasis hn i,inner_smul_right] at hh
    change ⟪b i,b i⟫_ℝ ≤ μ i*⟪b i,b i⟫_ℝ at hh
    simpa only [real_inner_self_eq_norm_sq,OrthonormalBasis.norm_eq_one,one_pow,mul_one] using hh
  refine ⟨μ,b.toBasis,hμ,?_,?_,?_⟩
  · have hh := hT.det_eq_prod_eigenvalues hn
    change (Matrix.toLin' (A⁻¹*B)).det=∏ i, μ i at hh
    rw [LinearMap.det_toLin',Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv] at hh
    calc
      B.det = A.det*(A.det⁻¹*B.det) := by field_simp [hA.det_pos.ne']
      _ = _ := congrArg (A.det*·) hh
  · intro x
    rw [hQa,←b.sum_inner_mul_inner x x]
    apply Finset.sum_congr rfl
    intro i _
    rw [b.coe_toBasis_repr_apply,b.repr_apply_apply,real_inner_comm x (b i)]
    ring
  · intro x
    rw [hQb,←b.sum_inner_mul_inner x (T x)]
    apply Finset.sum_congr rfl
    intro i _
    rw [b.coe_toBasis_repr_apply,b.repr_apply_apply,←hT (b i) x,
      hT.apply_eigenvectorBasis hn i,inner_smul_left,real_inner_comm x (b i)]
    change ⟪x,b i⟫_ℝ * (μ i*⟪x,b i⟫_ℝ) = μ i*⟪x,b i⟫_ℝ^2
    ring

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
