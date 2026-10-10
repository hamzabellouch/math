import Mathlib
import OAI.Analysis.AffineBernstein.RadialAdjugate

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section RadialAdjugateGL
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- The cofactor tensor of a symmetric matrix with any nonzero radial null
vector is a scalar multiple of its radial outer product. No rank or positive
definiteness assumption is needed, including an empty transverse block. -/
lemma radial_adjugate_exists_scalar {K : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ}
    (hK : K.IsSymm) {v : ι ⊕ Unit → ℝ} (hv : v ≠ 0) (hz : K *ᵥ v = 0) :
    ∃ c : ℝ, K.adjugate = c • Matrix.vecMulVec v v := by
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  let e := Equiv.swap (Sum.inr ()) j
  let w : ι ⊕ Unit → ℝ := (v j)⁻¹ • (v ∘ e)
  let B := K.submatrix e e
  have hB : B.IsSymm := by
    ext a b
    exact hK.apply (e a) (e b)
  have hw : w (Sum.inr ()) = 1 := by simp [w,e,Function.comp_def,hj]
  have hzB : B *ᵥ w = 0 := by
    dsimp only [B,w]
    rw [Matrix.mulVec_smul,Matrix.submatrix_mulVec_equiv]
    have hc : (v ∘ e) ∘ e.symm = v := by funext i; simp
    rw [hc,hz]
    simp
  let c : ℝ := (B.submatrix Sum.inl Sum.inl).det * ((v j)⁻¹)^2
  refine ⟨c,?_⟩
  ext a b
  have hh := radial_adjugate hB w hw hzB (e.symm a) (e.symm b)
  dsimp only [B] at hh
  rw [Matrix.adjugate_submatrix_equiv_self] at hh
  simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply,w,Pi.smul_apply,smul_eq_mul,
    Function.comp_apply] at hh
  rw [hh]
  simp only [Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul,c]
  ring

lemma adjugate_congruence_radial {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P K : Matrix κ κ ℝ) (v : κ → ℝ) (c : ℝ)
    (hK : K.adjugate = c • Matrix.vecMulVec (P *ᵥ v) (P *ᵥ v)) :
    (Pᵀ * K * P).adjugate = (c*P.det^2) • Matrix.vecMulVec v v := by
  rw [Matrix.adjugate_mul_distrib,Matrix.adjugate_mul_distrib,hK,
    ← Matrix.mul_assoc,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,← Matrix.adjugate_transpose,
    Matrix.vecMul_transpose,Matrix.mulVec_mulVec,Matrix.adjugate_mul,
    Matrix.smul_mulVec,Matrix.one_mulVec]
  ext i j
  simp only [Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul]
  ring

lemma adjugate_congruence_trace_radial {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P K : Matrix κ κ ℝ) (v : κ → ℝ) (c : ℝ)
    (hK : K.adjugate = c • Matrix.vecMulVec (P *ᵥ v) (P *ᵥ v))
    (hv : (∑ i, v i*v i) = 1) :
    (Pᵀ * K * P).adjugate.trace = c*P.det^2 := by
  rw [adjugate_congruence_radial P K v c hK,Matrix.trace_smul,Matrix.trace_vecMulVec]
  change (c*P.det^2)*(∑ i, v i*v i) = _
  rw [hv,mul_one]

end RadialAdjugateGL


end DependencyScope
end AffineBernstein
end

end OAI
