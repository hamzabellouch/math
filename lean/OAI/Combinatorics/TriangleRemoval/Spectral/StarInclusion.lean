import Mathlib

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

variable {E U : Type*} [Fintype E] [DecidableEq E] [Fintype U]

def starInclusion (S : Finset E) : Matrix E S ℝ :=
  fun e f => if e = f.val then 1 else 0

noncomputable def extendStar (S : Finset E) (M : Matrix S S ℝ) : Matrix E E ℝ :=
  starInclusion S * M * (starInclusion S)ᴴ

theorem starInclusion_mulVec (S : Finset E) (x : E → ℝ) :
    (starInclusion S)ᴴ *ᵥ x = fun e : S => x e.val := by
  ext e
  simp [starInclusion,Matrix.mulVec,dotProduct]

theorem extendStar_quadratic (S : Finset E) (M : Matrix S S ℝ) (x : E → ℝ) :
    x ⬝ᵥ (extendStar S M *ᵥ x) =
      (fun e : S => x e.val) ⬝ᵥ (M *ᵥ fun e : S => x e.val) := by
  rw [extendStar,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,starInclusion_mulVec,
    Matrix.dotProduct_mulVec]
  congr 1
  ext e
  simp [starInclusion,Matrix.vecMul,dotProduct]

theorem matrix_quadratic_abs (M : Matrix E E ℝ) (x : E → ℝ) :
    |x ⬝ᵥ (M *ᵥ x)| ≤ ‖M‖ * ∑ e, (x e)^2 := by
  let y : EuclideanSpace ℝ E := WithLp.toLp 2 x
  let T := (Matrix.toEuclideanCLM (n := E) (𝕜 := ℝ)) M
  have heq : x ⬝ᵥ (M *ᵥ x) = inner ℝ y (T y) := by
    simp [T,y,Matrix.toEuclideanCLM_toLp,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      mul_comm]
  have hn : ‖y‖^2 = ∑ e, (x e)^2 := by
    simp [EuclideanSpace.norm_sq_eq,y,Real.norm_eq_abs]
  rw [heq]
  calc
    _ ≤ ‖y‖ * ‖T y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖T‖ * ‖y‖) := mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg _)
    _ = ‖M‖ * ∑ e, (x e)^2 := by
      rw [mul_left_comm,← pow_two,hn]
      exact congrArg (fun a : ℝ => a * ∑ e, (x e)^2) (Matrix.l2_opNorm_toEuclideanCLM M)

theorem hermitian_norm_le_of_quadratic (M : Matrix E E ℝ) (hM : M.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a)
    (hquad : ∀ x : E → ℝ, |x ⬝ᵥ (M *ᵥ x)| ≤ a * ∑ e, (x e)^2) : ‖M‖ ≤ a := by
  have hev : ∀ e, |hM.eigenvalues e| ≤ a := by
    intro e
    have h := hquad (hM.eigenvectorBasis e).ofLp
    have hn : ∑ i, ((hM.eigenvectorBasis e).ofLp i)^2 = 1 := by
      have hh := hM.eigenvectorBasis.norm_eq_one e
      have hs := EuclideanSpace.norm_sq_eq (hM.eigenvectorBasis e)
      simpa [hh,Real.norm_eq_abs] using hs.symm
    rw [hn,mul_one] at h
    simpa [hM.eigenvalues_eq e] using h
  conv_lhs => rw [hM.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply,← Unitary.coe_star,CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg ha).mpr (fun e => hev e)

theorem sum_star_norm_bound (S : U → Finset E) (M : (u : U) → Matrix (S u) (S u) ℝ)
    (hM : ∀ u, (M u).IsHermitian) (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hlocal : ∀ u, ‖M u‖ ≤ ε)
    (hoverlap : ∀ e : E, ((Finset.univ.filter fun u => e ∈ S u).card : ℝ) ≤ K) :
    ‖∑ u, extendStar (S u) (M u)‖ ≤ K*ε := by
  have hsym : (∑ u, extendStar (S u) (M u)).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.sum_apply,star_sum]
    apply Finset.sum_congr rfl
    intro u _
    exact (Matrix.isHermitian_mul_mul_conjTranspose (starInclusion (S u)) (hM u)).apply i j
  apply hermitian_norm_le_of_quadratic _ hsym (K*ε) (mul_nonneg hK hε)
  intro x
  have hsum : x ⬝ᵥ ((∑ u, extendStar (S u) (M u)) *ᵥ x) =
      ∑ u, (fun e : S u => x e.val) ⬝ᵥ (M u *ᵥ fun e : S u => x e.val) := by
    simp only [Matrix.sum_mulVec,dotProduct_sum,extendStar_quadratic]
  have hcount : (∑ u, ∑ e : S u, (x e.val)^2) ≤ K * ∑ e, (x e)^2 := by
    have hrewrite : ∀ u, (∑ e : S u, (x e.val)^2) =
        ∑ e : E, if e ∈ S u then (x e)^2 else 0 := by
      intro u
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (Finset.univ.filter fun e => e ∈ S u)
        (fun e => by simp only [Finset.mem_filter,Finset.mem_univ,true_and])
        (fun e => (x e)^2)).symm
    simp_rw [hrewrite]
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    have heq : (∑ u : U, if e ∈ S u then (x e)^2 else 0) =
        ((Finset.univ.filter fun u => e ∈ S u).card : ℝ) * (x e)^2 := by
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hoverlap e) (sq_nonneg _)
  rw [hsum]
  calc
    _ ≤ ∑ u, |(fun e : S u => x e.val) ⬝ᵥ (M u *ᵥ fun e : S u => x e.val)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u, ε * ∑ e : S u, (x e.val)^2 := by
      apply Finset.sum_le_sum
      intro u _
      exact (matrix_quadratic_abs _ _).trans
        (mul_le_mul_of_nonneg_right (hlocal u) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    _ = ε * (∑ u, ∑ e : S u, (x e.val)^2) := by rw [Finset.mul_sum]
    _ ≤ ε * (K * ∑ e, (x e)^2) := mul_le_mul_of_nonneg_left hcount hε
    _ = K * ε * ∑ e, (x e)^2 := by ring

end SharpTerminalLeave

end
end

end OAI
