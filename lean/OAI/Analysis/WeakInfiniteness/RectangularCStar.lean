import Mathlib

namespace OAI

noncomputable section

namespace WeakPureInfiniteness

open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder


open scoped CStarAlgebra InnerProductSpace NNReal

open CStarMatrix CStarModule ContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

omit [PartialOrder A] [StarOrderedRing A] [Fintype k] in
lemma rectangular_toCLM_mul (M : CStarMatrix m n A) (N : CStarMatrix n k A) :
    toCLM (M*N) = (toCLM N).comp (toCLM M) := by
  ext v i
  simp only [toCLM_apply, comp_apply]
  exact congrFun (Matrix.vecMul_vecMul v M N).symm i

omit [PartialOrder A] [StarOrderedRing A] [Fintype m] [Fintype n] in
lemma rectangular_conjTranspose_conjTranspose (M : CStarMatrix m n A) :
    M.conjTranspose.conjTranspose = M := by
  ext i j
  simp only [CStarMatrix.conjTranspose_apply, star_star]

lemma rectangular_norm_mul_le (M : CStarMatrix m n A) (N : CStarMatrix n k A) :
    ‖M*N‖ ≤ ‖M‖*‖N‖ := by
  rw [CStarMatrix.norm_def, rectangular_toCLM_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

lemma rectangular_norm_conjTranspose_le (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ ≤ ‖M‖ := by
  apply CStarMatrix.norm_le_of_forall_inner_le (C := ‖M‖₊)
  intro v w
  refine (congrArg (fun a : A => ‖a‖)
    (inner_toCLM_conjTranspose_right (M := M) (v := w) (w := v))).trans_le ?_
  calc
    ‖⟪toCLM M w, v⟫_A‖ ≤ ‖toCLM M w‖*‖v‖ := norm_inner_le (WithCStarModule A (n → A))
    _ ≤ (‖M‖*‖w‖)*‖v‖ := by
      gcongr
      exact le_opNorm _ _
    _ = ‖M‖₊*‖v‖*‖w‖ := by simp only [coe_nnnorm]; ring

lemma rectangular_norm_conjTranspose (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ = ‖M‖ := by
  apply le_antisymm (rectangular_norm_conjTranspose_le M)
  simpa only [rectangular_conjTranspose_conjTranspose] using
    rectangular_norm_conjTranspose_le M.conjTranspose

lemma rectangular_norm_sq_le_range (M : CStarMatrix m n A) :
    ‖M‖^2 ≤ ‖M*M.conjTranspose‖ := by
  have hmain : ‖M‖ ≤ Real.sqrt ‖M*M.conjTranspose‖ := by
    change ‖toCLM M‖ ≤ Real.sqrt ‖M*M.conjTranspose‖
    rw [opNorm_le_iff (by positivity)]
    intro v
    rw [norm_eq_sqrt_norm_inner_self (A := A), ← inner_toCLM_conjTranspose_right]
    have h₁ : ‖⟪v, (toCLM M.conjTranspose) ((toCLM M) v)⟫_A‖ ≤
        ‖M*M.conjTranspose‖ * ‖v‖^2 := calc
      _ ≤ ‖v‖ * ‖(toCLM M.conjTranspose) ((toCLM M) v)‖ := norm_inner_le (WithCStarModule A (m → A))
      _ ≤ ‖v‖ * (‖(toCLM M.conjTranspose).comp (toCLM M)‖ * ‖v‖) := by
        gcongr
        exact le_opNorm ((toCLM M.conjTranspose).comp (toCLM M)) v
      _ = ‖M*M.conjTranspose‖*‖v‖^2 := by
        rw [← rectangular_toCLM_mul, ← CStarMatrix.norm_def]
        ring
    conv_rhs => rw [show ‖v‖ = Real.sqrt (‖v‖^2) by simp]
    rw [← Real.sqrt_mul (norm_nonneg _)]
    exact Real.sqrt_le_sqrt h₁
  exact (Real.le_sqrt (norm_nonneg _) (norm_nonneg _)).mp hmain

lemma rectangular_norm_range (M : CStarMatrix m n A) :
    ‖M*M.conjTranspose‖ = ‖M‖^2 := by
  apply le_antisymm _ (rectangular_norm_sq_le_range M)
  simpa only [rectangular_norm_conjTranspose, pow_two] using
    rectangular_norm_mul_le M M.conjTranspose

lemma rectangular_norm_initial (M : CStarMatrix m n A) :
    ‖M.conjTranspose*M‖ = ‖M‖^2 := by
  simpa only [rectangular_conjTranspose_conjTranspose, rectangular_norm_conjTranspose] using
    rectangular_norm_range M.conjTranspose

lemma rectangular_initial_nonneg (M : CStarMatrix m n A) : 0 ≤ M.conjTranspose*M := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have : M.conjTranspose*M = 0 := by ext i j; exact hn.false i |>.elim
    rw [this]
  | inr hn =>
    let i₀ : n := Classical.choice hn
    let R (i : m) : CStarMatrix n n A := fun j k => if j = i₀ then M i k else 0
    have hrows (T : m → n → A) :
        Matrix.conjTranspose (Matrix.of T) * Matrix.of T = ∑ i : m,
          Matrix.conjTranspose (Matrix.of (fun j k : n => if j = i₀ then T i k else 0)) *
            Matrix.of (fun j k : n => if j = i₀ then T i k else 0) := by
      ext j k
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.of_apply]
      simp
    have he : M.conjTranspose*M = ∑ i : m, star (R i)*R i :=
      hrows (Matrix.of.symm (CStarMatrix.ofMatrix.symm M))
    rw [he]
    exact Finset.sum_nonneg (fun i _ => star_mul_self_nonneg (R i))


end WeakPureInfiniteness

end

end OAI
