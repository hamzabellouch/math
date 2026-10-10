import Mathlib
import OAI.Probability.SKGap.Matrix.OpNormKernelMatrixSub

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sandShift (B D M : Matrix ι ι ℂ) : Matrix ι ι ℂ := B-D*M*D

omit [DecidableEq ι] in
lemma sandShift_hermitian (B D M : Matrix ι ι ℂ) (hB : Bᴴ = B) (hD : Dᴴ = D) (hM : Mᴴ = M) :
    (sandShift B D M)ᴴ = sandShift B D M := by
  simp [sandShift,Matrix.conjTranspose_mul,hB,hD,hM,mul_assoc]

lemma sandShift_sub (B D M N : Matrix ι ι ℂ) :
    sandShift B D M-sandShift B D N = -(D*(M-N)*D) := by dsimp [sandShift]; noncomm_ring

lemma sandShift_lipschitz (B D M N : Matrix ι ι ℂ) :
    ‖sandShift B D M-sandShift B D N‖ ≤ opNorm D^2*‖M-N‖ := by
  rw [sandShift_sub,norm_neg]
  exact sandwich_frobenius _ _

lemma sandShift_parameter (B B' D D' M : Matrix ι ι ℂ) :
    opNorm (sandShift B D M-sandShift B' D' M) ≤
      opNorm (B-B')+(opNorm D+opNorm D')*opNorm (D-D')*opNorm M := by
  have he : sandShift B D M-sandShift B' D' M = (B-B')-(D*M*D-D'*M*D') := by dsimp [sandShift]; abel
  rw [he]
  calc
    _ ≤ opNorm (B-B')+opNorm (D*M*D-D'*M*D') := opNorm_sub (B-B') (D*M*D-D'*M*D')
    _ ≤ _ := by
      have hh := sandwich_difference_opNorm D D' M
      linarith only [hh]

lemma sandShift_four_point (B B' D D' M N : Matrix ι ι ℂ) :
    ‖(sandShift B D M-sandShift B D N)-(sandShift B' D' M-sandShift B' D' N)‖ ≤
      (opNorm D+opNorm D')*opNorm (D-D')*‖M-N‖ := by
  rw [sandShift_sub,sandShift_sub,← norm_neg]
  have he : -(-(D*(M-N)*D)- -(D'*(M-N)*D')) = D*(M-N)*D-D'*(M-N)*D' := by abel
  rw [he]
  exact sandwich_difference_frobenius _ _ _

lemma schwartzMatrix_sandShift_lipschitz (f : 𝓢(ℝ,ℂ)) (B D M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hD : Dᴴ = D) (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖schwartzMatrix f (sandShift B D M)-schwartzMatrix f (sandShift B D N)‖ ≤
      (2*Real.pi*fourierMoment f 1)*opNorm D^2*‖M-N‖ := by
  exact (schwartzMatrix_lipschitz f _ _ (sandShift_hermitian _ _ _ hB hD hM)
    (sandShift_hermitian _ _ _ hB hD hN)).trans
    ((mul_le_mul_of_nonneg_left (sandShift_lipschitz B D M N)
      (by positivity [fourierMoment_nonneg f 1])).trans_eq (by ring))

lemma schwartzMatrix_sandShift_four_point (f : 𝓢(ℝ,ℂ)) (B B' D D' M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hB' : B'ᴴ = B') (hD : Dᴴ = D) (hD' : D'ᴴ = D')
    (hM : Mᴴ = M) (hN : Nᴴ = N) :
    ‖(schwartzMatrix f (sandShift B D M)-schwartzMatrix f (sandShift B D N))-
      (schwartzMatrix f (sandShift B' D' M)-schwartzMatrix f (sandShift B' D' N))‖ ≤
      ((2*Real.pi*fourierMoment f 1)*(opNorm D+opNorm D')*opNorm (D-D')+
        ((2*Real.pi)^2*fourierMoment f 2)*
          (2*opNorm (B-B')+(opNorm D+opNorm D')*opNorm (D-D')*(opNorm M+opNorm N))*opNorm D'^2)*‖M-N‖ := by
  have hL : 0 ≤ 2*Real.pi*fourierMoment f 1 := by have := fourierMoment_nonneg f 1; positivity
  have hQ : 0 ≤ (2*Real.pi)^2*fourierMoment f 2 := by have := fourierMoment_nonneg f 2; positivity
  have hP : 0 ≤ (opNorm D+opNorm D')*opNorm (D-D') :=
    mul_nonneg (add_nonneg (opNorm_nonneg _) (opNorm_nonneg _)) (opNorm_nonneg _)
  have hp := add_le_add (sandShift_parameter B B' D D' M) (sandShift_parameter B B' D D' N)
  have hp' : opNorm (sandShift B D M-sandShift B' D' M)+opNorm (sandShift B D N-sandShift B' D' N) ≤
      2*opNorm (B-B')+(opNorm D+opNorm D')*opNorm (D-D')*(opNorm M+opNorm N) := by nlinarith only [hp]
  have hx := schwartzMatrix_four_point f (sandShift B D M) (sandShift B D N) (sandShift B' D' M) (sandShift B' D' N)
    (sandShift_hermitian _ _ _ hB hD hM) (sandShift_hermitian _ _ _ hB hD hN)
    (sandShift_hermitian _ _ _ hB' hD' hM) (sandShift_hermitian _ _ _ hB' hD' hN)
  apply hx.trans
  calc
    _ ≤ (2*Real.pi*fourierMoment f 1)*((opNorm D+opNorm D')*opNorm (D-D')*‖M-N‖)+
      ((2*Real.pi)^2*fourierMoment f 2)*
        (2*opNorm (B-B')+(opNorm D+opNorm D')*opNorm (D-D')*(opNorm M+opNorm N))*(opNorm D'^2*‖M-N‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (sandShift_four_point _ _ _ _ _ _) hL
      · apply mul_le_mul (mul_le_mul_of_nonneg_left hp' hQ) (sandShift_lipschitz B' D' M N) (norm_nonneg _)
        exact mul_nonneg hQ (add_nonneg (mul_nonneg (by norm_num) (opNorm_nonneg _))
          (mul_nonneg hP (add_nonneg (opNorm_nonneg _) (opNorm_nonneg _))))
    _ = _ := by ring

end SKGap.ComplexMatrix

noncomputable section
open Set Real
open scoped Topology
namespace SKGap
section Projection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure ClosedConvexNonempty (K : Set E) : Prop where
  nonempty : K.Nonempty
  complete : IsComplete K
  convex : Convex ℝ K

noncomputable def convexProject {K : Set E} (hK : ClosedConvexNonempty K) (x : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hK.nonempty hK.complete hK.convex x)

lemma convexProject_mem {K : Set E} (hK : ClosedConvexNonempty K) (x : E) :
    convexProject hK x ∈ K :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hK.nonempty hK.complete hK.convex x)).1

lemma convexProject_minimal {K : Set E} (hK : ClosedConvexNonempty K) (x : E) :
    ‖x-convexProject hK x‖ = ⨅ y : K, ‖x-y‖ :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hK.nonempty hK.complete hK.convex x)).2

lemma convexProject_inner {K : Set E} (hK : ClosedConvexNonempty K) (x : E)
    {y : E} (hy : y ∈ K) :
    inner ℝ (x-convexProject hK x) (y-convexProject hK x) ≤ 0 := by
  exact ((norm_eq_iInf_iff_real_inner_le_zero hK.convex (convexProject_mem hK x)).mp
    (convexProject_minimal hK x)) y hy

lemma convexProject_lipschitz {K : Set E} (hK : ClosedConvexNonempty K) :
    LipschitzWith 1 (convexProject hK) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  let p := convexProject hK x
  let q := convexProject hK y
  have hx := convexProject_inner hK x (convexProject_mem hK y)
  have hy := convexProject_inner hK y (convexProject_mem hK x)
  change inner ℝ (x-p) (q-p) ≤ 0 at hx
  change inner ℝ (y-q) (p-q) ≤ 0 at hy
  have hi : ‖p-q‖^2 ≤ inner ℝ (p-q) (x-y) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left,inner_sub_right,real_inner_comm] at *
    nlinarith
  have hb := real_inner_le_norm (p-q) (x-y)
  nlinarith [norm_nonneg (p-q),norm_nonneg (x-y)]

lemma convexProject_eq_self {K : Set E} (hK : ClosedConvexNonempty K) {x : E}
    (hx : x ∈ K) : convexProject hK x = x := by
  have hh := convexProject_inner hK x hx
  rw [real_inner_self_eq_norm_sq] at hh
  have hz : ‖x-convexProject hK x‖ = 0 := by nlinarith [norm_nonneg (x-convexProject hK x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

lemma convexProject_unique {K : Set E} (hK : ClosedConvexNonempty K) {x p : E}
    (hp : p ∈ K) (hmin : ∀ y ∈ K, inner ℝ (x-p) (y-p) ≤ 0) :
    p = convexProject hK x := by
  let q := convexProject hK x
  have h₁ := hmin q (convexProject_mem hK x)
  have h₂ := convexProject_inner hK x hp
  change inner ℝ (x-q) (p-q) ≤ 0 at h₂
  have hh : ‖p-q‖^2 ≤ 0 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_right,inner_sub_left,real_inner_comm] at *
    nlinarith
  have hz : ‖p-q‖ = 0 := by nlinarith [norm_nonneg (p-q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma convexProject_equivariant {K : Set E} (hK : ClosedConvexNonempty K)
    (U : E ≃ₗᵢ[ℝ] E) (hU : ∀ x, U x ∈ K ↔ x ∈ K) (x : E) :
    convexProject hK (U x) = U (convexProject hK x) := by
  apply Eq.symm
  apply convexProject_unique hK ((hU _).mpr (convexProject_mem hK x))
  intro y hy
  have hy' : U.symm y ∈ K := (hU _).mp (by simpa using hy)
  have hh := convexProject_inner hK x hy'
  rw [← U.inner_map_map] at hh
  simpa only [map_sub,LinearIsometryEquiv.apply_symm_apply] using hh

end Projection
end SKGap

end
end
end
end
end
end
end
end
end

end OAI
