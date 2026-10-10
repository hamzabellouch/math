import Mathlib
import OAI.Probability.SKRatio.Matrices.FourierMoment
import OAI.Probability.SKRatio.Matrices.OpNormNonneg

namespace OAI

section
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
namespace SKRatioGaussian.ComplexMatrix
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

end SKRatioGaussian.ComplexMatrix

noncomputable section
open Set Real
open scoped Topology

end
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
