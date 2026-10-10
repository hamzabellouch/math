import Mathlib
import OAI.Probability.SKRatio.Matrices.OpNormKernelMatrixSub
import OAI.Probability.SKRatio.Matrices.TruncatedG

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
noncomputable section
open Set Real
open scoped Topology
namespace SKRatioGaussian.ComplexMatrix
open scoped SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fl1 (f : 𝓢(ℝ,ℂ)) : ℝ := 2*Real.pi*fourierMoment f 1
def fl2 (f : 𝓢(ℝ,ℂ)) : ℝ := (2*Real.pi)^2*fourierMoment f 2
lemma fl_nonneg (f : 𝓢(ℝ,ℂ)) : 0 ≤ fl1 f ∧ 0 ≤ fl2 f := by
  have h₁ := fourierMoment_nonneg f 1
  have h₂ := fourierMoment_nonneg f 2
  unfold fl1 fl2
  constructor <;> positivity

def diagonalChange (D D' : Matrix ι ι ℂ) : ℝ :=
  (opNorm D+opNorm D')*opNorm (D-D')
def shiftChange (R : ℝ) (B B' D D' : Matrix ι ι ℂ) : ℝ :=
  opNorm (B-B')+diagonalChange D D'*R
def gBound (f : 𝓢(ℝ,ℂ)) (D : Matrix ι ι ℂ) : ℝ :=
  opNorm D^2*fourierMoment f 0
def gLip (f : 𝓢(ℝ,ℂ)) (D : Matrix ι ι ℂ) : ℝ :=
  fl1 f*opNorm D^4
def gChange (f : 𝓢(ℝ,ℂ)) (R : ℝ) (B B' D D' : Matrix ι ι ℂ) : ℝ :=
  diagonalChange D D'*fourierMoment f 0+opNorm D'^2*fl1 f*shiftChange R B B' D D'
def gMixed (f : 𝓢(ℝ,ℂ)) (R : ℝ) (B B' D D' : Matrix ι ι ℂ) : ℝ :=
  diagonalChange D D'*fl1 f*opNorm D^2+
  opNorm D'^2*(fl1 f*diagonalChange D D'+fl2 f*(2*shiftChange R B B' D D')*opNorm D'^2)

lemma diagonalChange_nonneg (D D' : Matrix ι ι ℂ) : 0 ≤ diagonalChange D D' := by
  unfold diagonalChange
  positivity [opNorm_nonneg D,opNorm_nonneg D',opNorm_nonneg (D-D')]
lemma shiftChange_nonneg {R : ℝ} (hR : 0 ≤ R) (B B' D D' : Matrix ι ι ℂ) :
    0 ≤ shiftChange R B B' D D' := by
  unfold shiftChange
  positivity [opNorm_nonneg (B-B'),diagonalChange_nonneg D D']
lemma g_constants_nonneg (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B B' D D' : Matrix ι ι ℂ) :
    0 ≤ gBound f D ∧ 0 ≤ gLip f D ∧ 0 ≤ gChange f R B B' D D' ∧ 0 ≤ gMixed f R B B' D D' := by
  have h₀ := fourierMoment_nonneg f 0
  have h₁ := (fl_nonneg f).1
  have h₂ := (fl_nonneg f).2
  have hd := diagonalChange_nonneg D D'
  have hs := shiftChange_nonneg hR B B' D D'
  unfold gBound gLip gChange gMixed
  exact ⟨by positivity,by positivity,by positivity,by positivity⟩

lemma truncatedG_parameter (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B B' D D' M : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hB' : B'ᴴ = B') (hD : Dᴴ = D) (hD' : D'ᴴ = D') :
    opNorm (truncatedG f R hR B D M-truncatedG f R hR B' D' M) ≤
      gChange f R B B' D D' := by
  let P := matrixProject R hR M
  let F := schwartzMatrix f (sandShift B D P)
  let F' := schwartzMatrix f (sandShift B' D' P)
  have hP := matrixProject_bound R hR M
  have hF : opNorm F ≤ fourierMoment f 0 := by
    simpa only [F,fourierMoment,pow_zero,mul_one] using
      schwartzMatrix_opNorm f _ (sandShift_hermitian _ _ _ hB hD hP.1)
  have hs : opNorm (sandShift B D P-sandShift B' D' P) ≤ shiftChange R B B' D D' := by
    apply (sandShift_parameter B B' D D' P).trans
    unfold shiftChange diagonalChange
    exact add_le_add_right (mul_le_mul_of_nonneg_left hP.2 (diagonalChange_nonneg D D')) _
  have hL : opNorm (F-F') ≤ fl1 f*shiftChange R B B' D D' :=
    (schwartzMatrix_opNorm_lipschitz f _ _ (sandShift_hermitian _ _ _ hB hD hP.1)
      (sandShift_hermitian _ _ _ hB' hD' hP.1)).trans
      (mul_le_mul_of_nonneg_left hs (fl_nonneg f).1)
  have he : truncatedG f R hR B D M-truncatedG f R hR B' D' M =
      (D*F*D-D'*F*D')+D'*(F-F')*D' := by dsimp [truncatedG,F,F',P]; noncomm_ring
  rw [he]
  calc
    _ ≤ opNorm (D*F*D-D'*F*D')+opNorm (D'*(F-F')*D') := opNorm_add _ _
    _ ≤ diagonalChange D D'*opNorm F+opNorm D'^2*opNorm (F-F') :=
      add_le_add (sandwich_difference_opNorm _ _ _) (sandwich_opNorm _ _)
    _ ≤ diagonalChange D D'*fourierMoment f 0+opNorm D'^2*(fl1 f*shiftChange R B B' D D') :=
      add_le_add (mul_le_mul_of_nonneg_left hF (diagonalChange_nonneg _ _))
        (mul_le_mul_of_nonneg_left hL (sq_nonneg _))
    _ = _ := by unfold gChange; ring

lemma truncatedG_four_point (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B B' D D' M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hB' : B'ᴴ = B') (hD : Dᴴ = D) (hD' : D'ᴴ = D') :
    ‖(truncatedG f R hR B D M-truncatedG f R hR B D N)-
      (truncatedG f R hR B' D' M-truncatedG f R hR B' D' N)‖ ≤
      gMixed f R B B' D D'*‖M-N‖ := by
  let P := matrixProject R hR M
  let Q := matrixProject R hR N
  let F := schwartzMatrix f (sandShift B D P)-schwartzMatrix f (sandShift B D Q)
  let F' := schwartzMatrix f (sandShift B' D' P)-schwartzMatrix f (sandShift B' D' Q)
  have hP := matrixProject_bound R hR M
  have hQ := matrixProject_bound R hR N
  have hPQ : ‖P-Q‖ ≤ ‖M-N‖ := matrixProject_sub_norm _ _ _ _
  have hF : ‖F‖ ≤ fl1 f*opNorm D^2*‖M-N‖ :=
    (schwartzMatrix_sandShift_lipschitz f B D P Q hB hD hP.1 hQ.1).trans
      (mul_le_mul_of_nonneg_left hPQ (mul_nonneg (fl_nonneg f).1 (sq_nonneg _)))
  have hFF : ‖F-F'‖ ≤
      (fl1 f*diagonalChange D D'+fl2 f*(2*shiftChange R B B' D D')*opNorm D'^2)*‖M-N‖ := by
    apply (schwartzMatrix_sandShift_four_point f B B' D D' P Q hB hB' hD hD' hP.1 hQ.1).trans
    simp only [mul_assoc (2*Real.pi*fourierMoment f 1) (opNorm D+opNorm D')]
    change (fl1 f*diagonalChange D D'+fl2 f*
      (2*opNorm (B-B')+diagonalChange D D'*(opNorm P+opNorm Q))*opNorm D'^2)*‖P-Q‖ ≤ _
    have hd := diagonalChange_nonneg D D'
    have hs := shiftChange_nonneg hR B B' D D'
    have hc : 2*opNorm (B-B')+diagonalChange D D'*(opNorm P+opNorm Q) ≤
        2*shiftChange R B B' D D' := by
      calc
        _ ≤ 2*opNorm (B-B')+diagonalChange D D'*(R+R) :=
          add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add hP.2 hQ.2) hd) _
        _ = _ := by unfold shiftChange; ring
    have hc' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (fl_nonneg f).2) (sq_nonneg (opNorm D'))
    have hcoef := add_le_add_right hc' (fl1 f*diagonalChange D D')
    have hn : 0 ≤ fl1 f*diagonalChange D D'+fl2 f*(2*shiftChange R B B' D D')*opNorm D'^2 :=
      add_nonneg (mul_nonneg (fl_nonneg f).1 hd)
        (mul_nonneg (mul_nonneg (fl_nonneg f).2 (mul_nonneg (by norm_num) hs)) (sq_nonneg _))
    exact mul_le_mul hcoef hPQ (norm_nonneg _) hn
  have he : (truncatedG f R hR B D M-truncatedG f R hR B D N)-
      (truncatedG f R hR B' D' M-truncatedG f R hR B' D' N) =
      (D*F*D-D'*F*D')+D'*(F-F')*D' := by dsimp [truncatedG,F,F',P,Q]; noncomm_ring
  rw [he]
  calc
    _ ≤ ‖D*F*D-D'*F*D'‖+‖D'*(F-F')*D'‖ := norm_add_le _ _
    _ ≤ diagonalChange D D'*‖F‖+opNorm D'^2*‖F-F'‖ :=
      add_le_add (sandwich_difference_frobenius _ _ _) (sandwich_frobenius _ _)
    _ ≤ diagonalChange D D'*(fl1 f*opNorm D^2*‖M-N‖)+opNorm D'^2*
        ((fl1 f*diagonalChange D D'+fl2 f*(2*shiftChange R B B' D D')*opNorm D'^2)*‖M-N‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hF (diagonalChange_nonneg _ _))
        (mul_le_mul_of_nonneg_left hFF (sq_nonneg _))
    _ = _ := by unfold gMixed; ring

noncomputable def truncatedK (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (B D C M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  1+truncatedG f R hR B D M*(matrixProject R hR M-C)

def kBound (f : 𝓢(ℝ,ℂ)) (R : ℝ) (D C : Matrix ι ι ℂ) : ℝ :=
  1+gBound f D*(R+opNorm C)
def kLip (f : 𝓢(ℝ,ℂ)) (R : ℝ) (D C : Matrix ι ι ℂ) : ℝ :=
  gLip f D*(R+opNorm C)+gBound f D
def kMixed (f : 𝓢(ℝ,ℂ)) (R : ℝ) (B B' D D' C C' : Matrix ι ι ℂ) : ℝ :=
  gMixed f R B B' D D'*(R+opNorm C)+gLip f D'*opNorm (C-C')+gChange f R B B' D D'

lemma projected_sub_bound {R : ℝ} (hR : 0 ≤ R) (M C : Matrix ι ι ℂ) :
    opNorm (matrixProject R hR M-C) ≤ R+opNorm C :=
  (opNorm_sub _ _).trans (add_le_add_left (matrixProject_bound R hR M).2 _)

lemma truncatedK_opNorm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B D C M : Matrix ι ι ℂ) (hB : Bᴴ = B) (hD : Dᴴ = D) :
    opNorm (truncatedK f R hR B D C M) ≤ kBound f R D C := by
  apply (opNorm_add _ _).trans
  apply add_le_add opNorm_one_le
  exact (opNorm_mul _ _).trans
    (mul_le_mul (truncatedG_opNorm _ _ _ _ _ _ hB hD) (projected_sub_bound hR M C)
      (opNorm_nonneg _) (g_constants_nonneg f hR B B D D).1)

lemma truncatedK_sub_norm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B D C M N : Matrix ι ι ℂ) (hB : Bᴴ = B) (hD : Dᴴ = D) :
    ‖truncatedK f R hR B D C M-truncatedK f R hR B D C N‖ ≤
      kLip f R D C*‖M-N‖ := by
  let G := truncatedG f R hR B D
  let P : Matrix ι ι ℂ → Matrix ι ι ℂ := matrixProject R hR
  have he : truncatedK f R hR B D C M-truncatedK f R hR B D C N =
      (G M-G N)*(P M-C)+G N*(P M-P N) := by dsimp [truncatedK,G,P]; noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(G M-G N)*(P M-C)‖+‖G N*(P M-P N)‖ := norm_add_le _ _
    _ ≤ ‖G M-G N‖*opNorm (P M-C)+opNorm (G N)*‖P M-P N‖ :=
      add_le_add (frobenius_mul_le_opNorm_right _ _) (frobenius_mul_le_opNorm _ _)
    _ ≤ (gLip f D*‖M-N‖)*(R+opNorm C)+gBound f D*‖M-N‖ := by
      apply add_le_add
      · exact mul_le_mul (truncatedG_sub_norm _ _ _ _ _ _ _ hB hD) (projected_sub_bound hR M C)
          (opNorm_nonneg _) (mul_nonneg (g_constants_nonneg f hR B B D D).2.1 (norm_nonneg _))
      · exact mul_le_mul (truncatedG_opNorm _ _ _ _ _ _ hB hD) (matrixProject_sub_norm _ _ _ _)
          (norm_nonneg _) (g_constants_nonneg f hR B B D D).1
    _ = _ := by unfold kLip; ring

lemma truncatedK_four_point (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B B' D D' C C' M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hB' : B'ᴴ = B') (hD : Dᴴ = D) (hD' : D'ᴴ = D') :
    ‖(truncatedK f R hR B D C M-truncatedK f R hR B D C N)-
      (truncatedK f R hR B' D' C' M-truncatedK f R hR B' D' C' N)‖ ≤
      kMixed f R B B' D D' C C'*‖M-N‖ := by
  let G := truncatedG f R hR B D
  let G' := truncatedG f R hR B' D'
  let P : Matrix ι ι ℂ → Matrix ι ι ℂ := matrixProject R hR
  have he : (truncatedK f R hR B D C M-truncatedK f R hR B D C N)-
      (truncatedK f R hR B' D' C' M-truncatedK f R hR B' D' C' N) =
      (G M*(P M-C)-G N*(P N-C))-(G' M*(P M-C')-G' N*(P N-C')) := by
    dsimp [truncatedK,G,G',P]; abel
  rw [he]
  have h₁ : (P M-C)-(P M-C') = -(C-C') := by abel
  have h₂ : (P M-C)-(P N-C) = P M-P N := by abel
  have h₃ : ((P M-C)-(P N-C))-((P M-C')-(P N-C')) = 0 := by abel
  have hh := product_four_point (G M) (G N) (G' M) (G' N) (P M-C) (P N-C) (P M-C') (P N-C')
  rw [h₃,h₁,h₂,opNorm_neg,norm_zero,mul_zero,add_zero] at hh
  apply hh.trans
  calc
    _ ≤ (gMixed f R B B' D D'*‖M-N‖)*(R+opNorm C)+
        (gLip f D'*‖M-N‖)*opNorm (C-C')+gChange f R B B' D D'*‖M-N‖ := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul (truncatedG_four_point f hR B B' D D' M N hB hB' hD hD')
            (projected_sub_bound hR M C) (opNorm_nonneg _)
            (mul_nonneg (g_constants_nonneg f hR B B' D D').2.2.2 (norm_nonneg _))
        · exact mul_le_mul_of_nonneg_right (truncatedG_sub_norm _ _ _ _ _ _ _ hB' hD') (opNorm_nonneg _)
      · exact mul_le_mul (truncatedG_parameter f hR B B' D D' N hB hB' hD hD')
          (matrixProject_sub_norm _ _ _ _) (norm_nonneg _)
          (g_constants_nonneg f hR B B' D D').2.2.1
    _ = _ := by unfold kMixed; ring

end SKRatioGaussian.ComplexMatrix

noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius

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
end

end OAI
