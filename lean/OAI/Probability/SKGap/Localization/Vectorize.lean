import Mathlib
import OAI.Probability.SKGap.Localization.SandShift

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
noncomputable section
open Set Real
open scoped Topology
namespace SKGap.ComplexMatrix
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def vectorize : Matrix ι ι ℂ →ₗ[ℝ] EuclideanSpace ℂ (ι × ι) where
  toFun M := WithLp.toLp 2 (fun p => M p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma vectorize_norm (M : Matrix ι ι ℂ) : ‖vectorize M‖ = ‖M‖ := by
  have hh : ‖vectorize M‖^2 = ‖M‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,frobenius_sq]
    change (∑ p : ι × ι, ‖M p.1 p.2‖^2) = ∑ i, ∑ k, ‖M i k‖^2
    exact Fintype.sum_prod_type _
  nlinarith [norm_nonneg (vectorize M),norm_nonneg M]

noncomputable instance frobeniusInnerProduct : InnerProductSpace ℝ (Matrix ι ι ℂ) where
  inner M N := inner ℝ (vectorize M) (vectorize N)
  norm_sq_eq_re_inner M := by
    change ‖M‖^2 = inner ℝ (vectorize M) (vectorize M)
    rw [real_inner_self_eq_norm_sq,vectorize_norm]
  conj_inner_symm M N := by simp only [conj_trivial]; exact real_inner_comm _ _
  add_left M N P := by rw [map_add,inner_add_left]
  smul_left M N r := by rw [map_smul,inner_smul_left]

noncomputable def hermitianBall (R : ℝ) : Set (Matrix ι ι ℂ) :=
  {M | Mᴴ = M ∧ opNorm M ≤ R}

lemma hermitianBall_closed (R : ℝ) : IsClosed (hermitianBall (ι := ι) R) := by
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop : Continuous (fun M : Matrix ι ι ℂ => Mᴴ)) continuous_id
  · exact isClosed_le continuous_lin.norm continuous_const

lemma hermitianBall_convex (R : ℝ) : Convex ℝ (hermitianBall (ι := ι) R) := by
  intro M hM N hN a b ha hb hab
  constructor
  · simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,hM.1,hN.1,star_trivial]
  · have he : lin (a • M+b • N) = a • lin M+b • lin N := by
      exact (linEquiv (ι := ι)).toLinearMap.restrictScalars ℝ |>.map_add _ _ |>.trans
        (by rw [LinearMap.map_smul,LinearMap.map_smul]; rfl)
    change ‖lin (a • M+b • N)‖ ≤ R
    rw [he]
    calc
      _ ≤ ‖a • lin M‖+‖b • lin N‖ := norm_add_le _ _
      _ = a*opNorm M+b*opNorm N := by simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb,opNorm]
      _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hM.2 ha) (mul_le_mul_of_nonneg_left hN.2 hb)
      _ = R := by rw [← add_mul,hab,one_mul]

lemma hermitianBall_good {R : ℝ} (hR : 0 ≤ R) : SKGap.ClosedConvexNonempty (hermitianBall (ι := ι) R) where
  nonempty := ⟨0,by simp [hermitianBall,opNorm,lin,hR]⟩
  complete := (hermitianBall_closed R).isComplete
  convex := by convert hermitianBall_convex (ι := ι) R using 0

noncomputable def matrixProject (R : ℝ) (hR : 0 ≤ R) : Matrix ι ι ℂ → Matrix ι ι ℂ :=
  SKGap.convexProject (hermitianBall_good hR)

lemma matrixProject_lipschitz (R : ℝ) (hR : 0 ≤ R) :
    LipschitzWith 1 (matrixProject (ι := ι) R hR) :=
  SKGap.convexProject_lipschitz _

lemma matrixProject_bound (R : ℝ) (hR : 0 ≤ R) (M : Matrix ι ι ℂ) :
    (matrixProject R hR M)ᴴ = matrixProject R hR M ∧ opNorm (matrixProject R hR M) ≤ R :=
  SKGap.convexProject_mem (hermitianBall_good (ι := ι) hR) M

lemma matrixProject_eq_self (R : ℝ) (hR : 0 ≤ R) (M : Matrix ι ι ℂ)
    (hM : Mᴴ = M) (hMR : opNorm M ≤ R) : matrixProject R hR M = M :=
  SKGap.convexProject_eq_self _ ⟨hM,hMR⟩

end SKGap.ComplexMatrix

namespace SKGap.ComplexMatrix
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def truncatedG (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (B D M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  D*schwartzMatrix f (sandShift B D (matrixProject R hR M))*D

lemma matrixProject_sub_norm (R : ℝ) (hR : 0 ≤ R) (M N : Matrix ι ι ℂ) :
    ‖matrixProject R hR M-matrixProject R hR N‖ ≤ ‖M-N‖ := by
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using (matrixProject_lipschitz R hR).dist_le_mul M N

lemma truncatedG_opNorm (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (B D M : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hD : Dᴴ = D) :
    opNorm (truncatedG f R hR B D M) ≤ opNorm D^2*fourierMoment f 0 := by
  have hS := sandShift_hermitian B D (matrixProject R hR M) hB hD (matrixProject_bound R hR M).1
  apply (sandwich_opNorm D _).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  simpa only [fourierMoment,pow_zero,mul_one] using schwartzMatrix_opNorm f _ hS

lemma truncatedG_sub_norm (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (B D M N : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (hD : Dᴴ = D) :
    ‖truncatedG f R hR B D M-truncatedG f R hR B D N‖ ≤
      (2*Real.pi*fourierMoment f 1)*opNorm D^4*‖M-N‖ := by
  have hL : 0 ≤ 2*Real.pi*fourierMoment f 1 := by have := fourierMoment_nonneg f 1; positivity
  have hM := (matrixProject_bound R hR M).1
  have hN := (matrixProject_bound R hR N).1
  have hl := schwartzMatrix_sandShift_lipschitz f B D (matrixProject R hR M) (matrixProject R hR N) hB hD hM hN
  have he : truncatedG f R hR B D M-truncatedG f R hR B D N =
      D*(schwartzMatrix f (sandShift B D (matrixProject R hR M))-
        schwartzMatrix f (sandShift B D (matrixProject R hR N)))*D := by dsimp [truncatedG]; noncomm_ring
  rw [he]
  calc
    _ ≤ opNorm D^2*‖schwartzMatrix f (sandShift B D (matrixProject R hR M))-
        schwartzMatrix f (sandShift B D (matrixProject R hR N))‖ := sandwich_frobenius _ _
    _ ≤ opNorm D^2*((2*Real.pi*fourierMoment f 1)*opNorm D^2*‖matrixProject R hR M-matrixProject R hR N‖) :=
      mul_le_mul_of_nonneg_left hl (sq_nonneg _)
    _ ≤ opNorm D^2*((2*Real.pi*fourierMoment f 1)*opNorm D^2*‖M-N‖) := by
      gcongr
      exact matrixProject_sub_norm _ _ _ _
    _ = _ := by ring

lemma truncatedG_hermitian (f : 𝓢(ℝ,ℂ)) (hf : ∀ x, star (f x) = f x)
    (R : ℝ) (hR : 0 ≤ R) (B D M : Matrix ι ι ℂ) (hB : Bᴴ = B) (hD : Dᴴ = D) :
    (truncatedG f R hR B D M)ᴴ = truncatedG f R hR B D M := by
  have hs := schwartzMatrix_hermitian f hf (sandShift B D (matrixProject R hR M))
    (sandShift_hermitian B D (matrixProject R hR M) hB hD (matrixProject_bound R hR M).1)
  change (D*schwartzMatrix f (sandShift B D (matrixProject R hR M))*D)ᴴ = _
  simp only [Matrix.conjTranspose_mul,hD,hs.eq,truncatedG,mul_assoc]

lemma truncatedG_eq_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    (R : ℝ) (hR : 0 ≤ R) (B D M : Matrix ι ι ℂ) (hB : Bᴴ = B) (hD : Dᴴ = D)
    (hM : Mᴴ = M) (hMR : opNorm M ≤ R)
    (hspec : ∀ i, Matrix.IsHermitian.eigenvalues (sandShift_hermitian B D M hB hD hM) i ∈ Set.Icc lo hi) :
    truncatedG f R hR B D M = D*(sandShift B D M)⁻¹*D := by
  rw [truncatedG,matrixProject_eq_self R hR M hM hMR,
    schwartzMatrix_eq_inverse f hlo hf _ (sandShift_hermitian B D M hB hD hM) hspec]

end SKGap.ComplexMatrix

namespace SKGap.ComplexMatrix
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

end SKGap.ComplexMatrix

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

end OAI
