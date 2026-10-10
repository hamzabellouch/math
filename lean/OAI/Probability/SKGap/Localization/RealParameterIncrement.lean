import Mathlib
import OAI.Probability.SKGap.Localization.RealPart

namespace OAI

section
noncomputable section
open Matrix Real Set
open scoped Matrix.Norms.Frobenius SchwartzMap
namespace SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def kChange (f : 𝓢(ℝ,ℂ)) (R : ℝ) (B B' D D' C C' : Matrix ι ι ℂ) : ℝ :=
  gChange f R B B' D D'*(R+opNorm C)+gBound f D'*opNorm (C-C')
lemma kChange_nonneg (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R)
    (B B' D D' C C' : Matrix ι ι ℂ) : 0≤kChange f R B B' D D' C C' := by
  have hh := g_constants_nonneg f hR B B' D D'
  have hh' := (g_constants_nonneg f hR B B' D' D').1
  unfold kChange
  exact add_nonneg (mul_nonneg hh.2.2.1 (add_nonneg hR (opNorm_nonneg C)))
    (mul_nonneg hh' (opNorm_nonneg (C-C')))
lemma kMixed_nonneg (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R)
    (B B' D D' C C' : Matrix ι ι ℂ) : 0≤kMixed f R B B' D D' C C' := by
  have hh := g_constants_nonneg f hR B B' D D'
  have hh' := (g_constants_nonneg f hR B B' D' D').2.1
  unfold kMixed
  exact add_nonneg (add_nonneg (mul_nonneg hh.2.2.2 (add_nonneg hR (opNorm_nonneg C)))
    (mul_nonneg hh' (opNorm_nonneg (C-C')))) hh.2.2.1
lemma truncatedK_parameter (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R)
    (B B' D D' C C' M : Matrix ι ι ℂ)
    (hB : Bᴴ=B) (hB' : B'ᴴ=B') (hD : Dᴴ=D) (hD' : D'ᴴ=D') :
    opNorm (truncatedK f R hR B D C M-truncatedK f R hR B' D' C' M)≤
      kChange f R B B' D D' C C' := by
  have he : truncatedK f R hR B D C M-truncatedK f R hR B' D' C' M=
    (truncatedG f R hR B D M-truncatedG f R hR B' D' M)*(matrixProject R hR M-C)+
      truncatedG f R hR B' D' M*(C'-C) := by unfold truncatedK;noncomm_ring
  rw [he]
  apply (opNorm_add _ _).trans
  apply (add_le_add (opNorm_mul _ _) (opNorm_mul _ _)).trans
  have h1 := mul_le_mul (truncatedG_parameter f hR B B' D D' M hB hB' hD hD')
    (projected_sub_bound hR M C) (opNorm_nonneg _) (g_constants_nonneg f hR B B' D D').2.2.1
  have h2 := mul_le_mul_of_nonneg_right (truncatedG_opNorm f R hR B' D' M hB' hD')
    (opNorm_nonneg (C'-C))
  have hs : opNorm (C'-C)=opNorm (C-C') := by rw [← neg_sub C C',opNorm_neg]
  rw [hs] at h2
  simpa only [kChange,hs,gBound] using add_le_add h1 h2
end SKGap.ComplexMatrix
namespace SKGap.RealComplex
open SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma liftedSand_hermitian (D C : Matrix ι ι ℝ) (hD : Dᵀ=D) (hC : Cᵀ=C) :
    (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ=1+liftMatrix D*liftMatrix C*liftMatrix D := by
  simp [Matrix.conjTranspose_mul,liftMatrix_hermitian D hD,liftMatrix_hermitian C hC,mul_assoc]
lemma realTruncatedK_parameter (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R)
    (D D' C C' M : Matrix ι ι ℝ) (hD : Dᵀ=D) (hD' : D'ᵀ=D') (hC : Cᵀ=C) (hC' : C'ᵀ=C') :
    SKGap.opNorm (realTruncatedK f R hR D C M-realTruncatedK f R hR D' C' M)≤
      kChange f R (1+liftMatrix D*liftMatrix C*liftMatrix D)
        (1+liftMatrix D'*liftMatrix C'*liftMatrix D') (liftMatrix D) (liftMatrix D') (liftMatrix C) (liftMatrix C') := by
  unfold realTruncatedK
  rw [← realPart_sub]
  exact (operator_realPart_le _).trans (truncatedK_parameter f hR _ _ _ _ _ _ _
    (liftedSand_hermitian D C hD hC) (liftedSand_hermitian D' C' hD' hC')
    (liftMatrix_hermitian D hD) (liftMatrix_hermitian D' hD'))

lemma realTruncatedK_four_point (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R)
    (D D' C C' M N : Matrix ι ι ℝ) (hD : Dᵀ=D) (hD' : D'ᵀ=D') (hC : Cᵀ=C) (hC' : C'ᵀ=C') :
    ‖(realTruncatedK f R hR D C M-realTruncatedK f R hR D C N)-
      (realTruncatedK f R hR D' C' M-realTruncatedK f R hR D' C' N)‖≤
      kMixed f R (1+liftMatrix D*liftMatrix C*liftMatrix D)
        (1+liftMatrix D'*liftMatrix C'*liftMatrix D') (liftMatrix D) (liftMatrix D') (liftMatrix C) (liftMatrix C')*‖M-N‖ := by
  unfold realTruncatedK
  rw [← realPart_sub,← realPart_sub,← realPart_sub]
  apply (norm_realPart_le _).trans
  simpa only [← liftMatrix_sub,norm_liftMatrix] using! truncatedK_four_point f hR _ _ _ _ _ _
    (liftMatrix M) (liftMatrix N) (liftedSand_hermitian D C hD hC)
    (liftedSand_hermitian D' C' hD' hC') (liftMatrix_hermitian D hD) (liftMatrix_hermitian D' hD')
end SKGap.RealComplex
end
end

section
noncomputable section
namespace SKGap.ComplexMatrix
open Matrix Real
open scoped Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def parameterGC (f : 𝓢(ℝ,ℂ)) (R V H : ℝ) : ℝ :=
  2*V*fourierMoment f 0+V^2*fl1 f*(H+2*V*R)
def parameterGM (f : 𝓢(ℝ,ℂ)) (R V H : ℝ) : ℝ :=
  2*V*fl1 f*V^2+V^2*(fl1 f*(2*V)+fl2 f*(2*(H+2*V*R))*V^2)
def parameterKC (f : 𝓢(ℝ,ℂ)) (R V T H : ℝ) : ℝ :=
  parameterGC f R V H*(R+T)+V^2*fourierMoment f 0
def parameterKM (f : 𝓢(ℝ,ℂ)) (R V T H : ℝ) : ℝ :=
  parameterGM f R V H*(R+T)+fl1 f*V^4+parameterGC f R V H

theorem cutoff_parameter_constants (f : 𝓢(ℝ,ℂ))
    {R V T H δ : ℝ} (hR : 0≤R) (hV : 0≤V) (_hT : 0≤T) (hH : 0≤H) (hδ : 0≤δ)
    (B B' D D' C C' : Matrix ι ι ℂ)
    (hD : opNorm D≤V) (hD' : opNorm D'≤V) (hC : opNorm C≤T)
    (hBD : opNorm (B-B')≤H*δ) (hDD : opNorm (D-D')≤δ) (hCD : opNorm (C-C')≤δ) :
    kChange f R B B' D D' C C'≤parameterKC f R V T H*δ ∧
    kMixed f R B B' D D' C C'≤parameterKM f R V T H*δ := by
  have hf0 := fourierMoment_nonneg f 0
  obtain ⟨hf1,hf2⟩ := fl_nonneg f
  have hDC : diagonalChange D D'≤(2*V)*δ := by
    unfold diagonalChange
    exact mul_le_mul (by linarith) hDD (opNorm_nonneg _) (by positivity)
  have hSC : shiftChange R B B' D D'≤(H+2*V*R)*δ := by
    unfold shiftChange
    have hh := add_le_add hBD (mul_le_mul_of_nonneg_right hDC hR)
    nlinarith only [hh]
  have hGH : 0≤H+2*V*R := by positivity
  have hgc : gChange f R B B' D D'≤parameterGC f R V H*δ := by
    unfold gChange parameterGC
    calc
      _ ≤ ((2*V)*δ)*fourierMoment f 0+V^2*fl1 f*((H+2*V*R)*δ) := by
        apply add_le_add (mul_le_mul_of_nonneg_right hDC hf0)
        apply mul_le_mul _ hSC (shiftChange_nonneg hR _ _ _ _) (by positivity)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (opNorm_nonneg D') hD' 2) hf1
      _ = _ := by ring
  have hgm : gMixed f R B B' D D'≤parameterGM f R V H*δ := by
    unfold gMixed parameterGM
    calc
      _ ≤ ((2*V)*δ)*fl1 f*V^2+V^2*(fl1 f*((2*V)*δ)+fl2 f*(2*((H+2*V*R)*δ))*V^2) := by
        apply add_le_add
        · apply mul_le_mul _ (pow_le_pow_left₀ (opNorm_nonneg D) hD 2) (by positivity [fl_nonneg f]) (by positivity)
          exact mul_le_mul_of_nonneg_right hDC hf1
        · apply mul_le_mul (pow_le_pow_left₀ (opNorm_nonneg D') hD' 2) _ (by positivity [diagonalChange_nonneg D D',shiftChange_nonneg hR B B' D D']) (by positivity)
          apply add_le_add (mul_le_mul_of_nonneg_left hDC hf1)
          apply mul_le_mul _ (pow_le_pow_left₀ (opNorm_nonneg D') hD' 2) (by positivity [opNorm_nonneg D']) (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSC (by norm_num)) hf2
      _ = _ := by ring
  have hgc0 : 0≤parameterGC f R V H := by unfold parameterGC;positivity
  have hgm0 : 0≤parameterGM f R V H := by unfold parameterGM;positivity
  constructor
  · unfold kChange parameterKC
    calc
      _ ≤ (parameterGC f R V H*δ)*(R+T)+(V^2*fourierMoment f 0)*δ := by
        apply add_le_add
        · exact mul_le_mul hgc (add_le_add le_rfl hC) (by positivity [opNorm_nonneg C]) (by positivity)
        · exact mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (opNorm_nonneg D') hD' 2) hf0) hCD (opNorm_nonneg _) (by positivity)
      _ = _ := by ring
  · unfold kMixed parameterKM
    calc
      _ ≤ (parameterGM f R V H*δ)*(R+T)+(fl1 f*V^4)*δ+parameterGC f R V H*δ := by
        apply add_le_add _ hgc
        apply add_le_add
        · exact mul_le_mul hgm (add_le_add le_rfl hC) (by positivity [opNorm_nonneg C]) (by positivity)
        · exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (opNorm_nonneg D') hD' 4) hf1) hCD (opNorm_nonneg _) (by positivity)
      _ = _ := by ring
end SKGap.ComplexMatrix
end
end

end OAI
