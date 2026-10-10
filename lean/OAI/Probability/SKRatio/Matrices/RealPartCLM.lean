import Mathlib
import OAI.Probability.SKRatio.Matrices.SandShiftSpecial
import OAI.Probability.SKRatio.Matrices.RealPart

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
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKRatioGaussian.RealComplex
open scoped Matrix.Norms.Frobenius SchwartzMap ComplexOrder
open SKRatioGaussian.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma liftMatrix_isUnit_iff (M : Matrix ι ι ℝ) : IsUnit (liftMatrix M) ↔ IsUnit M := by
  rw [(liftMatrix M).isUnit_iff_isUnit_det,M.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero,isUnit_iff_ne_zero]
  have he : (liftMatrix M).det = (M.det : ℂ) := (Complex.ofRealHom.map_det M).symm
  rw [he]
  exact not_congr Complex.ofReal_eq_zero

noncomputable def realPartCLM : Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℝ :=
  ({ toFun := realPart
     map_add' := by intros; ext; simp [realPart]
     map_smul' := by intros; ext; simp [realPart] } : Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℝ).mkContinuous
      1 (fun M => by simpa using norm_realPart_le M)

noncomputable def realTruncatedK (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (D C M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  realPart (truncatedK f R hR (1+liftMatrix D*liftMatrix C*liftMatrix D)
    (liftMatrix D) (liftMatrix C) (liftMatrix M))

lemma realTruncatedK_sub_norm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (D C M N : Matrix ι ι ℝ) (hD : Dᵀ = D) (hC : Cᵀ = C) :
    ‖realTruncatedK f R hR D C M-realTruncatedK f R hR D C N‖ ≤
      kLip f R (liftMatrix D) (liftMatrix C)*‖M-N‖ := by
  have hD' := liftMatrix_hermitian D hD
  have hC' := liftMatrix_hermitian C hC
  have hB : (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ =
      1+liftMatrix D*liftMatrix C*liftMatrix D := by simp [Matrix.conjTranspose_mul,hD',hC',mul_assoc]
  unfold realTruncatedK
  rw [← realPart_sub]
  apply (norm_realPart_le _).trans
  simpa only [← liftMatrix_sub,norm_liftMatrix] using
    truncatedK_sub_norm f hR _ _ _ (liftMatrix M) (liftMatrix N) hB hD'

lemma realTruncatedK_opNorm (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (D C M : Matrix ι ι ℝ) (hD : Dᵀ = D) (hC : Cᵀ = C) :
    SKRatioGaussian.opNorm (realTruncatedK f R hR D C M) ≤ kBound f R (liftMatrix D) (liftMatrix C) := by
  have hD' := liftMatrix_hermitian D hD
  have hC' := liftMatrix_hermitian C hC
  have hB : (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ =
      1+liftMatrix D*liftMatrix C*liftMatrix D := by simp [Matrix.conjTranspose_mul,hD',hC',mul_assoc]
  exact (operator_realPart_le _).trans (truncatedK_opNorm f hR _ _ _ _ hB hD')

lemma realTruncatedK_eq_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C M : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (hM : Mᵀ = M) (hMR : SKRatioGaussian.opNorm M ≤ R)
    (hl : lo ≤ SKRatioGaussian.ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(M-C)*D)))
    (hu : -hi ≤ SKRatioGaussian.ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(M-C)*D))) :
    realTruncatedK f R hR D C M = (1-D*D*(M-C))⁻¹ := by
  have hD' := liftMatrix_hermitian D hD
  have hC' := liftMatrix_hermitian C hC
  have hM' := liftMatrix_hermitian M hM
  have hB : (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ =
      1+liftMatrix D*liftMatrix C*liftMatrix D := by simp [Matrix.conjTranspose_mul,hD',hC',mul_assoc]
  have hid : sandShift (1+liftMatrix D*liftMatrix C*liftMatrix D) (liftMatrix D) (liftMatrix M) =
      liftMatrix (1-D*(M-C)*D) := by
    rw [sandShift_special]; simp only [liftMatrix_sub,liftMatrix_mul,liftMatrix_one]
  have hS : (sandShift (1+liftMatrix D*liftMatrix C*liftMatrix D) (liftMatrix D) (liftMatrix M)).IsHermitian :=
    sandShift_hermitian _ _ _ hB hD' hM'
  have hspec : ∀ i, hS.eigenvalues i ∈ Set.Icc lo hi := by
    intro i
    have hm := SKRatioGaussian.ComplexSpectral.eigenvalue_lower_bound hS i
    have hp := SKRatioGaussian.ComplexSpectral.eigenvalue_upper_bound hS i
    have hl' : lo ≤ SKRatioGaussian.ComplexSpectral.lowerRayleigh
        (sandShift (1+liftMatrix D*liftMatrix C*liftMatrix D) (liftMatrix D) (liftMatrix M)) := by
      simpa only [hid] using hl
    have hu' : -hi ≤ SKRatioGaussian.ComplexSpectral.lowerRayleigh
        (-sandShift (1+liftMatrix D*liftMatrix C*liftMatrix D) (liftMatrix D) (liftMatrix M)) := by
      simpa only [hid] using hu
    constructor <;> linarith
  have hsunit : IsUnit (1-liftMatrix D*(liftMatrix M-liftMatrix C)*liftMatrix D) := by
    rw [← sandShift_special]
    exact (hS.posDef_iff_eigenvalues_pos.mpr (fun i => hlo.trans_le (hspec i).1)).isUnit
  have hrunit : IsUnit (1-D*D*(M-C)) := by
    apply (liftMatrix_isUnit_iff _).mp
    simpa only [liftMatrix_sub,liftMatrix_mul,liftMatrix_one] using
      SKRatioGaussian.ResolventIdentity.inverse_one_sub_square_mul_unit (liftMatrix D) (liftMatrix M-liftMatrix C) hsunit
  unfold realTruncatedK
  rw [truncatedK_eq_inverse f hlo hf hR _ _ _ hD' hC' hM'
    (by simpa only [SKRatioGaussian.ComplexMatrix.opNorm,SKRatioGaussian.ComplexMatrix.lin,operator_norm_lift] using hMR) hspec]
  rw [← liftMatrix_one,← liftMatrix_mul,← liftMatrix_sub,← liftMatrix_mul,← liftMatrix_sub,
    ← liftMatrix_inverse hrunit,realPart_liftMatrix]

lemma real_matrix_hasDerivAt_inverse {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ} {t : ℝ}
    (hQ : HasDerivAt Q Q' t) (hunit : IsUnit (Q t)) :
    HasDerivAt (fun s => (Q s)⁻¹) (-(Q t)⁻¹*Q'*(Q t)⁻¹) t := by
  obtain ⟨u,hu⟩ := hunit
  have hfi := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hfi
  have hi := hfi.comp_hasDerivAt t hQ
  have hv : (↑u⁻¹ : Matrix ι ι ℝ) = (Q t)⁻¹ := by
    rw [← hu,Matrix.nonsing_inv_eq_ringInverse,Ring.inverse_unit]
  simpa only [Function.comp_def,← Matrix.nonsing_inv_eq_ringInverse,_root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply,hv,neg_mul] using! hi

lemma continuous_realOpNorm : Continuous (SKRatioGaussian.opNorm : Matrix ι ι ℝ → ℝ) := by
  have h : Continuous (fun M : Matrix ι ι ℝ => liftMatrix M) := by
    dsimp [liftMatrix]; fun_prop
  have hc := SKRatioGaussian.ComplexMatrix.continuous_lin.norm.comp h
  simpa only [Function.comp_def,SKRatioGaussian.ComplexMatrix.lin,operator_norm_lift] using hc

lemma realTruncatedK_eventually_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C M E : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (hM : Mᵀ = M) (hE : Eᵀ = E)
    (hMR : SKRatioGaussian.opNorm M < R)
    (hl : lo < SKRatioGaussian.ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(M-C)*D)))
    (hu : -hi < SKRatioGaussian.ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(M-C)*D))) :
    (fun t : ℝ => realTruncatedK f R hR D C (M+t • E)) =ᶠ[𝓝 (0:ℝ)]
      (fun t => (1-D*D*(M+t • E-C))⁻¹) := by
  have hcont : Continuous (fun t : ℝ => liftMatrix (1-D*(M+t • E-C)*D)) := by
    dsimp [liftMatrix]; fun_prop
  have hcont' : Continuous (fun t : ℝ => SKRatioGaussian.opNorm (M+t • E)) :=
    continuous_realOpNorm.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hl' : ∀ᶠ t in 𝓝 (0:ℝ), lo < SKRatioGaussian.ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(M+t • E-C)*D)) :=
    (SKRatioGaussian.ComplexSpectral.continuous_lowerRayleigh.comp hcont).continuousAt.eventually
      (lt_mem_nhds (by simpa using hl))
  have hu' : ∀ᶠ t in 𝓝 (0:ℝ), -hi < SKRatioGaussian.ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(M+t • E-C)*D)) :=
    (SKRatioGaussian.ComplexSpectral.continuous_lowerRayleigh.comp hcont.neg).continuousAt.eventually
      (lt_mem_nhds (by simpa using hu))
  have hm' : ∀ᶠ t in 𝓝 (0:ℝ), SKRatioGaussian.opNorm (M+t • E) < R :=
    hcont'.continuousAt.eventually (gt_mem_nhds (by simpa using hMR))
  filter_upwards [hl',hu',hm'] with t ht ht' hm
  exact realTruncatedK_eq_inverse f hlo hf hR D C (M+t • E) hD hC
    (by simp [Matrix.transpose_smul,hM,hE]) hm.le ht.le ht'.le

lemma realTruncatedK_derivative (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C M E : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (hM : Mᵀ = M) (hE : Eᵀ = E)
    (hMR : SKRatioGaussian.opNorm M < R)
    (hl : lo < SKRatioGaussian.ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(M-C)*D)))
    (hu : -hi < SKRatioGaussian.ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(M-C)*D))) :
    HasDerivAt (fun t : ℝ => realTruncatedK f R hR D C (M+t • E))
      (realTruncatedK f R hR D C M*(D*D)*E*realTruncatedK f R hR D C M) 0 := by
  have hid := realTruncatedK_eq_inverse f hlo hf hR D C M hD hC hM hMR.le hl.le hu.le
  have he := realTruncatedK_eventually_inverse f hlo hf hR D C M E hD hC hM hE hMR hl hu
  have hunit : IsUnit (1-D*D*(M-C)) := by
    have hSH : (liftMatrix (1-D*(M-C)*D)).IsHermitian :=
      liftMatrix_hermitian _ (by simp [Matrix.transpose_mul,hD,hC,hM,mul_assoc])
    have hp : (liftMatrix (1-D*(M-C)*D)).PosDef := hSH.posDef_iff_eigenvalues_pos.mpr (fun i =>
      hlo.trans (hl.trans_le (SKRatioGaussian.ComplexSpectral.eigenvalue_lower_bound hSH i)))
    have hS : IsUnit (1-D*(M-C)*D) := (liftMatrix_isUnit_iff _).mp hp.isUnit
    exact SKRatioGaussian.ResolventIdentity.inverse_one_sub_square_mul_unit D (M-C) hS
  have hm : HasDerivAt (fun t : ℝ => M+t • E-C) E 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const E |>.const_add M).sub_const C using 1
    simp only [one_smul]
  have hq := (hm.const_mul (D*D)).const_sub 1
  have hi := real_matrix_hasDerivAt_inverse hq (by simpa using hunit)
  rw [hid]
  have hi' : HasDerivAt (fun t : ℝ => (1-D*D*(M+t • E-C))⁻¹)
      ((1-D*D*(M-C))⁻¹*(D*D)*E*(1-D*D*(M-C))⁻¹) 0 := by
    simpa only [zero_smul,add_zero,mul_neg,neg_mul,neg_neg,mul_assoc] using! hi
  exact hi'.congr_of_eventuallyEq he

end SKRatioGaussian.RealComplex

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
end
end

end OAI
