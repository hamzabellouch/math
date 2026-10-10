import Mathlib
import OAI.Probability.SKGap.Localization.SandShiftSpecial
import OAI.Probability.SKGap.Matrix.LiftMatrix

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
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap.RealComplex
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realPart (M : Matrix ι ι ℂ) : Matrix ι ι ℝ := M.map Complex.re

lemma norm_realPart_le (M : Matrix ι ι ℂ) : ‖realPart M‖ ≤ ‖M‖ := by
  rw [Matrix.frobenius_norm_def,Matrix.frobenius_norm_def]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro k _
  simp only [realPart,Matrix.map_apply,Real.rpow_two]
  exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (M i k)) 2

omit [Fintype ι] [DecidableEq ι] in
lemma realPart_sub (M N : Matrix ι ι ℂ) : realPart (M-N) = realPart M-realPart N := by
  ext i k; simp [realPart]
omit [Fintype ι] [DecidableEq ι] in
lemma realPart_liftMatrix (M : Matrix ι ι ℝ) : realPart (liftMatrix M) = M := by
  ext i k; simp [realPart,liftMatrix]

lemma realPart_lipschitz : LipschitzWith 1 (realPart (ι := ι)) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul,realPart_sub] using norm_realPart_le (M-N)

omit [DecidableEq ι] in
lemma reVec_norm_le (x : EuclideanSpace ℂ ι) : ‖reVec x‖ ≤ ‖x‖ := by
  have h := vec_norm_split x
  nlinarith [sq_nonneg ‖imVec x‖,norm_nonneg (reVec x),norm_nonneg x]

lemma realPart_operator (M : Matrix ι ι ℂ) (x : EuclideanSpace ℝ ι) :
    rlin (realPart M) x = reVec (clin M (liftVec x)) := by
  ext i
  change (∑ k, (M i k).re*x k) = (∑ k, M i k*(x k : ℂ)).re
  simp

lemma operator_realPart_le (M : Matrix ι ι ℂ) : opNorm (realPart M) ≤ ‖clin M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [realPart_operator]
  exact (reVec_norm_le _).trans ((clin M).le_opNorm (liftVec x) |>.trans_eq (by rw [norm_liftVec]))

lemma liftMatrix_inverse {M : Matrix ι ι ℝ} (hM : IsUnit M) :
    liftMatrix M⁻¹ = (liftMatrix M)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← liftMatrix_mul,Matrix.mul_nonsing_inv M (M.isUnit_iff_isUnit_det.mp hM),liftMatrix_one]

end SKGap.RealComplex

namespace SKGap.RealComplex
open scoped Matrix.Norms.Frobenius SchwartzMap ComplexOrder
open SKGap.ComplexMatrix
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
    SKGap.opNorm (realTruncatedK f R hR D C M) ≤ kBound f R (liftMatrix D) (liftMatrix C) := by
  have hD' := liftMatrix_hermitian D hD
  have hC' := liftMatrix_hermitian C hC
  have hB : (1+liftMatrix D*liftMatrix C*liftMatrix D)ᴴ =
      1+liftMatrix D*liftMatrix C*liftMatrix D := by simp [Matrix.conjTranspose_mul,hD',hC',mul_assoc]
  exact (operator_realPart_le _).trans (truncatedK_opNorm f hR _ _ _ _ hB hD')

lemma realTruncatedK_eq_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C M : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (hM : Mᵀ = M) (hMR : SKGap.opNorm M ≤ R)
    (hl : lo ≤ SKGap.ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(M-C)*D)))
    (hu : -hi ≤ SKGap.ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(M-C)*D))) :
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
    have hm := SKGap.ComplexSpectral.eigenvalue_lower_bound hS i
    have hp := SKGap.ComplexSpectral.eigenvalue_upper_bound hS i
    have hl' : lo ≤ SKGap.ComplexSpectral.lowerRayleigh
        (sandShift (1+liftMatrix D*liftMatrix C*liftMatrix D) (liftMatrix D) (liftMatrix M)) := by
      simpa only [hid] using hl
    have hu' : -hi ≤ SKGap.ComplexSpectral.lowerRayleigh
        (-sandShift (1+liftMatrix D*liftMatrix C*liftMatrix D) (liftMatrix D) (liftMatrix M)) := by
      simpa only [hid] using hu
    constructor <;> linarith
  have hsunit : IsUnit (1-liftMatrix D*(liftMatrix M-liftMatrix C)*liftMatrix D) := by
    rw [← sandShift_special]
    exact (hS.posDef_iff_eigenvalues_pos.mpr (fun i => hlo.trans_le (hspec i).1)).isUnit
  have hrunit : IsUnit (1-D*D*(M-C)) := by
    apply (liftMatrix_isUnit_iff _).mp
    simpa only [liftMatrix_sub,liftMatrix_mul,liftMatrix_one] using
      SKGap.ResolventIdentity.inverse_one_sub_square_mul_unit (liftMatrix D) (liftMatrix M-liftMatrix C) hsunit
  unfold realTruncatedK
  rw [truncatedK_eq_inverse f hlo hf hR _ _ _ hD' hC' hM'
    (by simpa only [SKGap.ComplexMatrix.opNorm,SKGap.ComplexMatrix.lin,operator_norm_lift] using hMR) hspec]
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

lemma continuous_realOpNorm : Continuous (SKGap.opNorm : Matrix ι ι ℝ → ℝ) := by
  have h : Continuous (fun M : Matrix ι ι ℝ => liftMatrix M) := by
    dsimp [liftMatrix]; fun_prop
  have hc := SKGap.ComplexMatrix.continuous_lin.norm.comp h
  simpa only [Function.comp_def,SKGap.ComplexMatrix.lin,operator_norm_lift] using hc

lemma realTruncatedK_eventually_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C M E : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (hM : Mᵀ = M) (hE : Eᵀ = E)
    (hMR : SKGap.opNorm M < R)
    (hl : lo < SKGap.ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(M-C)*D)))
    (hu : -hi < SKGap.ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(M-C)*D))) :
    (fun t : ℝ => realTruncatedK f R hR D C (M+t • E)) =ᶠ[𝓝 (0:ℝ)]
      (fun t => (1-D*D*(M+t • E-C))⁻¹) := by
  have hcont : Continuous (fun t : ℝ => liftMatrix (1-D*(M+t • E-C)*D)) := by
    dsimp [liftMatrix]; fun_prop
  have hcont' : Continuous (fun t : ℝ => SKGap.opNorm (M+t • E)) :=
    continuous_realOpNorm.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hl' : ∀ᶠ t in 𝓝 (0:ℝ), lo < SKGap.ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(M+t • E-C)*D)) :=
    (SKGap.ComplexSpectral.continuous_lowerRayleigh.comp hcont).continuousAt.eventually
      (lt_mem_nhds (by simpa using hl))
  have hu' : ∀ᶠ t in 𝓝 (0:ℝ), -hi < SKGap.ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(M+t • E-C)*D)) :=
    (SKGap.ComplexSpectral.continuous_lowerRayleigh.comp hcont.neg).continuousAt.eventually
      (lt_mem_nhds (by simpa using hu))
  have hm' : ∀ᶠ t in 𝓝 (0:ℝ), SKGap.opNorm (M+t • E) < R :=
    hcont'.continuousAt.eventually (gt_mem_nhds (by simpa using hMR))
  filter_upwards [hl',hu',hm'] with t ht ht' hm
  exact realTruncatedK_eq_inverse f hlo hf hR D C (M+t • E) hD hC
    (by simp [Matrix.transpose_smul,hM,hE]) hm.le ht.le ht'.le

lemma realTruncatedK_derivative (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C M E : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (hM : Mᵀ = M) (hE : Eᵀ = E)
    (hMR : SKGap.opNorm M < R)
    (hl : lo < SKGap.ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(M-C)*D)))
    (hu : -hi < SKGap.ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(M-C)*D))) :
    HasDerivAt (fun t : ℝ => realTruncatedK f R hR D C (M+t • E))
      (realTruncatedK f R hR D C M*(D*D)*E*realTruncatedK f R hR D C M) 0 := by
  have hid := realTruncatedK_eq_inverse f hlo hf hR D C M hD hC hM hMR.le hl.le hu.le
  have he := realTruncatedK_eventually_inverse f hlo hf hR D C M E hD hC hM hE hMR hl hu
  have hunit : IsUnit (1-D*D*(M-C)) := by
    have hSH : (liftMatrix (1-D*(M-C)*D)).IsHermitian :=
      liftMatrix_hermitian _ (by simp [Matrix.transpose_mul,hD,hC,hM,mul_assoc])
    have hp : (liftMatrix (1-D*(M-C)*D)).PosDef := hSH.posDef_iff_eigenvalues_pos.mpr (fun i =>
      hlo.trans (hl.trans_le (SKGap.ComplexSpectral.eigenvalue_lower_bound hSH i)))
    have hS : IsUnit (1-D*(M-C)*D) := (liftMatrix_isUnit_iff _).mp hp.isUnit
    exact SKGap.ResolventIdentity.inverse_one_sub_square_mul_unit D (M-C) hS
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

end SKGap.RealComplex

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
