import Mathlib
import OAI.Probability.SKRatio.Matrices.Fl1
import OAI.Probability.SKRatio.Matrices.Quadratic
import OAI.Probability.SKRatio.Matrices.PathResolvent
import OAI.Probability.SKRatio.Matrices.InverseSubSquareMul

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
namespace SKRatioGaussian.ComplexMatrix
open scoped SchwartzMap ComplexOrder
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sandShift_special (D C M : Matrix ι ι ℂ) :
    sandShift (1+D*C*D) D M = 1-D*(M-C)*D := by
  dsimp [sandShift]; noncomm_ring

lemma truncatedK_eq_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C M : Matrix ι ι ℂ)
    (hD : Dᴴ = D) (hC : Cᴴ = C) (hM : Mᴴ = M) (hMR : opNorm M ≤ R)
    (hspec : ∀ i, Matrix.IsHermitian.eigenvalues (sandShift_hermitian (1+D*C*D) D M
      (by simp [Matrix.conjTranspose_mul,hD,hC,mul_assoc]) hD hM) i ∈ Icc lo hi) :
    truncatedK f R hR (1+D*C*D) D C M = (1-D*D*(M-C))⁻¹ := by
  have hB : (1+D*C*D)ᴴ = 1+D*C*D := by simp [Matrix.conjTranspose_mul,hD,hC,mul_assoc]
  have hS : IsUnit (sandShift (1+D*C*D) D M) :=
    ((Matrix.IsHermitian.posDef_iff_eigenvalues_pos (sandShift_hermitian _ _ _ hB hD hM)).mpr
      (fun i => hlo.trans_le (hspec i).1)).isUnit
  rw [truncatedK,truncatedG_eq_inverse f hlo hf R hR _ _ _ hB hD hM hMR hspec,
    matrixProject_eq_self R hR M hM hMR,sandShift_special]
  exact (SKRatioGaussian.ResolventIdentity.inverse_one_sub_square_mul D (M-C) (by
    simpa only [sandShift_special] using hS)).symm

lemma truncatedK_eventually_eq_inverse (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C : Matrix ι ι ℂ)
    {M : ℝ → Matrix ι ι ℂ} {t : ℝ} (hMc : ContinuousAt M t)
    (hD : Dᴴ = D) (hC : Cᴴ = C) (hM : ∀ s, (M s)ᴴ = M s)
    (hMR : opNorm (M t) < R)
    (hl : lo < SKRatioGaussian.ComplexSpectral.lowerRayleigh (sandShift (1+D*C*D) D (M t)))
    (hu : -hi < SKRatioGaussian.ComplexSpectral.lowerRayleigh (-sandShift (1+D*C*D) D (M t))) :
    (fun s => truncatedK f R hR (1+D*C*D) D C (M s)) =ᶠ[𝓝 t]
      (fun s => (1-D*D*(M s-C))⁻¹) := by
  have hB : (1+D*C*D)ᴴ = 1+D*C*D := by simp [Matrix.conjTranspose_mul,hD,hC,mul_assoc]
  have hs : ContinuousAt (fun s => sandShift (1+D*C*D) D (M s)) t := by
    dsimp [sandShift]; fun_prop
  have he := SKRatioGaussian.ComplexSpectral.spectral_interval_eventually hs
    (fun s => sandShift_hermitian _ _ _ hB hD (hM s)) hl hu
  have hm := ((continuous_lin.norm).continuousAt.comp hMc).eventually (gt_mem_nhds hMR)
  filter_upwards [he,hm] with s hs hm
  exact truncatedK_eq_inverse f hlo hf hR D C (M s) hD hC (hM s) hm.le hs

lemma square_resolvent_derivative (D C M E : Matrix ι ι ℂ)
    (hunit : IsUnit (1-D*D*(M-C))) :
    HasDerivAt (fun t : ℝ => (1-D*D*(M+t • E-C))⁻¹)
      ((1-D*D*(M-C))⁻¹*(D*D)*E*(1-D*D*(M-C))⁻¹) 0 := by
  have hm : HasDerivAt (fun t : ℝ => M+t • E-C) E 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const E |>.const_add M).sub_const C using 1
    simp only [one_smul]
  have hq := (hm.const_mul (D*D)).const_sub 1
  have hi := matrix_hasDerivAt_inverse hq (by simpa using hunit)
  simpa only [zero_smul,add_zero,mul_neg,neg_mul,neg_neg,mul_assoc] using! hi

lemma truncatedK_derivative (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    {R : ℝ} (hR : 0 ≤ R) (D C M E : Matrix ι ι ℂ)
    (hD : Dᴴ = D) (hC : Cᴴ = C) (hM : Mᴴ = M) (hE : Eᴴ = E)
    (hMR : opNorm M < R)
    (hl : lo < SKRatioGaussian.ComplexSpectral.lowerRayleigh (sandShift (1+D*C*D) D M))
    (hu : -hi < SKRatioGaussian.ComplexSpectral.lowerRayleigh (-sandShift (1+D*C*D) D M)) :
    HasDerivAt (fun t : ℝ => truncatedK f R hR (1+D*C*D) D C (M+t • E))
      (truncatedK f R hR (1+D*C*D) D C M*(D*D)*E*
        truncatedK f R hR (1+D*C*D) D C M) 0 := by
  have hB : (1+D*C*D)ᴴ = 1+D*C*D := by simp [Matrix.conjTranspose_mul,hD,hC,mul_assoc]
  have hSM : (sandShift (1+D*C*D) D M).IsHermitian := sandShift_hermitian _ _ _ hB hD hM
  have hspec : ∀ i, hSM.eigenvalues i ∈ Icc lo hi := by
    intro i
    have hm := SKRatioGaussian.ComplexSpectral.eigenvalue_lower_bound hSM i
    have hp := SKRatioGaussian.ComplexSpectral.eigenvalue_upper_bound hSM i
    constructor <;> linarith
  have hS : IsUnit (1-D*(M-C)*D) := by
    rw [← sandShift_special]
    exact (hSM.posDef_iff_eigenvalues_pos.mpr (fun i => hlo.trans_le (hspec i).1)).isUnit
  have hunit := SKRatioGaussian.ResolventIdentity.inverse_one_sub_square_mul_unit D (M-C) hS
  have hid := truncatedK_eq_inverse f hlo hf hR D C M hD hC hM hMR.le hspec
  rw [hid]
  have he := truncatedK_eventually_eq_inverse f hlo hf hR D C
    (M := fun t : ℝ => M+t • E) (t := 0) (by fun_prop) hD hC
    (fun t => by simp [Matrix.conjTranspose_smul,hM,hE])
    (by simpa using hMR) (by simpa using hl) (by simpa using hu)
  exact (square_resolvent_derivative D C M E hunit).congr_of_eventuallyEq he

end SKRatioGaussian.ComplexMatrix

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
