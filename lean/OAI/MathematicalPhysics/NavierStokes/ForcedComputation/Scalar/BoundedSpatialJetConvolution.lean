import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedKernelConvolution
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetOperators
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! Convolution by an integrable scalar kernel on the Banach space of finite spatial jets.

The construction integrates each jet pointwise. It therefore does not assume that spatial
translations act strongly continuously on the uniform norm of the highest derivative.
-/

noncomputable section
namespace ForcedComputation.BoundedSpatialJets

open MeasureTheory Set Filter
open scoped Topology ContDiff BoundedContinuousFunction

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ E] [CompleteSpace F] in
private theorem continuous_convolve (μ : Measure E) (w : E → ℝ) (f : E → F)
    (hw : Integrable w μ) (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Continuous (BoundedKernel.convolve E F μ w f) := by
  apply continuous_of_dominated (bound := fun y => ‖w y‖ * C)
  · intro x
    exact (BoundedKernel.integrand_integrable E F μ w f hw hf C hC x).aestronglyMeasurable
  · intro x
    exact ae_of_all _ fun y => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC (x - y)) (norm_nonneg _)
  · exact hw.norm.mul_const C
  · exact ae_of_all _ fun y =>
      (hf.comp (continuous_id.sub continuous_const)).const_smul (w y)

/-- The kernel mass controlling every jet, with absolute values for signed kernels. -/
def kernelMass (μ : Measure E) (w : E → ℝ) : ℝ := ∫ y, |w y| ∂μ

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] in
theorem kernelMass_nonneg (μ : Measure E) (w : E → ℝ) : 0 ≤ kernelMass E μ w :=
  integral_nonneg fun y => abs_nonneg (w y)

/-- Pointwise convolution of the finite family of bounded derivatives. -/
def convolutionFamily (k : ℕ) (μ : Measure E) (w : E → ℝ) (hw : Integrable w μ)
    (J : Space E F k) : Family E F k := fun i =>
  BoundedContinuousFunction.ofNormedAddCommGroup
    (BoundedKernel.convolve E (Value E F i.val) μ w (J.val i))
    (continuous_convolve E (Value E F i.val) μ w (J.val i) hw (J.val i).continuous
      ‖J‖ (norm_jet_le E F k J i))
    (‖J‖ * kernelMass E μ w)
    (fun x => BoundedKernel.norm_convolve_le E (Value E F i.val) μ w (J.val i)
      hw (J.val i).continuous ‖J‖ (norm_jet_le E F k J i) x)

/-- The consecutive derivatives remain compatible after convolution. -/
theorem convolutionFamily_compatible (k : ℕ) (μ : Measure E) (w : E → ℝ)
    (hw : Integrable w μ) (J : Space E F k) :
    convolutionFamily E F k μ w hw J ∈ compatible E F k := by
  apply (mem_compatible E F k _).mpr
  intro i x
  have hf : ContDiff ℝ 1 (J.val i.castSucc) :=
    jet_contDiff E F k J i.val 1 (by omega)
  have hd (z : E) :
      fderiv ℝ (J.val i.castSucc) z = curryMap E F i.val (J.val i.succ z) :=
    (hasFDerivAt E F k J i z).fderiv
  have hb (z : E) : ‖fderiv ℝ (J.val i.castSucc) z‖ ≤ ‖J‖ := by
    rw [hd, (curryMap E F i.val).norm_map]
    exact norm_jet_le E F k J i.succ z
  have h := BoundedKernel.hasFDerivAt_convolve E (Value E F i.val) μ w
    (J.val i.castSucc) hw hf ‖J‖ ‖J‖ (norm_jet_le E F k J i.castSucc) hb x
  have hi := BoundedKernel.integrand_integrable E (Value E F (i.val + 1)) μ w
    (J.val i.succ) hw (J.val i.succ).continuous ‖J‖
    (norm_jet_le E F k J i.succ) x
  have he : (∫ y, w y • fderiv ℝ (J.val i.castSucc) (x - y) ∂μ) =
      curryMap E F i.val (∫ y, w y • J.val i.succ (x - y) ∂μ) := by
    simp_rw [hd]
    simpa only [map_smul, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      ((curryMap E F i.val).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm hi)
  rw [he] at h
  exact h

/-- Convolution as an element of the same finite-order jet space. -/
def convolution (k : ℕ) (μ : Measure E) (w : E → ℝ) (hw : Integrable w μ)
    (J : Space E F k) : Space E F k :=
  ⟨convolutionFamily E F k μ w hw J, convolutionFamily_compatible E F k μ w hw J⟩

@[simp] theorem convolution_jet (k : ℕ) (μ : Measure E) (w : E → ℝ)
    (hw : Integrable w μ) (J : Space E F k) (i : Fin (k + 1)) (x : E) :
    (convolution E F k μ w hw J).val i x = ∫ y, w y • J.val i (x - y) ∂μ := rfl

theorem function_convolution (k : ℕ) (μ : Measure E) (w : E → ℝ)
    (hw : Integrable w μ) (J : Space E F k) (x : E) :
    function E F k (convolution E F k μ w hw J) x =
      ∫ y, w y • function E F k J (x - y) ∂μ := by
  rw [function_apply, convolution_jet]
  have hi := BoundedKernel.integrand_integrable E (Value E F 0) μ w
    (J.val (firstIndex k)) hw (J.val (firstIndex k)).continuous ‖J‖
    (norm_jet_le E F k J (firstIndex k)) x
  symm
  simpa only [function_apply, map_smul, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
    ((valueMap E F).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm hi)

theorem norm_convolution_le (k : ℕ) (μ : Measure E) (w : E → ℝ)
    (hw : Integrable w μ) (J : Space E F k) :
    ‖convolution E F k μ w hw J‖ ≤ kernelMass E μ w * ‖J‖ := by
  change ‖convolutionFamily E F k μ w hw J‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (kernelMass_nonneg E μ w) (norm_nonneg J))).mpr
  intro i
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (kernelMass_nonneg E μ w) (norm_nonneg J))).mpr
  intro x
  change ‖BoundedKernel.convolve E (Value E F i.val) μ w (J.val i) x‖ ≤ _
  simpa only [kernelMass, mul_comm] using BoundedKernel.norm_convolve_le E (Value E F i.val)
    μ w (J.val i) hw (J.val i).continuous ‖J‖ (norm_jet_le E F k J i) x

/-- The bounded linear heat/convolution operator; its norm is at most the kernel's L1 mass. -/
def convolutionCLM (k : ℕ) (μ : Measure E) (w : E → ℝ) (hw : Integrable w μ) :
    Space E F k →L[ℝ] Space E F k :=
  LinearMap.mkContinuous
    { toFun := convolution E F k μ w hw
      map_add' := by
        intro J K
        apply Subtype.ext
        funext i
        apply BoundedContinuousFunction.ext
        intro x
        change (∫ y, w y • (J.val i (x - y) + K.val i (x - y)) ∂μ) =
          (∫ y, w y • J.val i (x - y) ∂μ) + ∫ y, w y • K.val i (x - y) ∂μ
        simp_rw [smul_add]
        exact integral_add
          (BoundedKernel.integrand_integrable E (Value E F i.val) μ w (J.val i)
            hw (J.val i).continuous ‖J‖ (norm_jet_le E F k J i) x)
          (BoundedKernel.integrand_integrable E (Value E F i.val) μ w (K.val i)
            hw (K.val i).continuous ‖K‖ (norm_jet_le E F k K i) x)
      map_smul' := by
        intro c J
        apply Subtype.ext
        funext i
        apply BoundedContinuousFunction.ext
        intro x
        change (∫ y, w y • (c • J.val i (x - y)) ∂μ) =
          c • ∫ y, w y • J.val i (x - y) ∂μ
        simp_rw [smul_comm (w _) c]
        exact integral_smul c _ }
    (kernelMass E μ w) (norm_convolution_le E F k μ w hw)

@[simp] theorem convolutionCLM_apply (k : ℕ) (μ : Measure E) (w : E → ℝ)
    (hw : Integrable w μ) (J : Space E F k) :
    convolutionCLM E F k μ w hw J = convolution E F k μ w hw J := rfl

theorem norm_convolutionCLM_le (k : ℕ) (μ : Measure E) (w : E → ℝ)
    (hw : Integrable w μ) : ‖convolutionCLM E F k μ w hw‖ ≤ kernelMass E μ w := by
  exact (convolutionCLM E F k μ w hw).opNorm_le_bound
    (kernelMass_nonneg E μ w) (norm_convolution_le E F k μ w hw)

end ForcedComputation.BoundedSpatialJets

end

end OAI
