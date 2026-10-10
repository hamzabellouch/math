import Mathlib
import OAI.Probability.Perceptron.Cascade.CascadeIndependentTilt
import OAI.Probability.Perceptron.Cascade.CascadeHeat

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev CavityRPCState (n d : ℕ) := (Fin (n+1)→ℕ→ℝ)×(Fin d→ℕ→ℝ)
abbrev CavityRPCMark (n d : ℕ) := (Fin (n+1)→ℝ)×(Fin d→ℝ)
def cavityRPCMarkLaw (n d : ℕ) : ProbabilityMeasure (CavityRPCMark n d) :=
  productMarkLaw (piMarkLaw (fun _ : Fin (n+1)=>standardGaussianMark))
    (piMarkLaw (fun _ : Fin d=>standardGaussianMark))
def cavityRPCStep (n d : ℕ) (σ τ : ℕ→ℝ) : CavityRPCState n d×CavityRPCMark n d→CavityRPCState n d :=
  fun p=>(canonicalCoordinateStep (n+1) σ (p.1.1,p.2.1),
    canonicalCoordinateStep d τ (p.1.2,p.2.2))
def cavityRPCTerminal (n d : ℕ) (F : ℝ→ᵇℝ) (x : CavityRPCState n d) : ℝ :=
  logSphericalExp n (Real.sqrt (n+1:ℕ)) (coordinateLeafField (n+1) x.1)+∑ i,F (x.2 i 0)

lemma cavityRPCStep_measurable (n d : ℕ) (σ τ : ℕ→ℝ) : Measurable (cavityRPCStep n d σ τ) :=
  ((canonicalCoordinateStep_measurable (n+1) σ).comp (measurable_fst.fst.prodMk measurable_snd.fst)).prodMk
    ((canonicalCoordinateStep_measurable d τ).comp (measurable_fst.snd.prodMk measurable_snd.snd))
lemma cavityRPCTerminal_measurable (n d : ℕ) (F : ℝ→ᵇℝ) : Measurable (cavityRPCTerminal n d F) := by
  have hv : Measurable (fun x : CavityRPCState n d=>logSphericalExp n (Real.sqrt (n+1:ℕ))
      (coordinateLeafField (n+1) x.1)) := (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))).continuous.measurable.comp
    ((coordinateLeafField_measurable (n+1)).comp measurable_fst)
  apply hv.add
  exact Finset.measurable_sum _ fun i _=>F.measurable.comp ((measurable_pi_apply 0).comp
    ((measurable_pi_apply i).comp measurable_snd))

theorem cavity_finiteRPC_conditional (n d k : ℕ) (σ τ : ℕ→ℝ) (F : ℝ→ᵇℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (x : CavityRPCState n d) :
    Integrable (fun η=>Real.log (decoratedTerminalTotal (cavityRPCStep n d σ τ)
      (cavityRPCTerminal n d F) k (x,η)/
        decoratedTerminalTotal (cavityRPCStep n d σ τ) (fun _=>0) k (x,η)))
      (decoratedCascadeLaw (cavityRPCMarkLaw n d) k z) ∧
    (∫ η,Real.log (decoratedTerminalTotal (cavityRPCStep n d σ τ)
      (cavityRPCTerminal n d F) k (x,η)/
        decoratedTerminalTotal (cavityRPCStep n d σ τ) (fun _=>0) k (x,η))
      ∂decoratedCascadeLaw (cavityRPCMarkLaw n d) k z)=
      gaussianBackward (stdGaussian (Spin (n+1))) (cascadeHeatWord σ k z)
        (logSphericalExp n (Real.sqrt (n+1:ℕ))) (coordinateDepthField (n+1) k x.1)+
      ∑ i,finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
        (fun a=>F (a 0)) (x.2 i) := by
  have hF : Measurable (fun a : ℕ→ℝ=>F (a 0)) := F.measurable.comp (measurable_pi_apply 0)
  have hFI := finiteCascadeFractionalIntegrable_of_bounded standardGaussianMark
    (gaussianShiftStep τ) (gaussianShiftStep_measurable τ) k z hz0 hF
    (fun a=>F.norm_coe_le_norm (a 0))
  have hs := finiteCascade_sum_pi (fun _ : Fin d=>standardGaussianMark)
    (fun _=>gaussianShiftStep τ) k z (fun _ a=>F (a 0)) (fun _=>hFI)
  have hv := coordinateRecursion_eq_backward (n+1) σ
    (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))) k z hz0
  have hi := finiteCascadeFractionalIntegrable_add_product
    (piMarkLaw (fun _ : Fin (n+1)=>standardGaussianMark))
    (piMarkLaw (fun _ : Fin d=>standardGaussianMark))
    (canonicalCoordinateStep (n+1) σ) (canonicalCoordinateStep d τ) k z hz0 hv.2 hs.2
  constructor
  · exact decoratedTerminalLogRatio_integrable (cavityRPCMarkLaw n d) (cavityRPCStep n d σ τ)
      (cavityRPCStep_measurable n d σ τ) k z hz hz0 hz1
      (cavityRPCTerminal_measurable n d F) hi x
  · rw [finiteCascade_terminal_log_recursion_of_fractional (cavityRPCMarkLaw n d)
      (cavityRPCStep n d σ τ) (cavityRPCStep_measurable n d σ τ) k z hz hz0 hz1
      (cavityRPCTerminal_measurable n d F) hi x]
    exact (finiteCascadeLogRecursion_add_product
      (piMarkLaw (fun _ : Fin (n+1)=>standardGaussianMark))
      (piMarkLaw (fun _ : Fin d=>standardGaussianMark))
      (canonicalCoordinateStep (n+1) σ) (canonicalCoordinateStep d τ) k z hz0 hv.2 hs.2 x.1 x.2).trans
      (congrArg₂ (fun a b : ℝ=>a+b) (hv.1 x.1) (hs.1 x.2))


def cavityScalarRootValue (k : ℕ) (τ : ℕ→ℝ) (z : Fin k→ℝ) (t : ℝ) (F : ℝ→ᵇℝ) : ℝ :=
  ∫ b, finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
    (fun x=>F (x 0)) (fun _=>t*b) ∂(standardGaussianMark : Measure ℝ)

def cavityRPCRootState (n d : ℕ) (r t : ℝ) (b : CavityRPCMark n d) : CavityRPCState n d :=
  (fun i _=>r*b.1 i,fun i _=>t*b.2 i)

lemma cavity_scalar_recursion_bound (k : ℕ) (τ : ℕ→ℝ) (z : Fin k→ℝ)
    (hz0 : ∀ i,0<z i) (F : ℝ→ᵇℝ) (x : ℕ→ℝ) :
    |finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
      (fun x=>F (x 0)) x|≤‖F‖ :=
  finiteCascadeLogRecursion_abs_le standardGaussianMark (gaussianShiftStep τ)
    (gaussianShiftStep_measurable τ) k z hz0
    (F.measurable.comp (measurable_pi_apply 0)) (fun a=>F.norm_coe_le_norm (a 0)) x

lemma cavity_scalar_root_pi_mean (d k : ℕ) (τ : ℕ→ℝ) (z : Fin k→ℝ)
    (hz0 : ∀ i,0<z i) (t : ℝ) (F : ℝ→ᵇℝ) :
    (∫ b : Fin d→ℝ, (∑ i,finiteCascadeLogRecursion standardGaussianMark
      (gaussianShiftStep τ) k z (fun x=>F (x 0)) (fun _=>t*b i))
      ∂(piMarkLaw (fun _ : Fin d=>standardGaussianMark) : Measure (Fin d→ℝ)))=
      d*cavityScalarRootValue k τ z t F := by
  have hm := finiteCascadeLogRecursion_measurable standardGaussianMark (gaussianShiftStep τ)
    (gaussianShiftStep_measurable τ) k z (F.measurable.comp (measurable_pi_apply 0))
  have hi (i : Fin d) : Integrable (fun b : Fin d→ℝ=>finiteCascadeLogRecursion
      standardGaussianMark (gaussianShiftStep τ) k z (fun x=>F (x 0)) (fun _=>t*b i))
      (piMarkLaw (fun _ : Fin d=>standardGaussianMark)) := by
    apply Integrable.of_bound (hm.comp (Measurable.of_eval (fun _=>measurable_const.mul
      (measurable_pi_apply i)))).aestronglyMeasurable ‖F‖
    exact ae_of_all _ fun b=>by
      change |finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
        (fun x=>F (x 0)) (fun _=>t*b i)|≤‖F‖
      exact cavity_scalar_recursion_bound k τ z hz0 F _
  rw [integral_finsetSum _ (fun index _=>hi index)]
  have he (i : Fin d) : (∫ b : Fin d→ℝ,finiteCascadeLogRecursion standardGaussianMark
      (gaussianShiftStep τ) k z (fun x=>F (x 0)) (fun _=>t*b i)
      ∂(piMarkLaw (fun _ : Fin d=>standardGaussianMark) : Measure (Fin d→ℝ)))=
        cavityScalarRootValue k τ z t F := by
    have hmp := measurePreserving_eval (fun _ : Fin d=>(standardGaussianMark : Measure ℝ)) i
    unfold cavityScalarRootValue
    rw [←hmp.map_eq]
    exact (integral_map hmp.measurable.aemeasurable
      ((hm.comp (Measurable.of_eval (fun _=>measurable_const.mul measurable_id))).aestronglyMeasurable)).symm
  simp_rw [he]
  simp

theorem cavity_finiteRPC_roots (n d k : ℕ) (σ τ : ℕ→ℝ) (F : ℝ→ᵇℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (r t : ℝ) :
    (∫ b, (∫ η,Real.log (decoratedTerminalTotal (cavityRPCStep n d σ τ)
      (cavityRPCTerminal n d F) k (cavityRPCRootState n d r t b,η)/
        decoratedTerminalTotal (cavityRPCStep n d σ τ) (fun _=>0) k
          (cavityRPCRootState n d r t b,η))
      ∂decoratedCascadeLaw (cavityRPCMarkLaw n d) k z)
      ∂(cavityRPCMarkLaw n d : Measure (CavityRPCMark n d)))=
      (n+1:ℕ)*amplitudeSphereValue n k σ z r+d*cavityScalarRootValue k τ z t F := by
  have hl := gaussianBackward_lipschitz (stdGaussian (Spin (n+1)))
    (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))) (cascadeHeatWord σ k z)
    (cascadeHeatWord_nonneg σ k z (fun i=>(hz0 i).le))
  let V := fun b : Fin (n+1)→ℝ=>gaussianBackward (stdGaussian (Spin (n+1)))
    (cascadeHeatWord σ k z) (logSphericalExp n (Real.sqrt (n+1:ℕ)))
      (r • WithLp.toLp 2 b)
  let W := fun b : Fin d→ℝ=>∑ i,finiteCascadeLogRecursion standardGaussianMark
    (gaussianShiftStep τ) k z (fun x=>F (x 0)) (fun _=>t*b i)
  have hV : Integrable V (piMarkLaw (fun _ : Fin (n+1)=>standardGaussianMark)) :=
    integrable_pi_standardGaussian (n+1) (hl.continuous.comp (continuous_id.const_smul r))
      (by simpa only [zero_add,Function.comp_def,Pi.smul_apply,id_eq] using (gaussian_integrable_lipschitz
        (stdGaussian (Spin (n+1))) hl r (0 : Spin (n+1))))
  have hW : Integrable W (piMarkLaw (fun _ : Fin d=>standardGaussianMark)) := by
    apply integrable_finsetSum
    intro i _
    have hm := finiteCascadeLogRecursion_measurable standardGaussianMark (gaussianShiftStep τ)
      (gaussianShiftStep_measurable τ) k z (F.measurable.comp (measurable_pi_apply 0))
    apply Integrable.of_bound (hm.comp (Measurable.of_eval (fun _=>measurable_const.mul
      (measurable_pi_apply i)))).aestronglyMeasurable ‖F‖
    exact ae_of_all _ fun b=>by
      change |finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
        (fun x=>F (x 0)) (fun _=>t*b i)|≤‖F‖
      exact cavity_scalar_recursion_bound k τ z hz0 F _
  simp_rw [(cavity_finiteRPC_conditional n d k σ τ F z hz hz0 hz1 _).2]
  change (∫ b,V b.1+W b.2 ∂(piMarkLaw (fun _ : Fin (n+1)=>standardGaussianMark) : Measure _).prod
    (piMarkLaw (fun _ : Fin d=>standardGaussianMark)))=_
  rw [integral_add (hV.comp_fst _) (hW.comp_snd _),integral_fun_fst,integral_fun_snd]
  simp only [probReal_univ,one_smul]
  rw [show (∫ b,W b ∂(piMarkLaw (fun _ : Fin d=>standardGaussianMark) : Measure _))=
    d*cavityScalarRootValue k τ z t F from cavity_scalar_root_pi_mean d k τ z hz0 t F]
  congr 1
  have he := amplitudeSphereValue_eq_backward n k σ z hz hz0 hz1 r
  rw [gaussianBackward,gaussianEntropic_zero _ hl] at he
  simp only [zero_add] at he
  have hpi : (∫ b,V b ∂(piMarkLaw (fun _ : Fin (n+1)=>standardGaussianMark) : Measure _))=
      ∫ y,gaussianBackward (stdGaussian (Spin (n+1))) (cascadeHeatWord σ k z)
        (logSphericalExp n (Real.sqrt (n+1:ℕ))) (r • y) ∂stdGaussian (Spin (n+1)) :=
    integral_pi_standardGaussian (n+1) (show Continuous (fun y : Spin (n+1)=>
      gaussianBackward (stdGaussian (Spin (n+1))) (cascadeHeatWord σ k z)
        (logSphericalExp n (Real.sqrt (n+1:ℕ))) (r • y)) from
          hl.continuous.comp (continuous_id.const_smul r))
  rw [hpi,he]
  field_simp

end SphericalPerceptronFreeEnergy
end

end OAI
