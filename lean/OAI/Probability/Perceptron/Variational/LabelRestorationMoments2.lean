import Mathlib
import OAI.Probability.Perceptron.Variational.LabelRestorationKernel

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

def jointRestorationBlockTest (r : ℕ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ) :
    (j : ℕ) → CompactBlock CompactJointOverlap (r+j) →ᵇ ℝ
  | 0 => F
  | j+1 => (jointRestorationBlockTest r F j).compContinuous
      ⟨fun Q i l => Q i.succ l.succ,by fun_prop⟩

lemma jointRestorationBlockTest_source (N k r : ℕ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ)
    (j : ℕ) (x : Fin (r+j) → NormalizedSpin N×IndexedLeaf k) :
    jointRestorationBlockTest r F j (fun i l => sourceJointOverlap (x i) (x l)) =
      replicaFrontLift (fun x : Fin r → NormalizedSpin N×IndexedLeaf k =>
        F (fun i l => sourceJointOverlap (x i) (x l))) j x := by
  induction j with
  | zero => rfl
  | succ j hj => exact hj _

lemma labelMarkedBlockKernel_source {N k r : ℕ} (q : Fin (k+1) → ℝ)
    (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) (x : Fin r → NormalizedSpin N×IndexedLeaf k) :
    labelMarkedBlockKernel q Ψ (fun i l => sourceJointOverlap (x i) (x l)) =
      freshMarkedMatrixKernel Ψ (fun i l => if i=l then 1 else q (indexedCommonDepth k (x l).2 (x i).2)) := by
  apply congrArg (freshMarkedMatrixKernel Ψ)
  funext i l
  change (if i=l then 1 else labelProfileInterpolant q (sourceJointOverlap (x i) (x l)).2)=_
  split_ifs with hi
  · rfl
  · exact labelProfileInterpolant_node q _

def labelRestorationBlockMoment {k r : ℕ} (q : Fin (k+1) → ℝ) (f : ℝ →ᵇ ℝ)
    (v w : Fin r → ℝ →ᵇ ℝ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ) (j : ℕ) :
    CompactBlock CompactJointOverlap (r+j) →ᵇ ℝ :=
  jointRestorationBlockTest r F j * labelMarkedBlockKernel q (gaussianMixedTest (labelRestoredFunctions f v j)) *
    labelMarkedBlockKernel q (gaussianMixedTest (labelRestoredFunctions f w j))

lemma labelRestoration_to_block (N k r : ℕ) (q : Fin (k+1) → ℝ)
    (h0 : 0≤q 0) (hq : Monotone q) (h1 : q (Fin.last k)≤1)
    (ψ : ℝ →ᵇ ℝ) (v w : Fin r → ℝ →ᵇ ℝ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ)
    (μ : Measure (NormalizedSpin N×IndexedLeaf k)) [IsProbabilityMeasure μ]
    (H : NormalizedSpin N×IndexedLeaf k → ℝ) (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (j : ℕ) :
    (∫ b, (tiltMean μ H (labelRestorationWeight q (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0) ψ b) 1)^j *
      gibbsReplicaMean μ H r (labelRestorationTest q (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0) ψ v w
        (fun x => F (fun i l => sourceJointOverlap (x i) (x l))) b)
        ∂countableGaussianLaw.prod countableGaussianLaw) =
      gibbsReplicaMean μ H (r+j) (fun x => labelRestorationBlockMoment q ψ v w F j
        (fun i l => sourceJointOverlap (x i) (x l))) := by
  have hp (i l : Fin r) : Measurable (fun x : Fin r → NormalizedSpin N×IndexedLeaf k => (x i,x l)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply l)
  have hc (i l : Fin r) := (sourceJointOverlap_measurable N k).comp (hp i l)
  have hblock : Measurable (fun x : Fin r → NormalizedSpin N×IndexedLeaf k =>
      fun i l => sourceJointOverlap (x i) (x l)) :=
    Measurable.of_eval fun row => Measurable.of_eval fun column => hc row column
  have hF := F.measurable.comp hblock
  have he := labelRestoration_moments q h0 hq h1 ψ v w μ H hH hi _ hF
    (norm_nonneg F) (fun x => F.norm_coe_le_norm _) j
  refine he.trans ?_
  apply congrArg (gibbsReplicaMean μ H (r+j))
  funext x
  simp only [labelRestorationBlockMoment,BoundedContinuousFunction.mul_apply,
    labelMarkedBlockKernel_source,jointRestorationBlockTest_source]
  rfl

def sourceLabelRestorationMoment (n k r : ℕ) (q : Fin (k+1) → ℝ) (s : ℝ≥0)
    (f ψ : ℝ →ᵇ ℝ) (v w : Fin r → ℝ →ᵇ ℝ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0) (j : ℕ) : ℝ :=
  ∫ a, ∫ b, (tiltMean (sourceFullSpinLeafKernel n k a)
    (sourceCouplingHamiltonian n k f p d h u a) (labelRestorationWeight q s ψ b) 1)^j *
    gibbsReplicaMean (sourceFullSpinLeafKernel n k a) (sourceCouplingHamiltonian n k f p d h u a) r
      (labelRestorationTest q s ψ v w (fun x => F (fun i l => sourceJointOverlap (x i) (x l))) b)
    ∂countableGaussianLaw.prod countableGaussianLaw ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw

lemma sourceLabelRestorationMoment_array (n k r : ℕ) (q : Fin (k+1) → ℝ)
    (h0 : 0≤q 0) (hq : Monotone q) (h1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (v w : Fin r → ℝ →ᵇ ℝ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0) (j : ℕ) :
    sourceLabelRestorationMoment n k r q (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0) f ψ v w F p d h u z t j =
      ∫ Q, labelRestorationBlockMoment q ψ v w F j (compactBlock (r+j) Q) ∂sourceGibbsArrayLaw n k f p d h u z t := by
  refine Eq.trans ?_ (sourceGibbsArray_block_integral n k f p d h hh0 hh u z t (r+j)
    (F := fun Q => labelRestorationBlockMoment q ψ v w F j Q)
    (labelRestorationBlockMoment q ψ v w F j).measurable
    (fun Q => (labelRestorationBlockMoment q ψ v w F j).norm_coe_le_norm Q)).symm
  unfold sourceLabelRestorationMoment
  apply integral_congr_ae
  filter_upwards [sourceFresh_exp_ae n k f p d h hh0 hh u z t] with a ha
  exact labelRestoration_to_block (n+1) k r q h0 hq h1 ψ v w F _ _
    (sourceCouplingHamiltonian_measurable n k f p d h u).of_uncurry_left ha j

lemma sourceLabelRestorationMoment_tendsto (k r : ℕ) (q : Fin (k+1) → ℝ)
    (h0 : 0≤q 0) (hq : Monotone q) (h1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (v w : Fin r → ℝ →ᵇ ℝ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ)
    (p d : (n : ℕ) → Fin (n+1) → ℕ) (h : ℕ → Fin (k+1) → ℝ)
    (hh0 : ∀ n i, 0≤h n i) (hh : ∀ n, Monotone (h n)) (u : (n : ℕ) → Fin (n+1) → ℝ)
    (z : Fin k → ℝ) (t : ℕ → ℝ≥0) (s : ℕ → ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) (j : ℕ) :
    Tendsto (fun n => sourceLabelRestorationMoment (s n) k r q (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0)
      f ψ v w F (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n)) j) atTop
      (𝓝 (∫ Q, labelRestorationBlockMoment q ψ v w F j (compactBlock (r+j) Q) ∂ν)) := by
  simp_rw [sourceLabelRestorationMoment_array _ _ _ _ h0 hq h1 _ _ _ _ _ _ _ _ (hh0 _) (hh _)]
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    ((labelRestorationBlockMoment q ψ v w F j).compContinuous
      ⟨compactBlock (r+j),compactBlock_continuous (r+j)⟩)).continuousAt.tendsto.comp hlim

lemma sourceReplicaBlock_measurable (N k r : ℕ) :
    Measurable (fun x : Fin r → NormalizedSpin N×IndexedLeaf k =>
      fun i l => sourceJointOverlap (x i) (x l)) := by
  have hp (i l : Fin r) : Measurable (fun x : Fin r → NormalizedSpin N×IndexedLeaf k => (x i,x l)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply l)
  have hc (i l : Fin r) := (sourceJointOverlap_measurable N k).comp (hp i l)
  exact Measurable.of_eval fun row => Measurable.of_eval fun column => hc row column

variable (n k r : ℕ) (q : Fin (k+1) → ℝ) (s : ℝ≥0)
variable (f ψ : ℝ →ᵇ ℝ) (v w : Fin r → ℝ →ᵇ ℝ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ)
variable (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ)
variable (z : Fin k → ℝ) (t : ℝ≥0)

def sourceLabelRestorationNumerator :=
  labelKernelNumerator (sourceFullSpinLeafKernel n k) (sourceCouplingHamiltonian n k f p d h u)
    q s ψ v w (fun x => F (fun i l => sourceJointOverlap (x i) (x l)))
def sourceLabelRestorationDenominator :=
  labelKernelCompactDenominator (sourceFullSpinLeafKernel n k) (sourceCouplingHamiltonian n k f p d h u) q s ψ

def sourceLabelRestorationRatio : ℝ :=
  ∫ a, sourceLabelRestorationNumerator n k r q s f ψ v w F p d h u a *
    restorationReciprocal ψ r (sourceLabelRestorationDenominator n k q s f ψ p d h u a)
    ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw)

lemma sourceLabelRestorationNumerator_measurable :
    Measurable (sourceLabelRestorationNumerator n k r q s f ψ v w F p d h u) :=
  labelKernelNumerator_measurable _ _ _ _ _ _ _ _ (sourceCouplingHamiltonian_measurable n k f p d h u)
    (F.measurable.comp (sourceReplicaBlock_measurable (n+1) k r))

lemma sourceLabelRestorationDenominator_measurable :
    Measurable (sourceLabelRestorationDenominator n k q s f ψ p d h u) :=
  labelKernelCompactDenominator_measurable _ _ _ _ _ (sourceCouplingHamiltonian_measurable n k f p d h u)

lemma sourceLabelRestorationNumerator_bound (a) :
    |sourceLabelRestorationNumerator n k r q s f ψ v w F p d h u a|≤
      ‖F‖*(∏ i, ‖expBCF 1 ψ*v i‖)*(∏ i, ‖expBCF 1 ψ*w i‖) :=
  labelKernelNumerator_uniform_bound _ _ _ _ _ _ _ _ (sourceCouplingHamiltonian_measurable n k f p d h u)
    (F.measurable.comp (sourceReplicaBlock_measurable (n+1) k r)) (norm_nonneg F)
    (fun _ => F.norm_coe_le_norm _) a

lemma sourceLabelRestorationPolynomial (hh0 : ∀ i,0≤h i) (hh : Monotone h) (j : ℕ) :
    (∫ a, sourceLabelRestorationNumerator n k r q s f ψ v w F p d h u a *
      (sourceLabelRestorationDenominator n k q s f ψ p d h u a).val^j
      ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw)) =
    sourceLabelRestorationMoment n k r q s f ψ v w F p d h u z t j := by
  let κ := sourceFullSpinLeafKernel n k
  let H := sourceCouplingHamiltonian n k f p d h u
  let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
  let T := fun x : Fin r → NormalizedSpin (n+1)×IndexedLeaf k => F (fun i l => sourceJointOverlap (x i) (x l))
  have hH := sourceCouplingHamiltonian_measurable n k f p d h u
  have hT := F.measurable.comp (sourceReplicaBlock_measurable (n+1) k r)
  have hF := sourceFresh_exp_ae n k f p d h hh0 hh u z t
  let J : C(RestorationRange ψ,ℝ) := ⟨fun x => x.val^j,continuous_subtype_val.pow j⟩
  have hI := labelKernel_weighted_integrable κ H q s ψ v w T hH hT
    (norm_nonneg F) (fun x => F.norm_coe_le_norm _) P J
  have hae := (measurePreserving_fst (μ:=P) (ν:=countableGaussianLaw.prod countableGaussianLaw)).quasiMeasurePreserving.ae hF
  have hEq : (fun a => labelKernelNumerator κ H q s ψ v w T a * J (labelKernelCompactDenominator κ H q s ψ a)) =ᵐ[P.prod (countableGaussianLaw.prod countableGaussianLaw)]
      (fun a => labelKernelNumerator κ H q s ψ v w T a * (labelKernelDenominator κ H q s ψ a)^j) := by
    filter_upwards [hae] with a ha
    dsimp only [J,ContinuousMap.coe_mk]
    rw [labelKernelCompactDenominator_eq κ H q s ψ hH ha a.2]
  have hi := hI.congr hEq
  change (∫ a, labelKernelNumerator κ H q s ψ v w T a * J (labelKernelCompactDenominator κ H q s ψ a) ∂P.prod _) = _
  rw [integral_congr_ae hEq,integral_prod _ hi]
  unfold sourceLabelRestorationMoment
  apply integral_congr_ae
  exact ae_of_all _ fun a => integral_congr_ae (ae_of_all _ fun b => mul_comm _ _)

lemma sourceLabelRestorationRatio_eq (hh0 : ∀ i,0≤h i) (hh : Monotone h) :
    sourceLabelRestorationRatio n k r q s f ψ v w F p d h u z t =
      ∫ a, labelKernelRestoredRatio (sourceFullSpinLeafKernel n k)
        (sourceCouplingHamiltonian n k f p d h u) q s ψ v w
        (fun x => F (fun i l => sourceJointOverlap (x i) (x l))) a
      ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw) := by
  have he := labelKernel_weighted_eq (sourceFullSpinLeafKernel n k)
    (sourceCouplingHamiltonian n k f p d h u) q s ψ v w
    (fun x => F (fun i l => sourceJointOverlap (x i) (x l)))
    (sourceCouplingHamiltonian_measurable n k f p d h u)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (sourceFresh_exp_ae n k f p d h hh0 hh u z t) (fun x => (x^r)⁻¹)
  simpa only [sourceLabelRestorationRatio,sourceLabelRestorationNumerator,sourceLabelRestorationDenominator,
    restorationReciprocal,ContinuousMap.coe_mk,labelKernelRestoredRatio,div_eq_mul_inv] using he

end SphericalPerceptronFreeEnergy
end

end OAI
