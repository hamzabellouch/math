import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityCompensator

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def bulkCDefect (m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (c : ℝ)
    (a : BulkDisorder (m+1) M) : ℝ :=
  tiltMean (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v a)
    (fun x=>|bulkC (m+1) M f a.1 x-c|) 1

lemma bulkCDefect_measurable (m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (c : ℝ) :
    Measurable (bulkCDefect m M f v c) := by
  exact kernel_tiltMean_measurable (bulkSpinKernel m M)
    (bulkGibbsHamiltonian_measurable m M f.f v) ((bulkC_measurable m M f).sub_const c).abs

lemma bulkCDefect_bound (m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (c K : ℝ) (hK : 0≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤K)
    (a : BulkDisorder (m+1) M) : |bulkCDefect m M f v c a|≤K+|c| := by
  apply tiltMean_bound_general (unitSphereLaw (m+1))
    ((bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left)
    ((((bulkC_measurable m M f).comp (measurable_const.prodMk measurable_id)).sub_const c).abs)
    (by positivity)
  intro x
  rw [abs_abs]
  exact (abs_sub _ _).trans (add_le_add (hC a x) le_rfl)

lemma bulkCDefect_integral (m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (c : ℝ) :
    (∫ a,bulkCDefect m M f v c a ∂bulkDisorderLaw (m+1) M)=
      bulkReplicaMean m M f.f v 1 (fun a x=>|bulkC (m+1) M f a.1 (x 0)-c|) := by
  unfold bulkReplicaMean
  apply integral_congr_ae
  filter_upwards [] with a
  symm
  exact gibbsReplicaMean_coordinate_of_integrable (unitSphereLaw (m+1))
    ((bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left)
    ((((bulkC_measurable m M f).comp (measurable_const.prodMk measurable_id)).sub_const c).abs)
    (bulkHamiltonian_exp_integrable m M f.f v a) 1 0

def cavityBulkCompError (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ) (c : ℝ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) : ℝ :=
  Real.log (cavityBulkCompPartition n d m M f v Λ hΛ p)-
    ((n+1:ℕ)/2*c+Real.log (cavityBulkPartition n d m M f v Λ hΛ p))

lemma cavityBulkCompError_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c : ℝ) : Measurable (cavityBulkCompError n d m M f v Λ hΛ c) :=
  (cavityBulkCompPartition_measurable n d m M f v Λ hΛ).log.sub
    ((cavityBulkPartition_measurable n d m M f v Λ hΛ).log.const_add _)

lemma cavityBulkCompError_integrable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c K : ℝ) (hc : |c|≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤K) :
    Integrable (cavityBulkCompError n d m M f v Λ hΛ c)
      ((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))) := by
  apply Integrable.of_bound (cavityBulkCompError_measurable n d m M f v Λ hΛ c).aestronglyMeasurable
    (cavityCompensatorConstant n d f.f Λ K*(K+|c|))
  filter_upwards [] with p
  rw [Real.norm_eq_abs]
  refine (cavityBulkCompPartition_error n d m M f v Λ hΛ c K hc hC p).trans ?_
  exact mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (bulkCDefect_bound m M f v c K ((abs_nonneg _).trans hc) hC p.1))
    (cavityCompensatorConstant_nonneg n d f.f hΛ)

lemma cavityBulkCompError_mean_bound (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c K : ℝ) (hc : |c|≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤K) :
    |∫ p,cavityBulkCompError n d m M f v Λ hΛ c p
      ∂((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M))))|≤
      cavityCompensatorConstant n d f.f Λ K*
        bulkReplicaMean m M f.f v 1 (fun a x=>|bulkC (m+1) M f a.1 (x 0)-c|) := by
  have hE:=cavityBulkCompError_integrable n d m M f v Λ hΛ c K hc hC
  let P:=(bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))
  have hD : Integrable (fun p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)=>
      bulkCDefect m M f v c p.1) P := by
    apply Integrable.of_bound ((bulkCDefect_measurable m M f v c).comp measurable_fst).aestronglyMeasurable (K+|c|)
    exact ae_of_all _ fun p=>by
      simpa only [Real.norm_eq_abs,Function.comp_apply] using bulkCDefect_bound m M f v c K ((abs_nonneg _).trans hc) hC p.1
  refine (abs_integral_le_integral_abs).trans ?_
  calc
    _≤∫ p,cavityCompensatorConstant n d f.f Λ K*bulkCDefect m M f v c p.1 ∂P :=
      integral_mono hE.abs (hD.const_mul _) (fun p=>cavityBulkCompPartition_error n d m M f v Λ hΛ c K hc hC p)
    _=_ := by rw [integral_const_mul,integral_fun_fst]; simp only [probReal_univ,one_smul,bulkCDefect_integral]

theorem cavityBulkCompError_tendsto_zero (n d : ℕ) (N M : ℕ→ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c K : ℝ) (hc : |c|≤K)
    (hC : ∀ j (a : BulkDisorder (N j+1) (M j)) x,|bulkC (N j+1) (M j) f a.1 x|≤K)
    (hL2 : Tendsto (fun j=>bulkReplicaMean (N j) (M j) f.f (v j) 1
      (fun a x=>(bulkC (N j+1) (M j) f a.1 (x 0)-c)^2)) atTop (𝓝 0)) :
    Tendsto (fun j=>∫ p,cavityBulkCompError n d (N j) (M j) f (v j) Λ hΛ c p
      ∂((bulkDisorderLaw (N j+1) (M j)).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d (N j) (M j))))))
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g:=fun j=> -(cavityCompensatorConstant n d f.f Λ K*
      bulkReplicaMean (N j) (M j) f.f (v j) 1 (fun a x=>|bulkC (N j+1) (M j) f a.1 (x 0)-c|)))
    (h:=fun j=>cavityCompensatorConstant n d f.f Λ K*
      bulkReplicaMean (N j) (M j) f.f (v j) 1 (fun a x=>|bulkC (N j+1) (M j) f a.1 (x 0)-c|))
  · simpa using ((bulkC_L1_of_L2 N M f hf v c hL2).const_mul (cavityCompensatorConstant n d f.f Λ K)).neg
  · simpa using (bulkC_L1_of_L2 N M f hf v c hL2).const_mul (cavityCompensatorConstant n d f.f Λ K)
  · intro j; exact (abs_le.mp (cavityBulkCompError_mean_bound n d (N j) (M j) f (v j) Λ hΛ c K hc (hC j))).1
  · intro j; exact (abs_le.mp (cavityBulkCompError_mean_bound n d (N j) (M j) f (v j) Λ hΛ c K hc (hC j))).2

end SphericalPerceptronFreeEnergy
end

end OAI
