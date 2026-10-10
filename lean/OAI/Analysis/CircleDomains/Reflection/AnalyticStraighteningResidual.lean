import OAI.Analysis.CircleDomains.Reflection.AnalyticReflectionData
import OAI.Analysis.CircleDomains.Reflection.PrincipalBeltramiResidual
import OAI.Analysis.CircleDomains.Modulus.StrongWeightedPullback

namespace OAI

/-! The actual pulled-back principal approximants have antiholomorphic
error tending strongly to zero on the original analytic domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

def straighteningApproximation (D : AnalyticReflectionData C) (n : ℕ) : ℂ → ℂ :=
  (D.approximation.map (D.limitData.index n)) ∘ D.comparison

lemma exists_straightening_residual (D : AnalyticReflectionData C) :
    ∃q : ℕ → PlaneL2,Tendsto q atTop (𝓝 0) ∧
      ∀n,∀ᵐ(z : ℂ) ∂volume,(z : Sphere)∈C.region →
        partialBar (D.straighteningApproximation n) z=q n z := by
  let μ := fun z : ℂ => D.extension (z : Sphere)
  have hμ : MemLp μ 2 volume := compact_coefficient_memLp
    ((D.extension_measurable.comp OnePoint.continuous_coe.measurable).aestronglyMeasurable)
    (isCompact_closedBall 0 D.supportRadius) D.bound_nonneg
    (fun z => D.extension_bound (z : Sphere)) (fun z hz => D.extension_zero z
      (le_of_lt (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz)))
  obtain ⟨e,he,her⟩ := D.approximation.exists_strong_beltrami_residual μ hμ D.bound_nonneg
    (.of_forall fun z => D.extension_bound (z : Sphere)) D.density_equation
  let P := D.comparison
  let K := (1+D.bound)/(1-D.bound)
  have hK : 0≤K := div_nonneg (by linarith [D.bound_nonneg]) (by linarith [D.bound_lt_one])
  have hdist := (smooth_beltrami_two_sided_distortion P.symm D.comparison_inverse_smooth
    D.comparison_smooth D.baseCoefficient D.bound_nonneg D.bound_lt_one D.base_bound D.base_equation).2
  obtain ⟨q,hq,hqr⟩ := exists_strong_weighted_pullback P D.comparison_smooth D.comparison_inverse_smooth
    hK hdist e he
  have hPq := differentiable_homeomorph_quasiMeasurePreserving P
    (D.comparison_inverse_smooth.differentiable (by simp))
  refine ⟨q ∘ D.limitData.index,hq.comp D.limitData.index_strict.tendsto_atTop,?_⟩
  intro n
  let j := D.limitData.index n
  filter_upwards [hqr j,hPq.ae (her j)] with z hqz hez hz
  have hbase : D.extension (P z : Sphere)=D.baseCoefficient (P z) :=
    D.extension_base (mem_image_of_mem D.comparison.onePointCongr hz)
  change partialBar (D.approximation.map j ∘ P) z=q j z
  rw [smooth_beltrami_pullback_cancellation P D.comparison_smooth D.comparison_inverse_smooth
    D.baseCoefficient D.base_equation (D.approximation.smooth j |>.differentiable (by simp) (P z))]
  rw [hqz,hez]
  change (partialBar (D.approximation.map j) (P z)-D.baseCoefficient (P z)*
      partialZ (D.approximation.map j) (P z))*star (partialZ P z)=
    (partialBar (D.approximation.map j) (P z)-D.extension (P z : Sphere)*
      partialZ (D.approximation.map j) (P z))*star (partialZ P z)
  rw [hbase]

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
