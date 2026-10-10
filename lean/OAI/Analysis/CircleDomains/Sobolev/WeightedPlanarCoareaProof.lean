import OAI.Analysis.CircleDomains.Sobolev.RegularCoareaProof
import OAI.Analysis.CircleDomains.Topology.PlaneCriticalFibers

namespace OAI

/-! The planar nonnegative weighted C1 coarea formula. The critical set
is treated by diameter covers, and the regular set by actual inverse
charts, curve arclength, Fubini and change of variables. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

/-- Federer's nonnegative weighted scalar planar coarea identity. -/
theorem weightedPlanarScalarCoarea : WeightedPlanarScalarCoarea := by
  intro D hD f hf q hq
  let R := D ∩ {z | fderiv ℝ f z ≠ 0}
  let C := D ∩ {z | fderiv ℝ f z = 0}
  have hR : WeightedScalarCoareaIdentity R f q := regular_weighted_coarea hD hf hq
  have hCm : MeasurableSet C := measurableSet_planar_critical hD hf
  have hCD : C ⊆ D := inter_subset_left
  have hRC : Disjoint R C := by
    apply disjoint_left.mpr
    intro z hzR hzC
    exact hzR.2 hzC.2
  have hDC : D = R ∪ C := by
    ext z
    simp only [R, C, mem_union, mem_inter_iff, mem_ofPred_eq]
    tauto
  have hCzero : ∀ᵐ t, weightedScalarLevelLength C f q t = 0 :=
    ae_zero_weighted_planar_critical_fiber hD hf q
  have hsplit (t : ℝ) : weightedScalarLevelLength D f q t =
      weightedScalarLevelLength R f q t + weightedScalarLevelLength C f q t := by
    unfold weightedScalarLevelLength
    rw [hDC, union_inter_distrib_right]
    exact lintegral_union (measurableSet_restricted_scalar_level hD hf.continuousOn hCm hCD t)
      (hRC.mono inter_subset_left inter_subset_left)
  have heq : weightedScalarLevelLength D f q =ᵐ[volume] weightedScalarLevelLength R f q := by
    filter_upwards [hCzero] with t ht
    rw [hsplit t, ht, add_zero]
  have hCE : (∫⁻ z in C, q z * ENNReal.ofReal ‖fderiv ℝ f z‖) = 0 := by
    apply setLIntegral_eq_zero hCm
    intro z hz
    change q z * ENNReal.ofReal ‖fderiv ℝ f z‖ = 0
    have hz0 : fderiv ℝ f z = 0 := hz.2
    rw [hz0, norm_zero, ENNReal.ofReal_zero, mul_zero]
  refine ⟨hR.1.congr heq.symm, ?_⟩
  calc
    (∫⁻ t, weightedScalarLevelLength D f q t) = ∫⁻ t, weightedScalarLevelLength R f q t :=
      lintegral_congr_ae heq
    _ = ∫⁻ z in R, q z * ENNReal.ofReal ‖fderiv ℝ f z‖ := hR.2
    _ = ∫⁻ z in D, q z * ENNReal.ofReal ‖fderiv ℝ f z‖ := by
      conv_rhs => rw [hDC, lintegral_union hCm hRC, hCE, add_zero]

end CircleDomainRigidity

end

end OAI
