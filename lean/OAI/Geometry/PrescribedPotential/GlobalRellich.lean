import Mathlib
import OAI.Geometry.PrescribedPotential.FrequencyApprox
import OAI.Geometry.PrescribedPotential.GlobalSmooth
import OAI.Geometry.PrescribedPotential.PatchCutoffs

namespace OAI

/-! Global Rellich. -/

section

 
noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ContDiff Classical BoundedContinuousFunction
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma realize_zero (u : L2 E) : realize 0 u = (u : 𝓢'(E, ℂ)) := by
  simp only [realize, neg_zero, ContinuousLinearMap.comp_apply,
    besselPotential_zero, ContinuousLinearMap.id_apply, Lp.toTemperedDistributionCLM_apply]

lemma bessel_lower_two (u : L2 E) :
    (multiplier (inverseWeight 1) u : 𝓢'(E, ℂ)) = realize 2 u := by
  rw [multiplier_distribution _ (inverseWeight_temperate 1)]
  simp only [realize, ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply]
  rw [besselPotential]
  have heq : (inverseWeight (E := E) 1 : E → ℂ) =
      (fun x : E => (((1+‖x‖^2)^(-(2:ℝ)/2) : ℝ) : ℂ)) := by
    funext x
    change (((1+‖x‖^2)^(-((1:ℕ):ℝ)) : ℝ) : ℂ) = _
    norm_num
  rw [heq]

end SobolevChart
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma cutoff_coordinate (p : ι) (u : D.localizers.Sobolev 0) :
    multiply (D.cutoff p).val.toBoundedContinuousFunction (u.val p) = u.val p := by
  apply l2_injective
  simp only [Lp.toTemperedDistributionCLM_apply]
  rw [multiply_distribution _ (D.cutoff p).val.hasTemperateGrowth]
  have hd : D.localizers.distribution 0 p u = (u.val p : 𝓢'(EC d, ℂ)) := realize_zero _
  rw [← hd]
  exact D.cutoff_distribution p u

lemma lower_coordinate (p : ι) (u : D.localizers.Sobolev 2) :
    (D.localizers.lower 2 0 u).val p = multiplier (inverseWeight 1) (u.val p) := by
  apply l2_injective
  simp only [Lp.toTemperedDistributionCLM_apply]
  rw [bessel_lower_two]
  rw [← realize_zero]
  exact D.localizers.distribution_lower (by norm_num : (0 : ℝ) ≤ 2) p u

 

theorem lower_compact : IsCompactOperator (D.localizers.lower 2 0) := by
  let T (p : ι) : D.localizers.Sobolev 2 →L[ℝ] D.localizers.Sobolev 0 :=
    D.localizers.globalizeL2 (D.patch p).index (D.cutoff p) ∘L
      (multiply (D.cutoff p).val.toBoundedContinuousFunction ∘L
        multiplier (inverseWeight 1)).restrictScalars ℝ ∘L
      (ContinuousLinearMap.proj p) ∘L (D.localizers.closedSpace 2).subtypeL
  have hT (p : ι) : IsCompactOperator (T p) := by
    have ht := ((EllipticCompact.localized_bessel_compact (D.cutoff p).val (D.cutoff p).compact).comp_clm
      ((ContinuousLinearMap.proj p) ∘L (D.localizers.closedSpace 2).subtypeL)).clm_comp
      (D.localizers.globalizeL2 (D.patch p).index (D.cutoff p))
    simpa only [T, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_restrictScalars',
      Function.comp_assoc] using ht
  have he : D.localizers.lower 2 0 = ∑ p, T p := by
    ext1 u
    rw [← D.reconstruct_eq (D.localizers.lower 2 0 u), D.reconstruct_apply]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro p _
    change D.localizers.globalizeL2 (D.patch p).index (D.cutoff p)
      ((D.localizers.lower 2 0 u).val p) =
      D.localizers.globalizeL2 (D.patch p).index (D.cutoff p)
        (multiply (D.cutoff p).val.toBoundedContinuousFunction
          (multiplier (inverseWeight 1) (u.val p)))
    rw [← D.lower_coordinate p u, D.cutoff_coordinate]
  rw [he]
  classical
  have hh (S : Finset ι) : IsCompactOperator (∑ p ∈ S, T p : D.localizers.Sobolev 2 →L[ℝ] D.localizers.Sobolev 0) := by
    induction S using Finset.induction_on with
    | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : D.localizers.Sobolev 2 →L[ℝ] D.localizers.Sobolev 0))
    | @insert p S hp ih =>
      simpa only [Finset.sum_insert hp, FunLike.coe_add] using (hT p).add ih
  exact hh Finset.univ

end GluingData
end GlobalElliptic

end
end

end OAI
