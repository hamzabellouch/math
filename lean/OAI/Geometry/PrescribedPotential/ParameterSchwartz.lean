import Mathlib
import OAI.Geometry.PrescribedPotential.ParameterRegularity
import OAI.Geometry.PrescribedPotential.SmoothDistributions

namespace OAI

/-! Parameter Schwartz. -/

section

 

noncomputable section
open Filter Topology MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Real ComplexOrder MatrixOrder

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartz_mul_temperate_distribution (a : 𝓢(E, ℂ)) {h : E → ℂ}
    (hh : h.HasTemperateGrowth) :
    ((SchwartzMap.smulLeftCLM ℂ h a : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) =
      smulLeftCLM ℂ a (hh.toTemperedDistribution volume) := by
  ext φ
  simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply,
    smulLeftCLM_apply_apply, Function.HasTemperateGrowth.toTemperedDistribution_apply,
    SchwartzMap.smulLeftCLM_apply_apply hh,
    SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

 

def representativePerturbation {ι : Type*} [Fintype ι] (v : ι → E)
    (a : SmoothCoefficients ι E) (u : E → ℂ) : 𝓢(E, ℂ) :=
  ∑ i, ∑ j, SchwartzMap.smulLeftCLM ℂ
    (directionDerivative (v i) (directionDerivative (v j) u)) (a i j)

lemma representativePerturbation_distribution {ι : Type*} [Fintype ι] (v : ι → E)
    (a : SmoothCoefficients ι E) {u : E → ℂ} (hu : u.HasTemperateGrowth) (w : L2 E)
    (hw : hu.toTemperedDistribution volume = realize 2 w) :
    ((representativePerturbation v a u : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) =
      (perturbation v (coefficientBCF a) w : 𝓢'(E, ℂ)) := by
  rw [perturbation_distribution v _ (fun i j => (a i j).hasTemperateGrowth)]
  simp only [representativePerturbation, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [schwartz_mul_temperate_distribution (a i j)
    (temperate_directionDerivative (v i) (temperate_directionDerivative (v j) hu)),
    temperateDistribution_derivative (v i) (temperate_directionDerivative (v j) hu),
    temperateDistribution_derivative (v j) hu, hw]
  rfl

end SobolevChart

namespace FrozenPoisson.ParameterRegularity
open FrozenPoisson SobolevChart EllipticKernel
variable {n : ℕ} {ι : Type*} [Fintype ι]

 

theorem exists_schwartz_local (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
    (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1)
    (f : 𝓢(EC n, ℂ)) :
    ∃ u : 𝓢(EC n, ℂ), SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume u =
      realize 2 (parameterLocal H hH t ht v (coefficientBCF a) hsmall (schwartzCoord 0 f)) := by
  let w := parameterLocal H hH t ht v (coefficientBCF a) hsmall (schwartzCoord 0 f)
  obtain ⟨u, hu, he⟩ := all_even_smooth_representative
    (parameterLocal_schwartz_memSobolev H hH t ht v a hsmall f)
  have he' : hu.toTemperedDistribution volume = realize 2 w := by
    rw [temperateDistribution_bounded]
    exact he
  let F := f + representativePerturbation v a u
  refine ⟨schwartzResolvent H t F, ?_⟩
  rw [schwartzResolvent_distribution H hH t ht]
  have hF : SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume F =
      SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume f +
      (perturbation v (coefficientBCF a) w : 𝓢'(EC n, ℂ)) := by
    simp only [F, map_add, representativePerturbation_distribution v a hu w he']
  rw [hF]
  have hfixed := congrArg (realize (E := EC n) 2)
    (parameterLocal_fixed H hH t ht v (coefficientBCF a) hsmall (schwartzCoord 0 f))
  have hr := parameterHilbert_realize H hH t ht 0
    (schwartzCoord 0 f + perturbation v (coefficientBCF a) w)
  norm_num only [zero_add] at hr
  rw [hr, map_add, realize_schwartzCoord] at hfixed
  simpa only [realize, neg_zero, besselPotential_zero, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, Lp.toTemperedDistributionCLM_apply] using hfixed.symm

 

def schwartzLocalValue (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
    (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1)
    (f : 𝓢(EC n, ℂ)) : 𝓢(EC n, ℂ) :=
  (exists_schwartz_local H hH t ht v a hsmall f).choose

lemma schwartzLocalValue_distribution (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
    (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1)
    (f : 𝓢(EC n, ℂ)) :
    SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume
      (schwartzLocalValue H hH t ht v a hsmall f) =
      realize 2 (parameterLocal H hH t ht v (coefficientBCF a) hsmall (schwartzCoord 0 f)) :=
  (exists_schwartz_local H hH t ht v a hsmall f).choose_spec

def schwartzLocal (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
    (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1) :
    𝓢(EC n, ℂ) →ₗ[ℂ] 𝓢(EC n, ℂ) where
  toFun := schwartzLocalValue H hH t ht v a hsmall
  map_add' f g := by
    apply schwartz_distribution_injective
    simp only [map_add, schwartzLocalValue_distribution, schwartzCoord_add]
  map_smul' c f := by
    apply schwartz_distribution_injective
    have hc : schwartzCoord 0 (c • f) = c • schwartzCoord 0 f := by
      apply realize_injective 0
      simp only [map_smul, realize_schwartzCoord]
    simp only [map_smul, schwartzLocalValue_distribution, hc, RingHom.id_apply]

lemma schwartzLocal_coord (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
    (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1)
    (f : 𝓢(EC n, ℂ)) :
    schwartzCoord 2 (schwartzLocal H hH t ht v a hsmall f) =
      parameterLocal H hH t ht v (coefficientBCF a) hsmall (schwartzCoord 0 f) := by
  apply realize_injective 2
  rw [realize_schwartzCoord]
  exact schwartzLocalValue_distribution H hH t ht v a hsmall f

end FrozenPoisson.ParameterRegularity

end
end

end OAI
