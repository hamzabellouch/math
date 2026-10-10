import OAI.Geometry.Kahler.BaseRadialMoments

namespace OAI

universe uKahler9159_1 uKahler9161_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def radialUnit (ξ : Sphere) : unitInterval :=
  ⟨radialU ξ,Complex.normSq_nonneg _,by
    have hv : 0 ≤ radialV ξ := Complex.normSq_nonneg _
    linarith [radialUV ξ]⟩

lemma radialUnit_continuous : Continuous radialUnit := radialU_continuous.subtype_mk _

lemma unit_moment (n : ℕ) : (∫ t : unitInterval, (t:ℝ)^n) = 1/(n+1:ℝ) := by
  rw [unitInterval.volume_def,integral_subtype_comap measurableSet_Icc (fun t : ℝ => t^n)]
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),integral_pow]
  simp

private def integralCM {X : Type uKahler9159_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {Y : Type uKahler9161_1} [TopologicalSpace Y] [CompactSpace Y] (g : X → Y) (hg : Continuous g) :
    C(Y,ℝ) →L[ℝ] ℝ :=
  ({ toFun := fun f => ∫ x, f (g x) ∂μ
     map_add' := fun f h => integral_add
       ((f.continuous.comp hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
       ((h.continuous.comp hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
     map_smul' := fun r f => by simp only [ContinuousMap.smul_apply,smul_eq_mul,integral_const_mul,RingHom.id_apply] } : C(Y,ℝ) →ₗ[ℝ] ℝ).mkContinuous 1 (by
    intro f
    simpa using norm_integral_le_of_norm_le_const (μ := μ)
      (Eventually.of_forall (fun x => f.norm_coe_le_norm (g x))))

lemma radial_polynomial_integral (p : Polynomial ℝ) :
    (∫ ξ, p.eval (radialU ξ) ∂sigma) = ∫ t : unitInterval, p.eval (t:ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    rw [integral_add,integral_add,hp,hq]
    all_goals first
      | exact continuous_integrable (p.continuous.comp radialU_continuous)
      | exact continuous_integrable (q.continuous.comp radialU_continuous)
      | exact (p.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      | exact (q.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  | monomial n a =>
    simp only [Polynomial.eval_monomial,integral_const_mul,radial_moment,unit_moment]

lemma radial_continuous_integral (f : C(unitInterval,ℝ)) :
    (∫ ξ, f (radialUnit ξ) ∂sigma) = ∫ t : unitInterval, f t := by
  let L := integralCM sigma radialUnit radialUnit_continuous
  let R := integralCM (volume : Measure unitInterval) id continuous_id
  have hc : IsClosed {f : C(unitInterval,ℝ) | L f = R f} := isClosed_eq L.continuous R.continuous
  have hpoly : (polynomialFunctions (Icc (0:ℝ) 1) : Set C(unitInterval,ℝ)) ⊆ {f | L f = R f} := by
    rw [polynomialFunctions_coe]
    rintro _ ⟨p,rfl⟩
    exact radial_polynomial_integral p
  have hcl := hc.closure_subset_iff.mpr hpoly
  have hd : closure (polynomialFunctions (Icc (0:ℝ) 1) : Set C(unitInterval,ℝ)) = univ := by
    simpa only [Subalgebra.topologicalClosure_coe,show ((⊤ : Subalgebra ℝ C(unitInterval,ℝ)) : Set C(unitInterval,ℝ)) = univ from rfl] using
      congrArg (fun A : Subalgebra ℝ C(unitInterval,ℝ) => (A : Set C(unitInterval,ℝ)))
        (polynomialFunctions.topologicalClosure (Icc (0:ℝ) 1))
  exact hcl (by rw [hd]; trivial)

lemma radial_law : Measure.map radialUnit sigma = (volume : Measure unitInterval) := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_map (f := fun x => f x) radialUnit_continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact radial_continuous_integral f.toContinuousMap

end PinchedHartogs.BaseConstruction

end

end OAI
