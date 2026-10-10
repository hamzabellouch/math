import Mathlib
import OAI.Probability.Perceptron.Sphere.SphereIsometryMap
import OAI.Probability.Perceptron.Variational.TensorFeatures

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

def unitSphereAmbientLaw (N : ℕ) : Measure (Spin N) :=
  (unitSphereLaw N).map (fun x : NormalizedSpin N => x.val)

instance unitSphereAmbientLaw_probability (n : ℕ) : IsProbabilityMeasure (unitSphereAmbientLaw (n+1)) := by
  unfold unitSphereAmbientLaw
  apply (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).2
  have : NeZero ((volume : Measure (Spin (n+1))).toSphere) :=
    ⟨Measure.toSphere_ne_zero volume⟩
  unfold unitSphereLaw
  infer_instance

lemma unitSphereAmbientLaw_norm (N : ℕ) : ∀ᵐ x ∂unitSphereAmbientLaw N, ‖x‖=1 := by
  apply (ae_map_iff measurable_subtype_coe.aemeasurable (measurableSet_eq_fun continuous_norm.measurable measurable_const)).mpr
  exact ae_of_all _ fun x => by simpa only [Metric.mem_sphere,dist_zero_right] using x.property

lemma unitSphereAmbientLaw_preserving {N : ℕ} (e : Spin N≃ₗᵢ[ℝ]Spin N) :
    MeasurePreserving e (unitSphereAmbientLaw N) (unitSphereAmbientLaw N) := by
  refine ⟨e.continuous.measurable,?_⟩
  rw [unitSphereAmbientLaw,Measure.map_map e.continuous.measurable measurable_subtype_coe]
  have he : e ∘ (fun x : NormalizedSpin N => x.val) =
      (fun x : NormalizedSpin N => x.val) ∘ sphereIsometryMap e := rfl
  rw [he,← Measure.map_map measurable_subtype_coe (sphereIsometryMap_measurable e),
    (unitSphereLaw_isometry_preserving e).map_eq]

lemma unitSphere_tangent_integral (n : ℕ) (y : Spin (n+1)) {F : Spin (n+1)→ℝ}
    (hF : ContDiff ℝ 1 F) :
    (∫ x : NormalizedSpin (n+1), fderiv ℝ F x.val (y-inner ℝ y x.val • x.val) ∂unitSphereLaw (n+1)) =
      (n:ℝ)*(∫ x : NormalizedSpin (n+1), inner ℝ y x.val*F x.val ∂unitSphereLaw (n+1)) := by
  have he := invariant_tangent_integral (unitSphereAmbientLaw (n+1))
    ((unitSphereAmbientLaw_norm (n+1)).mono fun _ h => h.le)
    (fun e => unitSphereAmbientLaw_preserving e) (Fin (n+1))
    (EuclideanSpace.basisFun (Fin (n+1)) ℝ) y hF
  have hleft : AEStronglyMeasurable (fun x : Spin (n+1) => fderiv ℝ F x ((‖x‖^2) • y-inner ℝ y x • x))
      (unitSphereAmbientLaw (n+1)) :=
    ((hF.continuous_fderiv (by norm_num)).clm_apply (by fun_prop)).aestronglyMeasurable
  have hright : AEStronglyMeasurable (fun x : Spin (n+1) => ((Fintype.card (Fin (n+1)):ℝ)-1)*inner ℝ y x*F x)
      (unitSphereAmbientLaw (n+1)) := (by fun_prop : Continuous _).aestronglyMeasurable
  rw [unitSphereAmbientLaw,integral_map measurable_subtype_coe.aemeasurable hleft,
    integral_map measurable_subtype_coe.aemeasurable hright] at he
  have hn (x : NormalizedSpin (n+1)) : ‖x.val‖=1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using x.property
  simpa only [hn,one_pow,one_smul,Fintype.card_fin,Nat.cast_add,Nat.cast_one,
    add_sub_cancel_right,mul_assoc,integral_const_mul] using he

lemma unitSphere_gibbs_tangent_integral (n : ℕ) (y : NormalizedSpin (n+1))
    {H : Spin (n+1)→ℝ} (hH : ContDiff ℝ 1 H) {G : ℝ→ℝ} (hG : ContDiff ℝ 1 G) :
    (n:ℝ)*(∫ x : NormalizedSpin (n+1), spinOverlap y x*(G (spinOverlap y x)*Real.exp (H x.val))
      ∂unitSphereLaw (n+1)) =
    ∫ x : NormalizedSpin (n+1),
      (deriv G (spinOverlap y x)*(1-spinOverlap y x^2)+G (spinOverlap y x)*
        fderiv ℝ H x.val (y.val-spinOverlap y x • x.val))*Real.exp (H x.val) ∂unitSphereLaw (n+1) := by
  let F : Spin (n+1)→ℝ := fun x => G (inner ℝ y.val x)*Real.exp (H x)
  have hF : ContDiff ℝ 1 F := (hG.comp (innerSL ℝ y.val).contDiff).mul hH.exp
  change (n:ℝ)*(∫ x : NormalizedSpin (n+1), inner ℝ y.val x.val*F x.val ∂unitSphereLaw (n+1)) = _
  rw [← unitSphere_tangent_integral n y.val hF]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    have hd := (((hG.differentiable (by norm_num) (inner ℝ y.val x.val)).hasDerivAt.comp_hasFDerivAt x.val
      (innerSL ℝ y.val).hasFDerivAt).mul (hH.differentiable (by norm_num) x.val).hasFDerivAt.exp).fderiv
    change fderiv ℝ F x.val (y.val-spinOverlap y x • x.val)=_
    have he : fderiv ℝ F x.val = G (spinOverlap y x) • (Real.exp (H x.val) • fderiv ℝ H x.val)+
        Real.exp (H x.val) • (deriv G (spinOverlap y x) • innerSL ℝ y.val) := by
      simpa only [F,spinOverlap,Function.comp_def,Pi.mul_def] using hd
    rw [he]
    have hy : ‖y.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using y.property
    simp only [add_apply,smul_apply,smul_eq_mul,
      coe_innerSL_apply,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hy,one_pow,spinOverlap]
    ring

end SphericalPerceptronFreeEnergy
end

end OAI
