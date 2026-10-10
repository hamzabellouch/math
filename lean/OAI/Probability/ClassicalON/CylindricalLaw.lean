import OAI.Probability.ClassicalON.CylindricalFiber

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ClassicalON

def cylinderLaw : Measure (Bool×PlanarAngle) := signLaw.prod angleLaw
instance cylinderLaw_isProbability : IsProbabilityMeasure cylinderLaw := by
  unfold cylinderLaw; infer_instance

def sphericalAmplitudeLaw : Measure Amplitude := (sphereProbability 3).map firstAmplitude
instance sphericalAmplitudeLaw_isProbability : IsProbabilityMeasure sphericalAmplitudeLaw :=
  (Measure.isProbabilityMeasure_map_iff continuous_firstAmplitude.measurable.aemeasurable).2 inferInstance

theorem integral_signLaw (f : Bool → ℝ) : (∫ τ,f τ ∂signLaw)=(f false+f true)/2 := by
  simp [signLaw,integral_smul_measure,integral_count,div_eq_mul_inv]
  ring

theorem integral_cylinderLaw (f : Bool×PlanarAngle → ℝ) (hf : Continuous f) :
    (∫ p,f p ∂cylinderLaw)=((∫ θ,f (false,θ) ∂angleLaw)+(∫ θ,f (true,θ) ∂angleLaw))/2 := by
  rw [cylinderLaw,integral_prod _ (compact_integrable hf),integral_signLaw]

theorem cylinder_orbit_average (f : Spin 3 → ℝ) (hf : Continuous f) (s : Spin 3) :
    (∫ p,f (spinRotation (cylinderRotation p.1 p.2) s) ∂cylinderLaw)=
      ∫ p,f (cylindricalSpin (firstAmplitude s) p.1 p.2) ∂cylinderLaw := by
  obtain ⟨υ,φ,hspin⟩ := cylindricalSpin_surjective_fiber s
  have he (p : Bool×PlanarAngle) :
      spinRotation (cylinderRotation p.1 p.2) s=
        cylindricalSpin (firstAmplitude s) (p.1==υ) (p.2+φ) := by
    conv_lhs => rw [← hspin]
    rw [cylinderRotation_cylindricalSpin]
  simp_rw [he]
  have hc : Continuous (fun p : Bool×PlanarAngle => f (cylindricalSpin (firstAmplitude s) p.1 p.2)) :=
    hf.comp (continuous_cylindricalSpin.comp (continuous_const.prodMk continuous_id))
  have hm : Continuous (fun p : Bool×PlanarAngle => (p.1==υ,p.2+φ)) :=
    ((show Continuous (fun τ : Bool => τ==υ) from continuous_of_discreteTopology).comp continuous_fst).prodMk
      (continuous_snd.add continuous_const)
  have hh : Continuous (fun p : Bool×PlanarAngle => f (cylindricalSpin (firstAmplitude s) (p.1==υ) (p.2+φ))) := hc.comp hm
  rw [integral_cylinderLaw _ hh,integral_cylinderLaw _ hc]
  have hshift (τ : Bool) :
      (∫ θ,f (cylindricalSpin (firstAmplitude s) τ (θ+φ)) ∂angleLaw)=
        ∫ θ,f (cylindricalSpin (firstAmplitude s) τ θ) ∂angleLaw :=
    integral_add_right_eq_self (fun θ => f (cylindricalSpin (firstAmplitude s) τ θ)) φ
  cases υ <;> simp only [Bool.false_beq,Bool.true_beq,Bool.not_false,Bool.not_true]
  all_goals rw [hshift,hshift]
  all_goals ring

theorem integral_sphere_orbit (f : Spin 3 → ℝ) (hf : Continuous f) :
    (∫ s,∫ p,f (spinRotation (cylinderRotation p.1 p.2) s) ∂cylinderLaw ∂sphereProbability 3)=
      ∫ s,f s ∂sphereProbability 3 := by
  have hcont : Continuous (fun p : Spin 3×(Bool×PlanarAngle) => f (spinRotation (cylinderRotation p.2.1 p.2.2) p.1)) :=
    hf.comp (continuous_cylinderSpinRotation.comp (f := (Prod.swap : Spin 3×(Bool×PlanarAngle) → (Bool×PlanarAngle)×Spin 3)) continuous_swap)
  have hi := integral_integral_swap (μ := sphereProbability 3) (ν := cylinderLaw)
    (f := fun s p => f (spinRotation (cylinderRotation p.1 p.2) s))
    (compact_integrable hcont)
  rw [hi]
  have hp (p : Bool×PlanarAngle) :
      (∫ s,f (spinRotation (cylinderRotation p.1 p.2) s) ∂sphereProbability 3)=∫ s,f s ∂sphereProbability 3 :=
    (spinRotation_preserves_probability _).integral_comp (spinRotation _).measurableEmbedding f
  simp_rw [hp]
  simp

theorem integral_sphere_cylinder (f : Spin 3 → ℝ) (hf : Continuous f) :
    (∫ s,f s ∂sphereProbability 3)=
      ∫ r,∫ p,f (cylindricalSpin r p.1 p.2) ∂cylinderLaw ∂sphericalAmplitudeLaw := by
  have hc : Continuous (fun p : Amplitude×(Bool×PlanarAngle) => f (cylindricalSpin p.1 p.2.1 p.2.2)) :=
    hf.comp continuous_cylindricalSpin
  have hm : Continuous (fun r => ∫ p,f (cylindricalSpin r p.1 p.2) ∂cylinderLaw) :=
    compact_parametric_integral _ hc
  rw [sphericalAmplitudeLaw,integral_map continuous_firstAmplitude.measurable.aemeasurable hm.measurable.aestronglyMeasurable]
  calc
    _ = ∫ s,∫ p,f (spinRotation (cylinderRotation p.1 p.2) s) ∂cylinderLaw ∂sphereProbability 3 :=
      (integral_sphere_orbit f hf).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (cylinder_orbit_average f hf))

theorem cylindricalSpin_preserves : MeasurePreserving
    (fun p : Amplitude×Bool×PlanarAngle => cylindricalSpin p.1 p.2.1 p.2.2)
    (sphericalAmplitudeLaw.prod cylinderLaw) (sphereProbability 3) := by
  refine ⟨continuous_cylindricalSpin.measurable,?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hc : Continuous (fun p : Amplitude×Bool×PlanarAngle => f (cylindricalSpin p.1 p.2.1 p.2.2)) :=
    f.continuous.comp continuous_cylindricalSpin
  rw [integral_map (f := fun x => f x) continuous_cylindricalSpin.measurable.aemeasurable f.continuous.aestronglyMeasurable,
    integral_prod _ (compact_integrable hc)]
  exact (integral_sphere_cylinder f f.continuous).symm

end ClassicalON

end

end OAI
