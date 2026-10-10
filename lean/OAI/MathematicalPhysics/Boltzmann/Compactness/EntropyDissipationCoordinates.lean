import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionConservation
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionDissipation
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDensityMeasurable

namespace OAI

/-! # The collision-rate dissipation is the physical entropy dissipation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

local instance : SFinite ((volume : Measure BoltzmannNonuniqueness.Velocity).prod
    BoltzmannNonuniqueness.sphereArea) := Measure.prod.instSFinite

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def kernelEntropyProduction (f : X × Velocity → ℝ)
    (p : X × (Velocity × (Velocity × Sphere))) : ℝ≥0∞ :=
  ENNReal.ofReal (collisionKernel p.2.1 p.2.2.1 p.2.2.2) *
    extendedEntropyProduction
      (f (p.1,scatterLeft p.2.1 p.2.2.1 p.2.2.2) *
        f (p.1,scatterRight p.2.1 p.2.2.1 p.2.2.2))
      (f (p.1,p.2.1)*f (p.1,p.2.2.1))

theorem kernelEntropyProduction_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (kernelEntropyProduction f) := by
  have hpost : Measurable (fun p : X × (Velocity × (Velocity × Sphere)) =>
      f (p.1,scatterLeft p.2.1 p.2.2.1 p.2.2.2)*
        f (p.1,scatterRight p.2.1 p.2.2.1 p.2.2.2)) := by
    unfold scatterLeft scatterRight normalComponent
    fun_prop
  have hpre : Measurable (fun p : X × (Velocity × (Velocity × Sphere)) =>
      f (p.1,p.2.1)*f (p.1,p.2.2.1)) := by fun_prop
  have hK : Measurable (fun p : X × (Velocity × (Velocity × Sphere)) =>
      collisionKernel p.2.1 p.2.2.1 p.2.2.2) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact hK.ennreal_ofReal.mul (measurable_extendedEntropyProduction hpost hpre)

def collisionEntropyGrouping : ((X × (Velocity × Velocity)) × Sphere) ≃ᵐ
    X × (Velocity × (Velocity × Sphere)) :=
  collisionGrouping.trans MeasurableEquiv.prodAssoc

theorem collisionEntropyGrouping_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (collisionEntropyGrouping (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (μ.prod ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea))) :=
  (measurePreserving_prodAssoc μ (volume : Measure Velocity)
    ((volume : Measure Velocity).prod sphereArea)).comp (collisionGrouping_measurePreserving μ)

theorem rateProduction_eq_kernel {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    extendedEntropyProduction (postRate f z) (preRate f z) =
      kernelEntropyProduction f (collisionEntropyGrouping z) := by
  rw [postRate_formula]
  change extendedEntropyProduction
    (collisionKernel z.1.2.1 z.1.2.2 z.2*f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*
      f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
    (collisionKernel z.1.2.1 z.1.2.2 z.2*f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)) =
    ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)*extendedEntropyProduction
      (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
      (f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))
  simpa only [mul_assoc] using
    extendedEntropyProduction_scale (collisionKernel_nonneg z.1.2.1 z.1.2.2 z.2)
      (mul_nonneg (hf _) (hf _)) (mul_nonneg (hf _) (hf _))

theorem rateDissipation_eq_kernel {μ : Measure X} [SFinite μ]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    rateDissipation μ f = (4:ℝ≥0∞)⁻¹ * ∫⁻ p, kernelEntropyProduction f p
      ∂μ.prod ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) := by
  unfold rateDissipation
  simp_rw [rateProduction_eq_kernel hf]
  rw [(collisionEntropyGrouping_measurePreserving μ).lintegral_comp
    (kernelEntropyProduction_measurable hfm)]

theorem rateDissipation_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    rateDissipation μ f = rateDissipation μ g := by
  unfold rateDissipation
  congr 1
  apply lintegral_congr_ae
  filter_upwards [postRate_congr hfm hgm he,preRate_congr hfm hgm he] with z hp hq
  rw [hp,hq]

end BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness

theorem kineticDensity_rateDissipation {F : Evolution}
    (hFm : Measurable (fun p : ℝ × Phase => F p.1 p.2))
    (hFn : ∀ t z, 0 ≤ F t z) (T : ℝ) :
    CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume T) (kineticDensity F) =
      ∫⁻ t in Icc (0:ℝ) T, entropyDissipation (F t) := by
  have hkin : Measurable (kineticDensity F) := hFm.comp MeasurableEquiv.prodAssoc.measurable
  rw [CollisionCompactness.rateDissipation_eq_kernel hkin (fun p => hFn _ _)]
  let ν := (volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)
  let G : ℝ × (Position × (Velocity × (Velocity × Sphere))) → ℝ≥0∞ :=
    fun p => CollisionCompactness.kernelEntropyProduction (F p.1) p.2
  have hG : Measurable G := by
    have hm := CollisionCompactness.kernelEntropyProduction_measurable hkin
    change Measurable (fun p : ℝ × (Position × (Velocity × (Velocity × Sphere))) =>
      CollisionCompactness.kernelEntropyProduction (kineticDensity F) ((p.1,p.2.1),p.2.2))
    exact hm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  have he := (measurePreserving_prodAssoc (volume.restrict (Icc (0:ℝ) T))
    (volume : Measure Position) ν).lintegral_comp hG
  change (4:ℝ≥0∞)⁻¹ * ∫⁻ p, G (MeasurableEquiv.prodAssoc p)
    ∂((volume.restrict (Icc (0:ℝ) T)).prod (volume : Measure Position)).prod ν = _
  rw [he,lintegral_prod _ hG.aemeasurable]
  rw [← lintegral_const_mul' _ _ (by norm_num : (4:ℝ≥0∞)⁻¹ ≠ ⊤)]
  rfl

end BoltzmannNonuniqueness

end

end OAI
