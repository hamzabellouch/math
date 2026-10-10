import OAI.Probability.SLE.Loewner.CanonicalRadiusKernel
import OAI.Probability.SLE.Geometry.SpatialPastKernels
import OAI.Probability.SLE.Stochastic.DriverPastFactorization
import OAI.Probability.SLE.Mass.GreenMeasureSupport

namespace OAI

/-! The canonical Green measure at a deterministic time uses only the
continuous driver prefix. This is a pathwise ODE fact, before any law is fixed. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

local instance greenPastDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance greenPastDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma canonicalGreen_eq_of_agree (κ : ℝ) (T : ℝ≥0)
    (p q : C(ℝ≥0,ℝ)) (hpq : ∀ s ≤ T, p s=q s) (z : ℂ) :
    canonicalGreen κ (T,z,p)=canonicalGreen κ (T,z,q) := by
  let c := canonicalRadiusFamily κ
  have hQ (n : ℕ) : c.Q n T (z,p)=c.Q n T (z,q) := by
    apply clipped_flow_eqOn_prefix (-(n:ℝ)) n _ T
      (fun s hs => congrArg (fun x => Real.sqrt κ*x) (hpq s hs))
      (c.derivative n z p) (c.derivative n z q)
      (by rw [c.initial,c.initial])
    exact ⟨T.coe_nonneg,le_rfl⟩
  have hv (n : ℕ) : c.valid n T z p ↔ c.valid n T z q := by
    simp only [SpatialClippedFamily.valid,hQ]
  change c.jointGreen κ (fun s r => r s) (T,z,p) =
    c.jointGreen κ (fun s r => r s) (T,z,q)
  unfold SpatialClippedFamily.jointGreen
  congr 1
  funext n
  simp only [SpatialClippedFamily.greenApprox,hv,hQ,hpq T le_rfl]

def canonicalGreenMass (κ : ℝ) (t : ℝ≥0) (p : C(ℝ≥0,ℝ)) :
    Measure upperHalfPlane :=
  (volume.withDensity (fun z => ENNReal.ofReal (canonicalGreen κ (t,z,p)))).comap Subtype.val

lemma canonicalGreenMass_measurable (κ : ℝ) (t : ℝ≥0) :
    Measurable (canonicalGreenMass κ t) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [canonicalGreenMass,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    withDensity_apply _ hAI]
  have hg : Measurable (fun x : C(ℝ≥0,ℝ) × ℂ => canonicalGreen κ (t,x.2,x.1)) :=
    (canonicalGreen_measurable κ).comp
      (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))
  exact hg.ennreal_ofReal.lintegral_prod_right'

lemma canonicalGreenMass_eq_of_agree (κ : ℝ) (t : ℝ≥0)
    (p q : C(ℝ≥0,ℝ)) (hpq : ∀ s ≤ t, p s=q s) :
    canonicalGreenMass κ t p=canonicalGreenMass κ t q := by
  unfold canonicalGreenMass
  congr 2
  funext z
  rw [canonicalGreen_eq_of_agree κ t p q hpq z]

lemma canonicalGreenMass_measurable_past (κ : ℝ) (t : ℝ≥0) :
    Measurable[driverPathFiltration t] (canonicalGreenMass κ t) := by
  have h := (canonicalGreenMass_measurable κ t).comp (driverPathStopped_measurable_past t)
  convert h using 1
  funext p
  apply canonicalGreenMass_eq_of_agree
  intro s hs
  simp only [driverPathStopped,ContinuousMap.coe_mk,min_eq_left hs]

lemma canonicalGreenMass_eq (κ : ℝ) (p : C(ℝ≥0,ℝ))
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*p t) γ G F) (t : ℝ≥0) :
    canonicalGreenMass κ t p =
      (volume.withDensity (fun z => ENNReal.ofReal
        (greenDensity κ (fun s => Real.sqrt κ*p s) γ G t z))).comap Subtype.val := by
  unfold canonicalGreenMass
  congr 2
  funext z
  rw [canonicalGreen_eq κ p hw t z]

end SLEExactGauge.Multipoint

end

end OAI
