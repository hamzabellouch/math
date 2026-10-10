import OAI.Analysis.CircleDomains.Sobolev.TransportedRealEnergy
import OAI.Analysis.CircleDomains.Topology.ConformalSphericalMetric
import OAI.Analysis.CircleDomains.Sobolev.RealGradientNorm
import OAI.Analysis.CircleDomains.Sobolev.ComplexSobolevTransport
import OAI.Analysis.CircleDomains.Sobolev.SphericalGradientEnergyNorm

namespace OAI

/-! The conformal energy identity in the Euclidean-plane
coordinates used by the Sobolev witnesses. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

def planeInverseTransport (fi : Sphere → Sphere) (u : EuclideanPlane → ℝ) :
    EuclideanPlane → ℝ :=
  u ∘ euclideanPlaneCoordinates.symm ∘ sphereRealMap fi ∘ euclideanPlaneCoordinates

 theorem smooth_plane_energy_transport
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (hf : IsConformalOn f U) {u : EuclideanPlane → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (physicalPlaneDomain U))
    (hgrad : ∀ i : Fin 2, MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain U))) :
    ContDiffOn ℝ 1 (planeInverseTransport fi u) (physicalPlaneDomain V) ∧
    (∀ i : Fin 2, MemLp (fun x => fderiv ℝ (planeInverseTransport fi u) x
      (EuclideanSpace.single i 1)) 2 (volume.restrict (physicalPlaneDomain V))) ∧
    (∫ x in physicalPlaneDomain V,
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 0 1)) ^ 2 +
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 1 1)) ^ 2) =
    ∫ x in physicalPlaneDomain U,
      (fderiv ℝ u x (EuclideanSpace.single 0 1)) ^ 2 +
      (fderiv ℝ u x (EuclideanSpace.single 1 1)) ^ 2 := by
  let w := u ∘ euclideanPlaneCoordinates.symm
  let t : ℂ → ℝ := (sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)
  have hdom : euclideanPlaneCoordinates ⁻¹' realChartDomain U = physicalPlaneDomain U := by
    ext x
    rfl
  have hD := isOpen_realChartDomain hU
  have hw : ContDiffOn ℝ (⊤ : ℕ∞) w (realChartDomain U) :=
    hu.comp euclideanPlaneCoordinates.symm.contDiff.contDiffOn (fun x hx => by
      change ((Complex.equivRealProdCLM.symm (euclideanPlaneCoordinates
        (euclideanPlaneCoordinates.symm x)) : ℂ) : Sphere) ∈ U
      change ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ U at hx
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hx)
  have hg : MemLp (planarGradient w) 2 (volume.restrict (realChartDomain U)) :=
    real_chart_gradient_memLp hD hu hgrad
  have ht := transported_real_energy heq hU hV hinf hfix w hw
    (fun p hp => (hf p hp).isMetricConformalAt_spherical)
    (fun x _ => Matrix.PosDef.one.smul (sphericalMetricFactor_pos x))
    (integrable_gradientEnergy_spherical_of_memLp hg)
  have htdef : planeInverseTransport fi u = t ∘ complexPlaneCoordinates := by
    funext x
    simp only [planeInverseTransport, t, w, comp_apply, sphereRealMap, sphereRealFunction,
      complexPlaneCoordinates, ContinuousLinearEquiv.trans_apply]
  have hs : ContDiffOn ℝ 1 (planeInverseTransport fi u) (physicalPlaneDomain V) := by
    rw [htdef]
    exact ht.1.comp complexPlaneCoordinates.contDiff.contDiffOn (fun x hx => hx)
  have hP := isOpen_physicalPlaneDomain hV
  have hd (x : EuclideanPlane) (hx : x ∈ physicalPlaneDomain V) (i : Fin 2) :
      fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single i 1) =
        fderiv ℝ t (complexPlaneCoordinates x) (if i = 0 then 1 else Complex.I) := by
    rw [htdef, fderiv_comp x
      ((ht.1.contDiffAt ((hV.preimage OnePoint.continuous_coe).mem_nhds hx)).differentiableAt
        (by norm_num)) complexPlaneCoordinates.differentiableAt, complexPlaneCoordinates.fderiv]
    change fderiv ℝ t (complexPlaneCoordinates x)
      (complexPlaneCoordinates (EuclideanSpace.single i 1)) = _
    have haxis : complexPlaneCoordinates (EuclideanSpace.single i 1) =
        (if i = 0 then 1 else Complex.I) := by
      fin_cases i
      · exact complexPlaneCoordinates_zero
      · exact complexPlaneCoordinates_one
    rw [haxis]
  have he (x : EuclideanPlane) (hx : x ∈ physicalPlaneDomain V) :
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 0 1)) ^ 2 +
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 1 1)) ^ 2 =
        euclideanGradientEnergy t (complexPlaneCoordinates x) := by
    rw [hd x hx 0, hd x hx 1]
    rfl
  have hmp := complexPlaneCoordinates_measurePreserving.restrict_preimage
    (hV.preimage OnePoint.continuous_coe).measurableSet
  have hi := (hmp.integrable_comp ht.2.1.aestronglyMeasurable).mpr ht.2.1
  have hie : IntegrableOn (fun x =>
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 0 1)) ^ 2 +
      (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 1 1)) ^ 2)
      (physicalPlaneDomain V) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem hP.measurableSet] with x hx
    exact (he x hx).symm
  have hparts (i : Fin 2) : MemLp (fun x =>
      fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain V)) := by
    have hm : AEStronglyMeasurable (fun x => fderiv ℝ (planeInverseTransport fi u) x
        (EuclideanSpace.single i 1)) (volume.restrict (physicalPlaneDomain V)) :=
      ((hs.continuousOn_fderiv_of_isOpen hP le_rfl).clm_apply
        continuousOn_const).aestronglyMeasurable hP.measurableSet
    apply (memLp_two_iff_integrable_sq hm).mpr
    apply hie.mono' (hm.pow 2)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    fin_cases i
    · change (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 0 1)) ^ 2 ≤ _
      exact le_add_of_nonneg_right (sq_nonneg _)
    · change (fderiv ℝ (planeInverseTransport fi u) x (EuclideanSpace.single 1 1)) ^ 2 ≤ _
      exact le_add_of_nonneg_left (sq_nonneg _)
  refine ⟨hs, hparts, ?_⟩
  calc
    _ = ∫ x in physicalPlaneDomain V, euclideanGradientEnergy t (complexPlaneCoordinates x) :=
      setIntegral_congr_fun hP.measurableSet he
    _ = ∫ z in ((↑) : ℂ → Sphere) ⁻¹' V, euclideanGradientEnergy t z :=
      hmp.integral_comp complexPlaneCoordinates.toHomeomorph.measurableEmbedding _
    _ = ∫ x in realChartDomain U, gradientEnergy w (fun z => sphericalMetricFactor z • 1) x := ht.2.2
    _ = _ := by
      have hn₀ : eLpNorm (fun p => fderiv ℝ w p (1, 0)) 2
          (volume.restrict (realChartDomain U)) =
          eLpNorm (fun x => fderiv ℝ u x (EuclideanSpace.single 0 1)) 2
            (volume.restrict (physicalPlaneDomain U)) := by
        simpa only [↓reduceIte, hdom] using real_chart_partial_eLpNorm hD hu 0 (hgrad 0)
      have hn₁ : eLpNorm (fun p => fderiv ℝ w p (0, 1)) 2
          (volume.restrict (realChartDomain U)) =
          eLpNorm (fun x => fderiv ℝ u x (EuclideanSpace.single 1 1)) 2
            (volume.restrict (physicalPlaneDomain U)) := by
        simpa only [ite_eq_right (show (1 : Fin 2) ≠ 0 by decide), hdom] using real_chart_partial_eLpNorm hD hu 1 (hgrad 1)
      rw [spherical_gradient_energy_eq_norms hg, hn₀, hn₁,
        ← integral_sq_eq_eLpNorm_toReal_sq (hgrad 0),
        ← integral_sq_eq_eLpNorm_toReal_sq (hgrad 1),
        integral_add (hgrad 0).integrable_sq (hgrad 1).integrable_sq]

end CircleDomainRigidity

end

end OAI
