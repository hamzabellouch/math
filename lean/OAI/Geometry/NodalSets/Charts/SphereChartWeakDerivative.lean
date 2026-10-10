import OAI.Geometry.NodalSets.Charts.SphereChartDerivativeMap
import OAI.Geometry.NodalSets.Charts.SphereCompactChartTesting
import OAI.Geometry.NodalSets.Elliptic.RealCompactMultiplierLemmas
import OAI.Geometry.NodalSets.Elliptic.RealCompactTestDerivative

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section
local instance sphereChartWeakDerivativeMeasurable : MeasurableSpace Base := borel Base
local instance sphereChartWeakDerivativeBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_chart_weak_derivative (d : SphereEnergyData) (p : Base) (i : Fin 4)
    (z : SphereEnergyHilbert d) (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ realFinCube 4) :
    IntegrableOn (fun x ↦ (sphereChartDerivativeMap d p i z) x*phi x) (realFinCube 4) ∧
    IntegrableOn (fun x ↦ (sphereEnergyL2Map d z) (sphereChartCoordMap p x)*Yau.coordPartial phi x i)
      (realFinCube 4) ∧
    (∫ x in realFinCube 4, (sphereChartDerivativeMap d p i z) x*phi x) =
      -(∫ x in realFinCube 4, (sphereEnergyL2Map d z) (sphereChartCoordMap p x)*Yau.coordPartial phi x i) := by
  have hd : ContDiff ℝ ∞ (fun x ↦ Yau.coordPartial phi x i) := Yau.real_coordPartial_smooth phi hp i
  have hdc : HasCompactSupport (fun x ↦ Yau.coordPartial phi x i) := hc.fderiv_apply ℝ (Pi.single i 1)
  obtain ⟨h,hh,ht⟩ := sphere_compact_chart_testing d p _ hd hdc
  let H := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) h hh
  let hP := Yau.real_continuous_memLp_compact (realFinCube_isCompact 4) phi hp.continuous
  let P := hP.toLp phi
  have hz (w : SphereEnergyHilbert d) (x : Yau.Jets.Coord) (hx : x ∉ realFinCube 4) :
      (sphereEnergyL2Map d w) (sphereChartCoordMap p x)*Yau.coordPartial phi x i = 0 := by
    unfold Yau.coordPartial
    rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hx (hs h))]
    simp
  have hright (w : SphereEnergyHilbert d) : inner ℝ (sphereEnergyL2Map d w) H =
      ∫ x in realFinCube 4, (sphereEnergyL2Map d w) (sphereChartCoordMap p x)*Yau.coordPartial phi x i := by
    rw [(ht (sphereEnergyL2Map d w)).2]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hz w)).symm
  have hid (w : SphereEnergyHilbert d) : inner ℝ (sphereChartDerivativeMap d p i w) P =
      -inner ℝ (sphereEnergyL2Map d w) H := by
    apply (sphereEnergyToCompletion_dense d).induction_on
      (p := fun w ↦ inner ℝ (sphereChartDerivativeMap d p i w) P = -inner ℝ (sphereEnergyL2Map d w) H) w
    · exact isClosed_eq ((sphereChartDerivativeMap d p i).continuous.inner continuous_const)
        (((sphereEnergyL2Map d).continuous.inner continuous_const).neg)
    · intro u
      rw [hright,sphereEnergyL2Map_coe,sphereChartDerivativeMap_coe]
      change inner ℝ ((sphereSmoothChartPartial_memLp d p i u).toLp (sphereSmoothChartPartial d p i u))
        (hP.toLp phi) = _
      rw [Yau.real_toLp_inner]
      have hae : ∀ᵐ x, (sphereEnergyL2Linear d u) (sphereChartCoordMap p x) =
          (SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p x) := by
        apply (sphereWeightedMeasure_ae_chart_iff d p (fun y ↦ (sphereEnergyL2Linear d u) y =
          (SphereEnergySmooth.toSmooth d u : Base → ℝ) y)).mp
        exact (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
          (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous).coeFn_toLp
      have he : (∫ x in realFinCube 4, (sphereEnergyL2Linear d u) (sphereChartCoordMap p x)*Yau.coordPartial phi x i) =
          ∫ x in realFinCube 4, (SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p x)*Yau.coordPartial phi x i := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hae] with x hx
        rw [hx]
      rw [he]
      exact (Yau.real_compact_test_derivative _ phi
        (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p) hp hc i (realFinCube 4) hs).2.2
  obtain ⟨hLi,hLe⟩ := Yau.real_L2_test_pairing (sphereChartDerivativeMap d p i z) phi hP
  refine ⟨hLi,(ht (sphereEnergyL2Map d z)).1.integrableOn,?_⟩
  rw [← hLe,← hright]
  exact hid z

end
end Yau.Target

end OAI
