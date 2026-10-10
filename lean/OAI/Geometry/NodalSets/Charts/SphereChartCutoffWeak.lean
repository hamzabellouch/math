import OAI.Geometry.NodalSets.Charts.SphereChartWeakDerivative
import OAI.Geometry.NodalSets.Elliptic.RealCompactL2Product
import OAI.Geometry.NodalSets.Elliptic.RealDifferenceQuotientTest

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section
local instance sphereChartCutoffWeakMeasurable : MeasurableSpace Base := borel Base
local instance sphereChartCutoffWeakBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_chart_cutoff_weak (d : SphereEnergyData) (p : Base) (z : SphereEnergyHilbert d)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) :
    let v := fun x ↦ eta x*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
    let G := fun i x ↦ eta x*(sphereChartDerivativeMap d p i z) x +
      Yau.coordPartial eta x i*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
    MemLp v 2 volume ∧ ∀ i : Fin 4, MemLp (G i) 2 volume ∧
      ∀ phi : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
        Integrable (fun x ↦ v x*Yau.coordPartial phi x i) ∧ Integrable (fun x ↦ G i x*phi x) ∧
        (∫ x, v x*Yau.coordPartial phi x i) = -(∫ x, G i x*phi x) := by
  dsimp only
  let w := fun x ↦ (sphereEnergyL2Map d z) (sphereChartCoordMap p x)
  have hw : MemLp w 2 (volume.restrict (realFinCube 4)) := by
    obtain ⟨_,_,hb⟩ := sphereWeightedL2_compact_chart_bound d p (realFinCube_isCompact 4)
    exact (hb (sphereEnergyL2Map d z)).1
  have hval := Yau.real_compact_localL2_product (realFinCube_isCompact 4) eta w he.continuous hs hw
  refine ⟨hval,?_⟩
  intro i
  have hpart : tsupport (fun x ↦ Yau.coordPartial eta x i) ⊆ realFinCube 4 :=
    (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs
  have h1 := Yau.real_compact_localL2_product (realFinCube_isCompact 4) eta
    (sphereChartDerivativeMap d p i z) he.continuous hs (Lp.memLp _)
  have h2 := Yau.real_compact_localL2_product (realFinCube_isCompact 4)
    (fun x ↦ Yau.coordPartial eta x i) w (Yau.real_coordPartial_smooth eta he i).continuous hpart hw
  refine ⟨h1.add h2,?_⟩
  intro phi hp hc
  have hphi := Yau.real_compact_continuous_memLp phi hp.continuous hc
  have hi1 : Integrable (fun x ↦ eta x*(sphereChartDerivativeMap d p i z) x*phi x) := h1.integrable_mul hphi
  have hi2 : Integrable (fun x ↦ Yau.coordPartial eta x i*w x*phi x) := h2.integrable_mul hphi
  have hi3 : Integrable (fun x ↦ eta x*w x*Yau.coordPartial phi x i) := hval.integrable_mul
    (Yau.real_compact_continuous_memLp _ (Yau.real_coordPartial_smooth phi hp i).continuous
      (hc.fderiv_apply ℝ (Pi.single i 1)))
  have hweak := (sphere_chart_weak_derivative d p i z (fun x ↦ eta x*phi x) (he.mul hp)
    hc.mul_left (tsupport_mul_subset_left.trans hs)).2.2
  have he1 : (fun x ↦ (sphereChartDerivativeMap d p i z) x*(eta x*phi x)) =
      fun x ↦ eta x*(sphereChartDerivativeMap d p i z) x*phi x := by funext x; ring
  have he2 : (fun x ↦ w x*Yau.coordPartial (fun y ↦ eta y*phi y) x i) =
      fun x ↦ Yau.coordPartial eta x i*w x*phi x+eta x*w x*Yau.coordPartial phi x i := by
    funext x
    rw [Yau.real_coordPartial_mul eta phi he hp]
    ring
  change (∫ x in realFinCube 4, (sphereChartDerivativeMap d p i z) x*(eta x*phi x)) =
    -(∫ x in realFinCube 4, w x*Yau.coordPartial (fun y ↦ eta y*phi y) x i) at hweak
  rw [he1,he2,integral_add hi2.integrableOn hi3.integrableOn] at hweak
  have hz (x : Yau.Jets.Coord) (hx : x ∉ realFinCube 4) : eta x=0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))
  have hdz (x : Yau.Jets.Coord) (hx : x ∉ realFinCube 4) : Yau.coordPartial eta x i=0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y ↦ Yau.coordPartial eta y i) (fun h ↦ hx (hpart h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hz x hx,zero_mul,zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hdz x hx,zero_mul,zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hz x hx,zero_mul,zero_mul])] at hweak
  have heG : (fun x ↦ (eta x*(sphereChartDerivativeMap d p i z) x+Yau.coordPartial eta x i*w x)*phi x) =
      fun x ↦ eta x*(sphereChartDerivativeMap d p i z) x*phi x+Yau.coordPartial eta x i*w x*phi x := by
    funext x
    ring
  refine ⟨hi3,by rw [heG]; exact hi1.add hi2,?_⟩
  change (∫ x, eta x*w x*Yau.coordPartial phi x i) = _
  rw [heG,integral_add hi1 hi2]
  linarith only [hweak]

end
end Yau.Target

end OAI
