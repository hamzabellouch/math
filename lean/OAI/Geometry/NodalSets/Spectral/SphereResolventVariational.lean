import OAI.Geometry.NodalSets.Charts.SphereChartTestFlux
import OAI.Geometry.NodalSets.Charts.SphereChartWeakDivergence
import OAI.Geometry.NodalSets.Spectral.SphereResolventDistribution

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section
local instance sphereResolventVariationalMeasurable : MeasurableSpace Base := borel Base
local instance sphereResolventVariationalBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereWeightedL2_compact_test_integrable (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) :
    Integrable (fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)*
      f (sphereChartCoordMap p x)*phi x) := by
  obtain ⟨v,hv,_,hval⟩ := sphere_chart_scalar_extension p phi hp hc
  have h := (sphereWeightedL2_test_chart d f v hv.continuous p).1
  simpa only [hval] using h

theorem sphere_resolvent_chart_variational (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ realFinCube 4) :
    let z := sphereWeakSolution d f
    let w := sphereEnergyL2Map d z
    let F := fun x ↦ roundCoordDensity x * ∑ i, (sphereChartDerivativeMap d p i z) x *
      (∑ j, intrinsicRealPrincipal d.tensor p x i j*Yau.coordPartial phi x j)
    let M := fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)*
      w (sphereChartCoordMap p x)*phi x
    let R := fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)*
      f (sphereChartCoordMap p x)*phi x
    IntegrableOn F (realFinCube 4) ∧ IntegrableOn M (realFinCube 4) ∧
      IntegrableOn R (realFinCube 4) ∧
      (∫ x in realFinCube 4, F x)+(∫ x in realFinCube 4, M x) = ∫ x in realFinCube 4, R x := by
  dsimp only
  let z := sphereWeakSolution d f
  let w := sphereEnergyL2Map d z
  let V := sphereChartTestFlux d p phi
  let M := fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)*w (sphereChartCoordMap p x)*phi x
  let R := fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)*f (sphereChartCoordMap p x)*phi x
  let D := fun x ↦ w (sphereChartCoordMap p x)*Yau.coordDiv V x
  obtain ⟨hF,hD,hweak⟩ := sphere_chart_weak_divergence d p z V
    (sphereChartTestFlux_smooth d p phi hp) (sphereChartTestFlux_compact d p phi hc)
    (fun i ↦ (sphereChartTestFlux_tsupport d p phi i).trans hs)
  have hM := sphereWeightedL2_compact_test_integrable d w p phi hp hc
  have hR := sphereWeightedL2_compact_test_integrable d f p phi hp hc
  have heF : (fun x ↦ ∑ i, (sphereChartDerivativeMap d p i z) x*V x i) =
      (fun x ↦ roundCoordDensity x * ∑ i, (sphereChartDerivativeMap d p i z) x *
        (∑ j, intrinsicRealPrincipal d.tensor p x i j*Yau.coordPartial phi x j)) := by
    funext x
    simp only [V,sphereChartTestFlux,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf
  rw [heF] at hF hweak
  have hdist := (sphere_resolvent_chart_distribution d f p phi hp hc).2.2
  have heDist : (fun x ↦ roundCoordDensity x*(sphereL2Resolvent d f) (sphereChartCoordMap p x)*
      (d.density (sphereChartCoordMap p x)*phi x - Yau.weightedDiv roundCoordDensity
        (fun y i ↦ ∑ j, intrinsicRealPrincipal d.tensor p y i j*Yau.coordPartial phi y j) x)) =
      fun x ↦ M x-D x := by
    funext x
    dsimp only [M,D,V]
    rw [sphereChartTestFlux_div]
    change roundCoordDensity x*w (sphereChartCoordMap p x)*_ = _
    ring
  rw [heDist] at hdist
  have hzM (x : Yau.Jets.Coord) (hx : x ∉ realFinCube 4) : M x=0 := by
    dsimp only [M]
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)),mul_zero]
  have hzR (x : Yau.Jets.Coord) (hx : x ∉ realFinCube 4) : R x=0 := by
    dsimp only [R]
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)),mul_zero]
  have hzD (x : Yau.Jets.Coord) (hx : x ∉ realFinCube 4) : D x=0 := by
    dsimp only [D,V]
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs (sphereChartTestFlux_div_tsupport d p phi h))),mul_zero]
  have hMD : (∫ x in realFinCube 4, M x-D x) = ∫ x, M x-D x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hzM x hx,hzD x hx,sub_self])
  have hReq : (∫ x in realFinCube 4, R x) = ∫ x, R x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzR
  change (∫ x, M x-D x) = ∫ x, R x at hdist
  rw [← hMD,← hReq,integral_sub hM.integrableOn hD] at hdist
  refine ⟨hF,hM.integrableOn,hR.integrableOn,?_⟩
  change _+(∫ x in realFinCube 4, M x) = ∫ x in realFinCube 4, R x
  linarith only [hweak,hdist]

end
end Yau.Target

end OAI
