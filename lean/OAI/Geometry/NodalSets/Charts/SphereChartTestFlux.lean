import OAI.Geometry.NodalSets.Charts.SphereEnergyCompletion
import OAI.Geometry.NodalSets.Elliptic.CompactFluxGreen
import OAI.Geometry.NodalSets.Elliptic.IntrinsicRealCoordinates

namespace OAI

namespace Yau.Target
open Set
open scoped ContDiff
noncomputable section

def sphereChartTestFlux (d : SphereEnergyData) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) (i : Fin 4) : ℝ :=
  roundCoordDensity x * ∑ j, intrinsicRealPrincipal d.tensor p x i j*Yau.coordPartial phi x j

theorem sphereChartTestFlux_smooth (d : SphereEnergyData) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi) (i : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ sphereChartTestFlux d p phi x i) :=
  roundCoordDensity_smooth.mul (ContDiff.sum (fun j _ ↦
    (intrinsicRealPrincipal_smooth d.tensor d.smooth d.symm d.pos p i j).mul
      (Yau.real_coordPartial_smooth phi hp j)))

theorem sphereChartTestFlux_tsupport (d : SphereEnergyData) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (i : Fin 4) :
    tsupport (fun x ↦ sphereChartTestFlux d p phi x i) ⊆ tsupport phi := by
  apply closure_minimal _ (isClosed_tsupport phi)
  intro x hx
  by_contra hn
  have hd : fderiv ℝ phi x = 0 := fderiv_of_notMem_tsupport ℝ hn
  have hz : sphereChartTestFlux d p phi x i = 0 := by
    simp [sphereChartTestFlux,Yau.coordPartial,hd]
  exact hx hz

theorem sphereChartTestFlux_compact (d : SphereEnergyData) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (hc : HasCompactSupport phi) (i : Fin 4) :
    HasCompactSupport (fun x ↦ sphereChartTestFlux d p phi x i) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (sphereChartTestFlux_tsupport d p phi i)

theorem sphereChartTestFlux_div_tsupport (d : SphereEnergyData) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) :
    tsupport (Yau.coordDiv (sphereChartTestFlux d p phi)) ⊆ tsupport phi := by
  apply closure_minimal _ (isClosed_tsupport phi)
  intro x hx
  by_contra hn
  have hd (i : Fin 4) : fderiv ℝ (fun y ↦ sphereChartTestFlux d p phi y i) x = 0 :=
    fderiv_of_notMem_tsupport ℝ (fun h ↦ hn (sphereChartTestFlux_tsupport d p phi i h))
  have hz : Yau.coordDiv (sphereChartTestFlux d p phi) x = 0 := by
    simp [Yau.coordDiv,Yau.coordPartial,hd]
  exact hx hz

theorem sphereChartTestFlux_div (d : SphereEnergyData) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    Yau.coordDiv (sphereChartTestFlux d p phi) x = roundCoordDensity x *
      Yau.weightedDiv roundCoordDensity
        (fun y i ↦ ∑ j, intrinsicRealPrincipal d.tensor p y i j*Yau.coordPartial phi y j) x := by
  simp only [Yau.weightedDiv,← mul_assoc,mul_inv_cancel₀ (roundCoordDensity_pos x).ne',one_mul]
  rfl

end
end Yau.Target

end OAI
