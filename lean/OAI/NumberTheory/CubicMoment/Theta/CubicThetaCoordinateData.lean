import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1EnergyLinear
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPoincareLinear
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateSectionNorm

namespace OAI

/-! Actual value-gradient data of periodized coordinate functions.
Smooth coordinate functions already lie in the defining energy graph. -/
noncomputable section
open Set
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

def cubicThetaCoordinateData {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2}) :
    CubicThetaGlobalEnergyAmbient :=
  cubicThetaC1EnergyData (cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc hp))
    (cubicThetaCoordinateSection_regular hg hc hp) (cubicThetaPoincareSection_compact _)

lemma cubicThetaCoordinateData_sub {g h : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (hcg : HasCompactSupport g) (hch : HasCompactSupport h)
    (hpg : tsupport g⊆{y : ℂ × ℝ | 0<y.2})
    (hph : tsupport h⊆{y : ℂ × ℝ | 0<y.2})
    (hpd : tsupport (g-h)⊆{y : ℂ × ℝ | 0<y.2}) :
    cubicThetaCoordinateData (hg.sub hh) (hcg.sub hch) hpd=
      cubicThetaCoordinateData hg hcg hpg-cubicThetaCoordinateData hh hch hph := by
  have hseed : cubicThetaCoordinateSeed (g-h) (hg.sub hh).continuous (hcg.sub hch) hpd=
      cubicThetaCoordinateSeed g hg.continuous hcg hpg-cubicThetaCoordinateSeed h hh.continuous hch hph := by
    ext p
    rfl
  have heq := (congrArg cubicThetaPoincareSection hseed).trans (cubicThetaPoincareSection_sub _ _)
  unfold cubicThetaCoordinateData
  let A := cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hcg hpg)
  let B := cubicThetaPoincareSection (cubicThetaCoordinateSeed h hh.continuous hch hph)
  have hA := cubicThetaCoordinateSection_regular hg hcg hpg
  have hB := cubicThetaCoordinateSection_regular hh hch hph
  have hcA := cubicThetaPoincareSection_compact (cubicThetaCoordinateSeed g hg.continuous hcg hpg)
  have hcB := cubicThetaPoincareSection_compact (cubicThetaCoordinateSeed h hh.continuous hch hph)
  calc
    _ = cubicThetaC1EnergyData (A-B) (hA.sub hB)
        (cubicThetaCompactSection_sub A B hcA hcB) := by
      congr 1
    _ = _ := cubicThetaC1EnergyData_sub A B hA hB hcA hcB

lemma cubicThetaCoordinateData_norm_sq {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hpos : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) :
    ‖cubicThetaCoordinateData hg hc (hgs.trans hpos)‖^2=
      ∫ y in K, (‖g y‖^2+y.2^2*cubicThetaFunctionEnergy g y)/y.2^3 :=
  cubicThetaCoordinateSection_norm_sq hg hc hK hpos hgs e he hKe

lemma cubicThetaCoordinateData_smooth {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2}) :
    cubicThetaCoordinateData (hg.of_le (by simp)) hc hp∈cubicThetaGlobalEnergySpace := by
  let F : cubicThetaSmoothTests :=
    ⟨cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc hp),
      cubicThetaCoordinateSection_regular hg hc hp,cubicThetaPoincareSection_compact _⟩
  exact Submodule.le_topologicalClosure _ ⟨F,rfl⟩

end CubicFirstMoment

end

end OAI
