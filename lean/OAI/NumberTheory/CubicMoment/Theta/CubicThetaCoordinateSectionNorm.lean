import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1ChartNorm
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateSectionSupport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCutoffEnergy

namespace OAI

/-! The norm of a periodized C1 coordinate function is exactly its
local hyperbolic energy integral when its support lies in one chart. -/
noncomputable section
open Set MeasureTheory
open scoped Pointwise
namespace CubicFirstMoment

lemma cubicThetaCoordinateSection_norm_sq {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hpos : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) :
    let hp := hgs.trans hpos
    let F := cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc hp)
    ‖cubicThetaC1EnergyData F (cubicThetaCoordinateSection_regular hg hc hp)
      (cubicThetaPoincareSection_compact _)‖^2=
      ∫ y in K, (‖g y‖^2+y.2^2*cubicThetaFunctionEnergy g y)/y.2^3 := by
  intro hp F
  let S := cubicThetaPointInclusion.symm '' K
  have hi : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  have hS : IsCompact S := hK.image_of_continuousOn (hi.mono hpos)
  have hss : tsupport (cubicThetaCoordinateSeed g hg.continuous hc hp)⊆S :=
    (cubicThetaCoordinateSeed_support g hg.continuous hc hp).trans (image_mono hgs)
  have hnorm : tsupport (cubicThetaSectionNorm F)⊆cubicThetaQuotientMap '' S :=
    (cubicThetaPoincareSection_norm_support _).trans (image_mono hss)
  have hcoord : cubicThetaPointCoordinates '' S=K := by
    ext y
    constructor
    · rintro ⟨p,⟨z,hz,rfl⟩,rfl⟩
      have heq := cubicThetaPointInclusion.right_inv
        (show z∈cubicThetaPointInclusion.target by rw [cubicThetaPointInclusion_target]; exact hpos hz)
      change cubicThetaPointCoordinates (cubicThetaPointInclusion.symm z)∈K
      change cubicThetaPointCoordinates (cubicThetaPointInclusion.symm z)=z at heq
      rw [heq]
      exact hz
    · intro hy
      exact ⟨cubicThetaPointInclusion.symm y,⟨y,hy,rfl⟩,
        cubicThetaPointInclusion.right_inv (by rw [cubicThetaPointInclusion_target]; exact hpos hy)⟩
  rw [cubicThetaC1EnergyData_chart_norm F (cubicThetaCoordinateSection_regular hg hc hp)
    (cubicThetaPoincareSection_compact _) e he hS.measurableSet hKe hnorm]
  have hsupp : Function.support (cubicThetaCoordinateSeed g hg.continuous hc hp)⊆e.source :=
    subset_tsupport _ |>.trans (hss.trans hKe)
  have hpt (p : CubicThetaPoint) (hpS : p∈S) :
      ‖F.val p‖^2+cubicThetaSectionEnergy F p=
        ‖g (cubicThetaPointCoordinates p)‖^2+(cubicThetaPointCoordinates p).2^2*
          cubicThetaFunctionEnergy g (cubicThetaPointCoordinates p) := by
    have hp' : cubicThetaPointInclusion.symm p.val=p :=
      cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
    have hv : F.val p=g p.val := cubicThetaPoincareSection_on_sheet _ e he hsupp (hKe hpS)
    have hd := cubicThetaCoordinateSection_fderiv_on_sheet g hg.continuous hc hp e he hsupp
      p.property (by rw [hp']; exact hKe hpS)
    change fderiv ℝ (cubicThetaSectionFunction F) p.val=fderiv ℝ g p.val at hd
    rw [hv]
    unfold cubicThetaSectionEnergy cubicThetaSectionDifferential cubicThetaFunctionEnergy
    rw [hd]
    rfl
  rw [setIntegral_congr_fun hS.measurableSet hpt]
  simpa only [hcoord] using cubicThetaPointIntegral_density hS.measurableSet
    (fun y => ‖g y‖^2+y.2^2*cubicThetaFunctionEnergy g y)

end CubicFirstMoment

end

end OAI
