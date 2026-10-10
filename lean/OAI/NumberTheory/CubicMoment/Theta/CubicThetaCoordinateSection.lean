import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1L2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothingSupport

namespace OAI

/-! Compact coordinate functions give actual automorphic sections.
Their C1 regularity follows from the locally finite arithmetic sum. -/
noncomputable section
open Set Filter Topology
open scoped CompactlySupported BigOperators ContDiff
namespace CubicFirstMoment

def cubicThetaCoordinateSeed (g : ℂ × ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2}) :
    C_c(CubicThetaPoint,ℂ) :=
  ⟨⟨fun p => g p.val,hg.comp continuous_subtype_val⟩,cubicThetaPositiveSeed_compact hc hp⟩

lemma cubicThetaCoordinateSeed_coordinates (g : ℂ × ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2})
    {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaCoordinateSeed g hg hc hp (cubicThetaPointInclusion.symm y)=g y := by
  change g (cubicThetaPointInclusion.symm y).val=g y
  exact congrArg g (cubicThetaPointInclusion.right_inv (by rwa [cubicThetaPointInclusion_target]))

lemma cubicThetaPoincareTerm_regular {n : ℕ∞} (ψ : C_c(CubicThetaPoint,ℂ))
    (hψ : ContDiffOn ℝ n (fun y => ψ (cubicThetaPointInclusion.symm y))
      {y : ℂ × ℝ | 0<y.2}) (g : cubicThetaPrincipalGroup)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    ContDiffAt ℝ n (fun x => cubicThetaPoincareTerm ψ g (cubicThetaPointInclusion.symm x)) y := by
  have hopen : IsOpen {x : ℂ × ℝ | 0<x.2} := isOpen_lt continuous_const continuous_snd
  have hs := hψ.contDiffAt (hopen.mem_nhds (cubicThetaMobius_height_pos
    (cubicThetaPrincipalComplex g) hy))
  have hcomp := hs.comp y ((cubicThetaMobius_contDiffAt (cubicThetaPrincipalComplex g) hy).of_le (by simp))
  have hconst : ContDiffAt ℝ n (fun _ : ℂ × ℝ => star (cubicThetaKubotaValue g)) y := contDiffAt_const
  apply (hconst.mul hcomp).congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hy] with x hx
  simp only [cubicThetaPoincareTerm,Function.comp_def,cubicThetaPointInclusion_action g hx]

lemma cubicThetaPoincareSection_regular {n : ℕ∞} (ψ : C_c(CubicThetaPoint,ℂ))
    (hψ : ContDiffOn ℝ n (fun y => ψ (cubicThetaPointInclusion.symm y))
      {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ n (cubicThetaSectionFunction (cubicThetaPoincareSection ψ))
      {y : ℂ × ℝ | 0<y.2} := by
  intro y hy
  have hy' : y∈cubicThetaPointInclusion.target := by rwa [cubicThetaPointInclusion_target]
  obtain ⟨s,hs⟩ := cubicTheta_locallyFinite_finsum _ (cubicThetaPoincareTerm_locallyFinite ψ)
    (cubicThetaPointInclusion.symm y)
  have he := hs.comp_tendsto (cubicThetaPointInclusion.symm.continuousAt hy')
  have hd : ContDiffAt ℝ n
      (fun x => ∑ g∈s, cubicThetaPoincareTerm ψ g (cubicThetaPointInclusion.symm x)) y :=
    ContDiffAt.sum (fun g _ => cubicThetaPoincareTerm_regular ψ hψ g hy)
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

lemma cubicThetaCoordinateSection_regular {n : ℕ∞} {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ n g) (hc : HasCompactSupport g)
    (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ n (cubicThetaSectionFunction
      (cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc hp)))
      {y : ℂ × ℝ | 0<y.2} := by
  apply cubicThetaPoincareSection_regular
  apply hg.contDiffOn.congr
  intro y hy
  exact cubicThetaCoordinateSeed_coordinates g hg.continuous hc hp hy

end CubicFirstMoment

end

end OAI
