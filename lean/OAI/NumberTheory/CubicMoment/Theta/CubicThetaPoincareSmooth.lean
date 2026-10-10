import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPoincareSections
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMobiusSmooth

namespace OAI

/-! Smoothness of periodized compact seeds is proved locally by replacing
its locally finite arithmetic sum with an actual finite sum. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicTheta_locallyFinite_finsum {X ι A : Type*} [TopologicalSpace X]
    [AddCommMonoid A] (f : ι → X → A)
    (hf : LocallyFinite (fun i => Function.support (f i))) (x : X) :
    ∃ s : Finset ι, (fun y => ∑ᶠ i, f i y) =ᶠ[𝓝 x] fun y => ∑ i∈s, f i y := by
  classical
  obtain ⟨t,ht,hfin⟩ := hf x
  refine ⟨hfin.toFinset,?_⟩
  filter_upwards [ht] with y hy
  apply finsum_eq_sum_of_support_subset
  intro i hi
  exact hfin.mem_toFinset.mpr ⟨y,hi,hy⟩

lemma cubicThetaPointInclusion_action (g : cubicThetaPrincipalGroup)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaPointInclusion.symm (cubicThetaMobius (cubicThetaPrincipalComplex g) y)=
      g • cubicThetaPointInclusion.symm y := by
  have hy' : y∈cubicThetaPointInclusion.target := by
    rwa [cubicThetaPointInclusion_target]
  have hgy : cubicThetaMobius (cubicThetaPrincipalComplex g) y∈cubicThetaPointInclusion.target := by
    rw [cubicThetaPointInclusion_target]
    exact cubicThetaMobius_height_pos _ hy
  have h₁ := cubicThetaPointInclusion.right_inv hy'
  have h₂ := cubicThetaPointInclusion.right_inv hgy
  change (cubicThetaPointInclusion.symm y).val=y at h₁
  change (cubicThetaPointInclusion.symm (cubicThetaMobius (cubicThetaPrincipalComplex g) y)).val=_ at h₂
  apply Subtype.ext
  change (cubicThetaPointInclusion.symm (cubicThetaMobius (cubicThetaPrincipalComplex g) y)).val=
    cubicThetaMobius (cubicThetaPrincipalComplex g) (cubicThetaPointInclusion.symm y).val
  simpa only [h₁] using h₂

lemma cubicThetaPoincareTerm_contDiffAt (ψ : C_c(CubicThetaPoint,ℂ))
    (hψ : ContDiffOn ℝ ∞ (fun y => ψ (cubicThetaPointInclusion.symm y))
      {y : ℂ × ℝ | 0<y.2}) (g : cubicThetaPrincipalGroup)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    ContDiffAt ℝ ∞ (fun x => cubicThetaPoincareTerm ψ g (cubicThetaPointInclusion.symm x)) y := by
  have hopen : IsOpen {x : ℂ × ℝ | 0<x.2} := isOpen_lt continuous_const continuous_snd
  have hs := hψ.contDiffAt (hopen.mem_nhds (cubicThetaMobius_height_pos
    (cubicThetaPrincipalComplex g) hy))
  have hcomp := hs.comp y (cubicThetaMobius_contDiffAt (cubicThetaPrincipalComplex g) hy)
  have hc : ContDiffAt ℝ ∞ (fun _ : ℂ × ℝ => star (cubicThetaKubotaValue g)) y := contDiffAt_const
  apply (hc.mul hcomp).congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hy] with x hx
  simp only [cubicThetaPoincareTerm,Function.comp_def,cubicThetaPointInclusion_action g hx]

lemma cubicThetaPoincareSection_contDiffOn (ψ : C_c(CubicThetaPoint,ℂ))
    (hψ : ContDiffOn ℝ ∞ (fun y => ψ (cubicThetaPointInclusion.symm y))
      {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ ∞
      (fun y => (cubicThetaPoincareSection ψ).val (cubicThetaPointInclusion.symm y))
      {y : ℂ × ℝ | 0<y.2} := by
  intro y hy
  have hy' : y∈cubicThetaPointInclusion.target := by rwa [cubicThetaPointInclusion_target]
  obtain ⟨s,hs⟩ := cubicTheta_locallyFinite_finsum _ (cubicThetaPoincareTerm_locallyFinite ψ)
    (cubicThetaPointInclusion.symm y)
  have he := hs.comp_tendsto (cubicThetaPointInclusion.symm.continuousAt hy')
  have hd : ContDiffAt ℝ ∞
      (fun x => ∑ g∈s, cubicThetaPoincareTerm ψ g (cubicThetaPointInclusion.symm x)) y :=
    ContDiffAt.sum (fun g _ => cubicThetaPoincareTerm_contDiffAt ψ hψ g hy)
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

end CubicFirstMoment

end

end OAI
