import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateSection

namespace OAI

/-! Exact support and differential identities on an injective
covering sheet for periodized coordinate functions. -/
noncomputable section
open Set Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPoincareSection_norm_support (ψ : C_c(CubicThetaPoint,ℂ)) :
    tsupport (cubicThetaSectionNorm (cubicThetaPoincareSection ψ))⊆
      cubicThetaQuotientMap '' tsupport ψ := by
  have hc := ψ.hasCompactSupport.image cubicThetaQuotientMap_open.continuous
  apply closure_minimal _ hc.isClosed
  intro q hq
  let p := cubicThetaQuotientLift q
  have hn : (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p)≠0 := by
    intro hz
    apply hq
    change ‖∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p‖=0
    simp [hz]
  have hex : ∃ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p≠0 := by
    by_contra! hn'
    exact hn (by simp [hn'])
  obtain ⟨g,hg⟩ := hex
  refine ⟨g • p,?_,?_⟩
  · apply subset_tsupport ψ
    intro hz
    exact hg (by simp [cubicThetaPoincareTerm,hz])
  · exact (cubicThetaQuotient_covering.map_smul g).trans (cubicThetaQuotientLift_map q)

lemma cubicThetaCoordinateSeed_support (g : ℂ × ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2}) :
    tsupport (cubicThetaCoordinateSeed g hg hc hp)⊆
      cubicThetaPointInclusion.symm '' tsupport g := by
  have hi : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  have hcompact := hc.image_of_continuousOn (hi.mono hp)
  apply closure_minimal _ hcompact.isClosed
  intro p hps
  refine ⟨p.val,subset_tsupport g hps,?_⟩
  exact cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)

lemma cubicThetaCoordinateSection_fderiv_on_sheet (g : ℂ × ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2})
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hs : Function.support (cubicThetaCoordinateSeed g hg hc hp)⊆e.source)
    {y : ℂ × ℝ} (hy : 0<y.2) (hye : cubicThetaPointInclusion.symm y∈e.source) :
    fderiv ℝ (cubicThetaSectionFunction
      (cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg hc hp))) y=fderiv ℝ g y := by
  have ht : y∈cubicThetaPointInclusion.target := by rwa [cubicThetaPointInclusion_target]
  have hi := cubicThetaPointInclusion.symm.continuousAt ht
  have heq : cubicThetaSectionFunction
      (cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg hc hp))=ᶠ[𝓝 y] g := by
    filter_upwards [hi.preimage_mem_nhds (e.open_source.mem_nhds hye),
      (isOpen_lt continuous_const continuous_snd).mem_nhds hy] with z hz hz0
    change (cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg hc hp)).val
      (cubicThetaPointInclusion.symm z)=g z
    rw [cubicThetaPoincareSection_on_sheet _ e he hs hz]
    exact cubicThetaCoordinateSeed_coordinates g hg hc hp hz0
  exact heq.fderiv_eq

end CubicFirstMoment

end

end OAI
