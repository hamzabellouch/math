import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFreeAction

namespace OAI

/-! Two local lifts of the actual arithmetic quotient differ by one fixed
deck transformation near any point. This is the local transition law for
both the geometric charts and the cubic multiplier. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaLocalLifts_eq {X : Type*} [TopologicalSpace X] {x : X}
    {F G : X → CubicThetaPoint} (hF : ContinuousAt F x) (hG : ContinuousAt G x)
    (hx : F x=G x)
    (h : ∀ᶠ y in 𝓝 x, cubicThetaQuotientMap (F y)=cubicThetaQuotientMap (G y)) :
    F =ᶠ[𝓝 x] G := by
  obtain ⟨U,hU,hxU,hUi⟩ := cubicThetaQuotient_localHomeomorph.isLocallyInjective (F x)
  have hFU : ∀ᶠ y in 𝓝 x, F y∈U := hF.preimage_mem_nhds (hU.mem_nhds hxU)
  have hGU : ∀ᶠ y in 𝓝 x, G y∈U := hG.preimage_mem_nhds (hU.mem_nhds (hx ▸ hxU))
  filter_upwards [hFU,hGU,h] with y hyF hyG hy
  exact hUi hyF hyG hy

lemma cubicThetaLocalLifts_deck {X : Type*} [TopologicalSpace X] {x : X}
    {F G : X → CubicThetaPoint} (hF : ContinuousAt F x) (hG : ContinuousAt G x)
    (h : ∀ᶠ y in 𝓝 x, cubicThetaQuotientMap (F y)=cubicThetaQuotientMap (G y)) :
    ∃ g : cubicThetaPrincipalGroup, F =ᶠ[𝓝 x] fun y => g • G y := by
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp h.self_of_nhds
  refine ⟨g,cubicThetaLocalLifts_eq hF ((continuous_const_smul g).continuousAt.comp hG) hg.symm ?_⟩
  filter_upwards [h] with y hy
  exact hy.trans (cubicThetaQuotient_covering.map_smul g).symm

lemma cubicThetaLocalLifts_deck_unique {X : Type*} [TopologicalSpace X] {x : X}
    {F G : X → CubicThetaPoint} {g h : cubicThetaPrincipalGroup}
    (hg : F =ᶠ[𝓝 x] fun y => g • G y) (hh : F =ᶠ[𝓝 x] fun y => h • G y) : g=h :=
  IsCancelSMul.right_cancel g h (G x) (hg.self_of_nhds.symm.trans hh.self_of_nhds)

end CubicFirstMoment

end

end OAI
