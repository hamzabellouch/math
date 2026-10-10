import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFundamentalDomain

namespace OAI

/-! A measurable injective quotient chart can be included in a genuine
fundamental domain. This supplies the local quotient-volume formula. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaFundamentalDomain_injOn :
    InjOn cubicThetaQuotientMap cubicThetaFundamentalDomain := by
  intro p hp q hq he
  exact hp.symm.trans ((congrArg cubicThetaBorelSection he).trans hq)

def cubicThetaFundamentalExtension (S : Set CubicThetaPoint) : Set CubicThetaPoint :=
  S ∪ (cubicThetaFundamentalDomain \ cubicThetaQuotientMap ⁻¹' (cubicThetaQuotientMap '' S))

lemma cubicThetaFundamentalExtension_measurable {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hQ : MeasurableSet (cubicThetaQuotientMap '' S)) :
    MeasurableSet (cubicThetaFundamentalExtension S) :=
  hS.union (cubicThetaFundamentalDomain_measurable.diff
    (hQ.preimage cubicThetaQuotientMap_open.continuous.measurable))

lemma cubicThetaFundamentalExtension_injOn {S : Set CubicThetaPoint}
    (hS : InjOn cubicThetaQuotientMap S) :
    InjOn cubicThetaQuotientMap (cubicThetaFundamentalExtension S) := by
  intro p hp q hq he
  rcases hp with hp | hp
  · rcases hq with hq | hq
    · exact hS hp hq he
    · exact False.elim (hq.2 ⟨p,hp,he⟩)
  · rcases hq with hq | hq
    · exact False.elim (hp.2 ⟨q,hq,he.symm⟩)
    · exact cubicThetaFundamentalDomain_injOn hp.1 hq.1 he

lemma cubicThetaFundamentalExtension_covers (S : Set CubicThetaPoint) (p : CubicThetaPoint) :
    ∃ g : cubicThetaPrincipalGroup, g • p∈cubicThetaFundamentalExtension S := by
  by_cases hp : cubicThetaQuotientMap p∈cubicThetaQuotientMap '' S
  · obtain ⟨q,hq,he⟩ := hp
    obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
    refine ⟨g,Or.inl ?_⟩
    change g • p=q at hg
    rwa [hg]
  · obtain ⟨g,hg,_⟩ := cubicThetaFundamentalDomain_unique p
    refine ⟨g,Or.inr ⟨hg,?_⟩⟩
    simpa only [mem_preimage,cubicThetaQuotient_covering.map_smul] using hp

lemma cubicThetaFundamentalExtension_isFundamentalDomain {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hQ : MeasurableSet (cubicThetaQuotientMap '' S))
    (hi : InjOn cubicThetaQuotientMap S) (μ : Measure CubicThetaPoint) :
    IsFundamentalDomain cubicThetaPrincipalGroup (cubicThetaFundamentalExtension S) μ := by
  apply IsFundamentalDomain.mk' (cubicThetaFundamentalExtension_measurable hS hQ).nullMeasurableSet
  intro p
  obtain ⟨g,hg⟩ := cubicThetaFundamentalExtension_covers S p
  refine ⟨g,hg,fun h hh => ?_⟩
  have he : cubicThetaQuotientMap (h • p)=cubicThetaQuotientMap (g • p) := by
    rw [cubicThetaQuotient_covering.map_smul,cubicThetaQuotient_covering.map_smul]
  have hp := cubicThetaFundamentalExtension_injOn hi hh hg he
  have hf : (g⁻¹*h) • p=p := by rw [mul_smul,hp,inv_smul_smul]
  exact (inv_mul_eq_one.mp (cubicThetaPrincipal_fixed_eq_one _ _ hf)).symm

lemma cubicThetaFundamentalExtension_inter (S : Set CubicThetaPoint) :
    cubicThetaQuotientMap ⁻¹' (cubicThetaQuotientMap '' S) ∩ cubicThetaFundamentalExtension S=S := by
  ext p
  constructor
  · rintro ⟨hp,hS | hD⟩
    · exact hS
    · exact False.elim (hD.2 hp)
  · intro hp
    exact ⟨⟨p,hp,rfl⟩,Or.inl hp⟩

end CubicFirstMoment

end

end OAI
