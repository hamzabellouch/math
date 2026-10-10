import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBorelSection
import Mathlib.MeasureTheory.Group.FundamentalDomain

namespace OAI

/-! An actual measurable fundamental domain for the free principal
arithmetic action. It is the fixed-point set of the proved Borel section,
not a postulated domain or a boundary regularity assumption. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaBorelSection : CubicThetaQuotient → CubicThetaPoint :=
  Classical.choose cubicTheta_measurable_section_exists

lemma cubicThetaBorelSection_measurable : Measurable cubicThetaBorelSection :=
  (Classical.choose_spec cubicTheta_measurable_section_exists).1

lemma cubicThetaBorelSection_rightInverse :
    Function.RightInverse cubicThetaBorelSection cubicThetaQuotientMap :=
  (Classical.choose_spec cubicTheta_measurable_section_exists).2

def cubicThetaFundamentalDomain : Set CubicThetaPoint :=
  {p | cubicThetaBorelSection (cubicThetaQuotientMap p)=p}

lemma cubicThetaFundamentalDomain_measurable : MeasurableSet cubicThetaFundamentalDomain :=
  measurableSet_eq_fun
    (cubicThetaBorelSection_measurable.comp cubicThetaQuotientMap_open.continuous.measurable)
    measurable_id

lemma cubicThetaFundamentalDomain_unique (p : CubicThetaPoint) :
    ∃! g : cubicThetaPrincipalGroup, g • p∈cubicThetaFundamentalDomain := by
  have he := cubicThetaBorelSection_rightInverse (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  refine ⟨g,?_,?_⟩
  · change cubicThetaBorelSection (cubicThetaQuotientMap (g • p))=g • p
    rw [cubicThetaQuotient_covering.map_smul]
    exact hg.symm
  · intro h hh
    change cubicThetaBorelSection (cubicThetaQuotientMap (h • p))=h • p at hh
    rw [cubicThetaQuotient_covering.map_smul] at hh
    have hp : h • p=g • p := hh.symm.trans hg.symm
    have hf : (g⁻¹*h) • p=p := by rw [mul_smul,hp,inv_smul_smul]
    exact (inv_mul_eq_one.mp (cubicThetaPrincipal_fixed_eq_one _ _ hf)).symm

lemma cubicThetaFundamentalDomain_isFundamentalDomain (μ : Measure CubicThetaPoint) :
    IsFundamentalDomain cubicThetaPrincipalGroup cubicThetaFundamentalDomain μ :=
  IsFundamentalDomain.mk' cubicThetaFundamentalDomain_measurable.nullMeasurableSet
    cubicThetaFundamentalDomain_unique

end CubicFirstMoment

end

end OAI
