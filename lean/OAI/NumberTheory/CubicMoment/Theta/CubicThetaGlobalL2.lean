import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotientLocalFiniteness
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothTests

namespace OAI

/-! Actual automorphic sections as global L2 vectors. A Borel section
chooses representatives, while the norm is the continuous intrinsic norm
on the quotient, so compact smooth sections are square integrable. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

abbrev CubicThetaGlobalL2 := Lp ℂ 2 cubicThetaQuotientMeasure

def cubicThetaSectionRepresentative (F : CubicThetaSection) (q : CubicThetaQuotient) : ℂ :=
  F.val (cubicThetaBorelSection q)

lemma cubicThetaSectionRepresentative_measurable (F : CubicThetaSection) :
    Measurable (cubicThetaSectionRepresentative F) :=
  F.val.continuous.measurable.comp cubicThetaBorelSection_measurable

lemma cubicThetaSectionRepresentative_norm (F : CubicThetaSection) (q : CubicThetaQuotient) :
    ‖cubicThetaSectionRepresentative F q‖=cubicThetaSectionNorm F q := by
  have h := cubicThetaSectionNorm_apply F (cubicThetaBorelSection q)
  rw [cubicThetaBorelSection_rightInverse q] at h
  exact h.symm

lemma cubicThetaSectionRepresentative_memLp (F : cubicThetaSmoothTests) :
    MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure := by
  have hnorm : MemLp (cubicThetaSectionNorm F) 2 cubicThetaQuotientMeasure :=
    (cubicThetaSectionNorm_continuous F).memLp_of_hasCompactSupport F.property.2
  apply (memLp_norm_iff (cubicThetaSectionRepresentative_measurable F).aestronglyMeasurable).mp
  simpa only [cubicThetaSectionRepresentative_norm] using hnorm

def cubicThetaGlobalMass : cubicThetaSmoothTests →ₗ[ℂ] CubicThetaGlobalL2 where
  toFun F := (cubicThetaSectionRepresentative_memLp F).toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(cubicThetaSectionRepresentative_memLp (F+G)).coeFn_toLp,
      (cubicThetaSectionRepresentative_memLp F).coeFn_toLp,
      (cubicThetaSectionRepresentative_memLp G).coeFn_toLp,
      Lp.coeFn_add ((cubicThetaSectionRepresentative_memLp F).toLp _)
        ((cubicThetaSectionRepresentative_memLp G).toLp _)] with q hFG hF hG hadd
    simp only [Pi.add_apply] at hadd
    rw [hFG,hadd,hF,hG]
    rfl
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(cubicThetaSectionRepresentative_memLp (c • F)).coeFn_toLp,
      (cubicThetaSectionRepresentative_memLp F).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaSectionRepresentative_memLp F).toLp _)] with q hCF hF hsmul
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply] at hsmul
    rw [hCF,hsmul,hF]
    rfl

def cubicThetaAutomorphicL2 : Submodule ℂ CubicThetaGlobalL2 :=
  cubicThetaGlobalMass.range.topologicalClosure

instance cubicThetaAutomorphicL2_complete : CompleteSpace cubicThetaAutomorphicL2 :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

end CubicFirstMoment

end

end OAI
