import OAI.Analysis.BernoulliCone.SmallPerturbation

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology
namespace Bernoulli.Shape
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

def rankOneMap (a : E →L[ℝ] ℝ) (e : E) (t : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + t • a.smulRight e

def rankOneInverse (a : E →L[ℝ] ℝ) (e : E) (t : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (t/(1+t*a e)) • a.smulRight e

@[simp] lemma rankOneMap_apply (a : E →L[ℝ] ℝ) (e : E) (t : ℝ) (x : E) :
    rankOneMap a e t x = x+(t*a x) • e := by
  simp [rankOneMap,smul_smul]
@[simp] lemma rankOneInverse_apply (a : E →L[ℝ] ℝ) (e : E) (t : ℝ) (x : E) :
    rankOneInverse a e t x = x-((t/(1+t*a e))*a x) • e := by
  simp [rankOneInverse,smul_smul]

lemma rankOne_left_inverse (a : E →L[ℝ] ℝ) (e : E) (t : ℝ) (h : 1+t*a e ≠ 0) :
    Function.LeftInverse (rankOneInverse a e t) (rankOneMap a e t) := by
  intro x
  rw [rankOneInverse_apply,rankOneMap_apply]
  simp only [map_add,map_smul,smul_eq_mul]
  have hh : t/(1+t*a e)*(a x+t*a x*a e) = t*a x := by field_simp
  rw [hh,add_sub_cancel_right]

lemma rankOne_right_inverse (a : E →L[ℝ] ℝ) (e : E) (t : ℝ) (h : 1+t*a e ≠ 0) :
    Function.RightInverse (rankOneInverse a e t) (rankOneMap a e t) := by
  intro x
  rw [rankOneMap_apply,rankOneInverse_apply]
  simp only [map_sub,map_smul,smul_eq_mul]
  have hh : t*(a x-(t/(1+t*a e)*a x)*a e) = t/(1+t*a e)*a x := by field_simp; ring
  rw [hh,sub_add_cancel]

def rankOneEquiv (a : E →L[ℝ] ℝ) (e : E) (t : ℝ) (h : 1+t*a e ≠ 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse (rankOneMap a e t) (rankOneInverse a e t)
    (rankOne_left_inverse a e t h) (rankOne_right_inverse a e t h)

@[simp] lemma rankOneEquiv_coe (a : E →L[ℝ] ℝ) (e : E) (t : ℝ) (h : 1+t*a e ≠ 0) :
    (rankOneEquiv a e t h : E →L[ℝ] E) = rankOneMap a e t := rfl
@[simp] lemma rankOneEquiv_symm_coe (a : E →L[ℝ] ℝ) (e : E) (t : ℝ) (h : 1+t*a e ≠ 0) :
    ((rankOneEquiv a e t h).symm : E →L[ℝ] E) = rankOneInverse a e t := rfl

lemma dual_rankOneInverse (a b : E →L[ℝ] ℝ) (e : E) (t : ℝ) :
    b.comp (rankOneInverse a e t) = b - (t*b e/(1+t*a e)) • a := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,rankOneInverse_apply,map_sub,map_smul,
    smul_eq_mul,sub_apply,smul_apply]
  ring
end Bernoulli.Shape

end
end

end OAI
