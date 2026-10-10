import OAI.Analysis.CircleDomains.Reflection.ReflectedSphereNormalization
import OAI.Analysis.CircleDomains.Topology.EntireHomeomorphAffine

namespace OAI

/-! The actual reflected conjugate is fractional linear. Moving its pole
 to infinity produces an entire plane homeomorphism, so Liouville's theorem
 supplies its affine formula. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma poleNormalized_differentiableAt_ne_zero (D : AnalyticReflectionData C) (i : I)
    {z : ℂ} (hz : z≠0) : DifferentiableAt ℂ (D.poleNormalized i : ℂ → ℂ) z := by
  have hp : D.principal (D.center i)+z⁻¹ ∈ ({D.principal (D.center i)}ᶜ : Set ℂ) := by
    exact add_ne_left.mpr (inv_ne_zero hz)
  have hd := ((D.reflectedLimit_holomorphic i _ hp).differentiableAt
    (isOpen_compl_singleton.mem_nhds hp)).comp z
      ((differentiableAt_const (D.principal (D.center i))).add (differentiableAt_inv hz))
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hz] with w hw
  exact D.poleNormalized_coe i hw

lemma poleNormalized_holomorphic (D : AnalyticReflectionData C) (i : I) :
    Differentiable ℂ (D.poleNormalized i : ℂ → ℂ) := by
  have hzero : AnalyticAt ℂ (D.poleNormalized i : ℂ → ℂ) 0 := by
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _
      (D.poleNormalized i).continuous.continuousAt
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact D.poleNormalized_differentiableAt_ne_zero i hz
  intro z
  by_cases hz : z=0
  · subst z
    exact hzero.differentiableAt
  · exact D.poleNormalized_differentiableAt_ne_zero i hz

lemma reflectedLimit_fractional_linear (D : AnalyticReflectionData C) (i : I) :
    ∃A : ℂ,A≠0 ∧ ∀z : ℂ,z≠D.principal (D.center i) →
      D.reflectedLimit i z=star (D.principal (D.center i))+A/(z-D.principal (D.center i)) := by
  obtain ⟨A,b,hA,hf⟩ := entire_homeomorph_affine (D.poleNormalized i)
    (D.poleNormalized_holomorphic i)
  have hb : b=star (D.principal (D.center i)) := by
    have h := hf 0
    simpa only [mul_zero,zero_add,D.poleNormalized_zero i] using h.symm
  refine ⟨A,hA,?_⟩
  intro z hz
  have hw : (z-D.principal (D.center i))⁻¹≠0 := inv_ne_zero (sub_ne_zero.mpr hz)
  have h := D.poleNormalized_coe i hw
  rw [inv_inv,add_sub_cancel] at h
  rw [←h,hf,hb,div_eq_mul_inv,add_comm]

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
