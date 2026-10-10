import Mathlib
import OAI.Analysis.Commutator.CFCIntertwiner
import OAI.Analysis.Commutator.CFCTraceMoments

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.BalancedDilation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma sqrt_eq_real_cfc (a : A) (ha : 0≤a) : CFC.sqrt a=cfc Real.sqrt a := by
  rw [CFC.sqrt_eq_real_sqrt a ha,cfcₙ_eq_cfc (hf0 := Real.sqrt_zero)]

lemma defect_nonneg (x : A) (hx : ‖x‖≤1) : 0≤1-x*star x := by
  apply sub_nonneg.mpr
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg (x*star x) (mul_star_self_nonneg x)).mp
  rw [CStarRing.norm_self_mul_star]
  exact (mul_le_mul_of_nonneg_right hx (norm_nonneg x)).trans (by simpa using hx)

lemma defect_intertwines (x : A) (hx : ‖x‖≤1) :
    CFC.sqrt (1-x*star x)*x=x*CFC.sqrt (1-star x*x) := by
  have h₁ := defect_nonneg x hx
  have h₂ : 0≤1-star x*x := by simpa only [star_star] using defect_nonneg (star x) (by simpa using hx)
  rw [sqrt_eq_real_cfc _ h₁,sqrt_eq_real_cfc _ h₂]
  exact (CFCIntertwiner.semiconj_cfc x (1-star x*x) (1-x*star x)
    (IsSelfAdjoint.of_nonneg h₂) (IsSelfAdjoint.of_nonneg h₁)
    (by noncomm_ring) Real.sqrt Real.continuous_sqrt).symm

lemma sqrt_sub_one_cfc (a : A) (ha : IsSelfAdjoint a) (hpos : 0≤1-a) :
    CFC.sqrt (1-a)=cfc (fun r : ℝ => Real.sqrt (1-r)) a := by
  have he : cfc (fun r : ℝ => 1-r) a=1-a := by
    simpa only [cfc_const (1 : ℝ) a ha,map_one,cfc_id' ℝ a ha] using
      cfc_sub (fun _ : ℝ => 1) (fun r : ℝ => r) a
  rw [sqrt_eq_real_cfc _ hpos,←he,←cfc_comp Real.sqrt (fun r : ℝ => 1-r) a]
  rfl

lemma defect_trace (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (x : A) (hx : ‖x‖≤1) : τ (CFC.sqrt (1-x*star x))=τ (CFC.sqrt (1-star x*x)) := by
  have h₁ := defect_nonneg x hx
  have h₂ : 0≤1-star x*x := by simpa only [star_star] using defect_nonneg (star x) (by simpa using hx)
  rw [sqrt_sub_one_cfc _ (by cfc_tac) h₁,sqrt_sub_one_cfc _ (by cfc_tac) h₂]
  apply CFCTraceMoments.trace_cfc_of_powers τ (x*star x) (star x*x)
    (by cfc_tac) (by cfc_tac)
    (fun n => CFCTraceMoments.trace_cyclic_powers τ hτ x (star x) n)
  fun_prop

end Kadison.BalancedDilation

end

end
end

end OAI
