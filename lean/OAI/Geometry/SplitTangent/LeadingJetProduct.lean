import Mathlib

namespace OAI

/-! Leading Jet Product. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace SplitTangent.LeadingJet
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

lemma iteratedFDeriv_smul_zero {f : E → F} {u : E → ℂ} {x : E}
    (hf : AnalyticAt ℂ f x) (hu : AnalyticAt ℂ u x) (m : ℕ)
    (hu0 : u x=0) (hz : ∀n,n < m → iteratedFDeriv ℂ n f x=0) :
    iteratedFDeriv ℂ m (fun y => u y • f y) x=0 := by
  obtain ⟨s,hsub,hs,hxs⟩ := mem_nhds_iff.mp
    (hu.eventually_analyticAt.and hf.eventually_analyticAt)
  have hu' : ContDiffOn ℂ ω u s := fun y hy => (hsub hy).1.contDiffAt.contDiffWithinAt
  have hf' : ContDiffOn ℂ ω f s := fun y hy => (hsub hy).2.contDiffAt.contDiffWithinAt
  have hb := norm_iteratedFDerivWithin_smul_le hu' hf' hs.uniqueDiffOn hxs
    (n := m) (by simp only [le_top])
  have he (n : ℕ) (g : E → F) : iteratedFDerivWithin ℂ n g s x=iteratedFDeriv ℂ n g x :=
    iteratedFDerivWithin_of_isOpen n hs hxs
  have heu (n : ℕ) : iteratedFDerivWithin ℂ n u s x=iteratedFDeriv ℂ n u x :=
    iteratedFDerivWithin_of_isOpen n hs hxs
  simp only [he,heu] at hb
  have hs0 : (∑i∈Finset.range (m+1), (m.choose i : ℝ)*‖iteratedFDeriv ℂ i u x‖*
      ‖iteratedFDeriv ℂ (m-i) f x‖)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have him : i ≤ m := Finset.mem_range_succ_iff.mp hi
    by_cases hi0 : i=0
    · subst i
      rw [norm_iteratedFDeriv_zero,hu0,norm_zero,mul_zero,zero_mul]
    · rw [hz (m-i) (by omega),norm_zero,mul_zero]
  rw [hs0] at hb
  exact norm_le_zero_iff.mp hb

 

theorem iteratedFDeriv_smul_of_lower_zero {f : E → F} {u : E → ℂ} {x : E}
    (hf : AnalyticAt ℂ f x) (hu : AnalyticAt ℂ u x) (m : ℕ)
    (hz : ∀n,n < m → iteratedFDeriv ℂ n f x=0) :
    iteratedFDeriv ℂ m (fun y => u y • f y) x=u x • iteratedFDeriv ℂ m f x := by
  have hp := iteratedFDeriv_smul_zero hf (hu.sub analyticAt_const) m (sub_self _) hz
  have huf : ContDiffAt ℂ m (fun y => u y • f y) x := (hu.smul hf).contDiffAt
  have hcf : ContDiffAt ℂ m (fun y => u x • f y) x :=
    (hf.const_smul (c := u x)).contDiffAt
  have he : (fun y => (u y-u x) • f y)=
      (fun y => u y • f y)-(fun y => u x • f y) := by ext y; simp [sub_smul]
  change iteratedFDeriv ℂ m (fun y => (u y-u x) • f y) x=0 at hp
  rw [he,iteratedFDeriv_sub_apply huf hcf,
    iteratedFDeriv_const_smul_apply' (hf.contDiffAt)] at hp
  exact sub_eq_zero.mp hp

end SplitTangent.LeadingJet

end

end OAI
