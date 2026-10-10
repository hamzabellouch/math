import OAI.Analysis.CircleDomains.Reflection.CayleyHolomorphic

namespace OAI

/-! Exact Cayley side relations, including the reflected lower side. -/
open Complex
noncomputable section
namespace CircleDomainRigidity

lemma halfPlaneDisk_norm_lt_iff {z : ℂ} (hz : z+I≠0) :
    ‖halfPlaneDisk z‖<1 ↔ 0<z.im := by
  rw [halfPlaneDisk,norm_div,div_lt_one (norm_pos_iff.mpr hz)]
  have h := halfPlaneDisk_normSq z
  simp only [←Complex.sq_norm] at h
  constructor <;> intro ht <;>
    nlinarith [norm_nonneg (z-I),norm_nonneg (z+I)]

lemma halfPlaneDisk_norm_gt_iff {z : ℂ} (hz : z+I≠0) :
    1<‖halfPlaneDisk z‖ ↔ z.im<0 := by
  rw [halfPlaneDisk,norm_div,lt_div_iff₀ (norm_pos_iff.mpr hz),one_mul]
  have h := halfPlaneDisk_normSq z
  simp only [←Complex.sq_norm] at h
  constructor <;> intro ht <;>
    nlinarith [norm_nonneg (z-I),norm_nonneg (z+I)]

lemma halfPlaneDisk_norm_eq_iff {z : ℂ} (hz : z+I≠0) :
    ‖halfPlaneDisk z‖=1 ↔ z.im=0 := by
  rw [halfPlaneDisk,norm_div,div_eq_one_iff_eq (norm_ne_zero_iff.mpr hz)]
  have h := halfPlaneDisk_normSq z
  simp only [←Complex.sq_norm] at h
  constructor <;> intro ht <;>
    nlinarith [norm_nonneg (z-I),norm_nonneg (z+I)]

end CircleDomainRigidity

end

end OAI
