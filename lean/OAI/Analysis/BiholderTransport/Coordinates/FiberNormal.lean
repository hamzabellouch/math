import Mathlib

namespace OAI

section

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma outward_inner_ratio {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p e : E} {t D κ L : ℝ} (he : ‖e‖=1) (ht : 0<t)
    (hh : 0 < inner ℝ p e) (hκ : 0<κ) (hL : 0<L)
    (hhD : κ*D ≤ (inner ℝ p e)^2)
    (hgap : ‖p+t • e‖^2-‖p‖^2 ≤ L*D) :
    0 < inner ℝ p (t • e) ∧ ‖t • e‖^2/inner ℝ p (t • e) ≤ L/(2*κ) := by
  have hN : ‖t • e‖=t := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht,he,mul_one]
  have hI : inner ℝ p (t • e)=t*inner ℝ p e := by simp only [real_inner_smul_right]
  refine ⟨by rw [hI]; exact mul_pos ht hh,?_⟩
  rw [norm_add_sq_real,hN,hI] at hgap
  have H1 := mul_le_mul_of_nonneg_left hgap hκ.le
  have H2 := mul_le_mul_of_nonneg_left hhD hL.le
  have hT : 2*κ*t ≤ L*inner ℝ p e := by
    nlinarith only [H1,H2,hh,mul_nonneg hκ.le (sq_nonneg t)]
  have hr : ‖t • e‖^2/inner ℝ p (t • e)=t/inner ℝ p e := by
    rw [hN,hI]
    field_simp
  rw [hr,div_le_div_iff₀ hh (show 0<2*κ by positivity)]
  nlinarith only [hT]

end WeakMTWTransport
end
end
end

end OAI
