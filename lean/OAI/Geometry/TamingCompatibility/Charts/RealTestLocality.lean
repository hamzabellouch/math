import Mathlib

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open Set Filter TemperedDistribution
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma postcomp_support {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G →L[ℝ] H) (φ : 𝓢(E,G)) :
    tsupport (SchwartzMap.postcompCLM L φ) ⊆ tsupport φ :=
  tsupport_comp_subset (map_zero L) φ

lemma real_imag_decomposition (φ : 𝓢(E,ℂ)) :
    φ = SchwartzMap.postcompCLM Complex.ofRealCLM (SchwartzMap.postcompCLM Complex.reCLM φ) +
      Complex.I • SchwartzMap.postcompCLM Complex.ofRealCLM (SchwartzMap.postcompCLM Complex.imCLM φ) := by
  ext x
  simp only [SchwartzMap.postcompCLM_apply,_root_.add_apply,_root_.smul_apply,
    Complex.ofRealCLM_apply,Complex.reCLM_apply,Complex.imCLM_apply,smul_eq_mul]
  simpa only [mul_comm] using (Complex.re_add_im (φ x)).symm

lemma real_tests_equal {U : Set E} {u v : 𝓢'(E,F)}
    (h : ∀ φ : 𝓢(E,ℝ), HasCompactSupport (φ : E → ℝ) → tsupport φ ⊆ U →
      u (SchwartzMap.postcompCLM Complex.ofRealCLM φ) =
      v (SchwartzMap.postcompCLM Complex.ofRealCLM φ))
    (φ : 𝓢(E,ℂ)) (hc : HasCompactSupport (φ : E → ℂ)) (hU : tsupport φ ⊆ U) : u φ = v φ := by
  have hr := postcomp_support Complex.reCLM φ
  have hi := postcomp_support Complex.imCLM φ
  have her := h (SchwartzMap.postcompCLM Complex.reCLM φ)
    (hc.of_isClosed_subset (isClosed_tsupport _) hr) (hr.trans hU)
  have hei := h (SchwartzMap.postcompCLM Complex.imCLM φ)
    (hc.of_isClosed_subset (isClosed_tsupport _) hi) (hi.trans hU)
  conv_lhs => rw [real_imag_decomposition φ]
  conv_rhs => rw [real_imag_decomposition φ]
  simp only [map_add,map_smul,her,hei]

lemma localize_eq_of_real_tests {U : Set E} {u v : 𝓢'(E,F)}
    (h : ∀ φ : 𝓢(E,ℝ), HasCompactSupport (φ : E → ℝ) → tsupport φ ⊆ U →
      u (SchwartzMap.postcompCLM Complex.ofRealCLM φ) =
      v (SchwartzMap.postcompCLM Complex.ofRealCLM φ))
    (g : 𝓢(E,ℂ)) (hc : HasCompactSupport (g : E → ℂ)) (hU : tsupport g ⊆ U) :
    smulLeftCLM F g u = smulLeftCLM F g v := by
  ext φ
  apply real_tests_equal h
  · exact hc.of_isClosed_subset (isClosed_tsupport _)
      ((SchwartzMap.tsupport_smulLeftCLM_subset g φ).trans inter_subset_right)
  · exact (SchwartzMap.tsupport_smulLeftCLM_subset g φ).trans (inter_subset_right.trans hU)
end TamingCompatibility.ComplexMatrix

end

end OAI
