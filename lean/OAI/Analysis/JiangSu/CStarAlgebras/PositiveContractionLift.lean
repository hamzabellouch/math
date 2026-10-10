import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

noncomputable section
open CStarAlgebra
open scoped NNReal

namespace CStarLift
variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem exists_positive_contraction (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Surjective φ)
    {e : B} (hep : 0≤e) (hen : ‖e‖≤1) :
    ∃ x : A, φ x=e ∧ 0≤x ∧ ‖x‖≤1 := by
  obtain ⟨z,hz⟩ := hφ (CFC.sqrt e)
  let a := star z*z
  have hap : 0≤a := star_mul_self_nonneg z
  have ha : φ a=e := by
    simp only [a,map_mul,map_star,hz,(CFC.sqrt_nonneg e).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self e hep
  let f : ℝ≥0 → ℝ≥0 := fun t => min t 1
  have hf : Continuous f := continuous_id.min continuous_const
  have hf0 : f 0=0 := min_eq_left zero_le_one
  refine ⟨cfcₙ f a,?_,cfcₙ_nonneg_of_predicate,?_⟩
  · rw [φ.map_cfcₙ f a hf.continuousOn hf0 (by fun_prop) hap (ha.symm ▸ hep),ha]
    conv_rhs => rw [← cfcₙ_id ℝ≥0 e]
    apply cfcₙ_congr
    intro t ht
    exact min_eq_left ((le_nnnorm_of_mem_quasispectrum ht).trans (by exact_mod_cast hen))
  · exact_mod_cast (nnnorm_cfcₙ_nnreal_le (a := a) (f := f) (fun t _ => min_le_right t 1))

end CStarLift

end
end

end OAI
