import OAI.Analysis.PureInfiniteness.InnerHomCompression

namespace OAI

/-! The additional scalar summand in the forced unitization of a unital
algebra, expressed as a genuine star homomorphism. -/

noncomputable section
namespace WeakPureInfiniteness

variable {D : Type*} [CStarAlgebra D]

lemma unitization_complement_mul_self :
    (1 - (Unitization.inr (1 : D) : Unitization ℂ D)) *
      (1 - Unitization.inr (1 : D)) = 1 - Unitization.inr (1 : D) := by
  have h : (Unitization.inr (1 : D) : Unitization ℂ D) * Unitization.inr 1 =
      Unitization.inr (1 : D) := by rw [← Unitization.inr_mul]; simp
  calc
    _ = 1 - Unitization.inr (1 : D) - Unitization.inr (1 : D) +
        (Unitization.inr (1 : D) : Unitization ℂ D) * Unitization.inr 1 := by noncomm_ring
    _ = _ := by rw [h]; abel

def scalarComplementHom : ℂ →⋆ₙₐ[ℂ] Unitization ℂ D where
  toFun c := c • (1 - Unitization.inr (1 : D))
  map_zero' := zero_smul _ _
  map_add' c d := add_smul c d _
  map_smul' c d := mul_smul c d _
  map_mul' c d := by
    rw [smul_mul_assoc, mul_smul_comm, unitization_complement_mul_self, smul_smul]
  map_star' c := by simp only [star_smul, star_sub, star_one, ← Unitization.inr_star]

@[simp] lemma scalarComplementHom_apply (c : ℂ) :
    scalarComplementHom (D := D) c = c • (1 - Unitization.inr (1 : D)) := rfl

end WeakPureInfiniteness

end

end OAI
