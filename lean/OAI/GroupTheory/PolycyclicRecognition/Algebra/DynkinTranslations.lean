import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGroupLaws

namespace OAI

/-! # The actual inverse of a coordinate right translation -/

noncomputable section

namespace PolycyclicRecognition

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The finite group laws give a homeomorphism, with inverse translation
parameter `-q`. This identifies the inverse used by sampling densities. -/
def dynkinRightTranslation {c : ℕ} (a : DynkinCoefficients c 2)
    (B : V →L[ℝ] V →L[ℝ] V) (h : PolynomialGroupLaws (dynkinProduct a B))
    (q : V) : V ≃ₜ V where
  toFun x := dynkinProduct a B x q
  invFun x := dynkinProduct a B x (-q)
  left_inv x := by
    change dynkinProduct a B (dynkinProduct a B x q) (-q) = x
    rw [h.1]
    have hq : dynkinProduct a B q (-q) = 0 := by
      simpa only [neg_neg] using h.2.2.2.1 (-q)
    rw [hq, h.2.2.1]
  right_inv x := by
    change dynkinProduct a B (dynkinProduct a B x (-q)) q = x
    rw [h.1, h.2.2.2.1, h.2.2.1]
  continuous_toFun := continuous_dynkinProduct a _ _ _
    continuous_const continuous_id continuous_const
  continuous_invFun := continuous_dynkinProduct a _ _ _
    continuous_const continuous_id continuous_const

@[simp] theorem dynkinRightTranslation_apply {c : ℕ} (a : DynkinCoefficients c 2)
    (B : V →L[ℝ] V →L[ℝ] V) (h : PolynomialGroupLaws (dynkinProduct a B))
    (q x : V) : dynkinRightTranslation a B h q x = dynkinProduct a B x q := rfl

@[simp] theorem dynkinRightTranslation_symm_apply {c : ℕ} (a : DynkinCoefficients c 2)
    (B : V →L[ℝ] V →L[ℝ] V) (h : PolynomialGroupLaws (dynkinProduct a B))
    (q x : V) : (dynkinRightTranslation a B h q).symm x =
      dynkinProduct a B x (-q) := rfl

end PolycyclicRecognition

end

end OAI
