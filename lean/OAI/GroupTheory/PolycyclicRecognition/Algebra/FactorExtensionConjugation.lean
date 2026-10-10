import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionMap

namespace OAI

/-! # Conjugation on the completed kernel in factor coordinates -/

namespace PolycyclicRecognition.FactorExtension
variable {N Q : Type*} [Group N] [Group Q] (S : NonabelianFactorSystem N Q)

theorem conjugation_inl (a : FactorExtension S) (n : N) :
    (groupExtension S).conjAct a n = a.left * S.action a.right n * a.left⁻¹ := by
  apply (groupExtension S).inl_injective
  rw [(groupExtension S).inl_conjAct_comm]
  apply mul_inv_eq_iff_eq_mul.mpr
  change a * inl S n = inl S (a.left * S.action a.right n * a.left⁻¹) * a
  apply FactorExtension.ext
  · change a.left * S.action a.right n * S.factor a.right 1 =
      (a.left * S.action a.right n * a.left⁻¹) * S.action 1 a.left * S.factor 1 a.right
    rw [S.factor_one_right, S.action_one, MulAut.one_apply, S.factor_one_left]
    group
  · exact (mul_one a.right).trans (one_mul a.right).symm

theorem conjugation_eq (a : FactorExtension S) :
    (groupExtension S).conjAct a = MulAut.conj a.left * S.action a.right := by
  apply DFunLike.ext
  exact conjugation_inl S a

/-- The coordinate section has exactly the prescribed kernel action. -/
theorem conjugation_section (q : Q) :
    (groupExtension S).conjAct (⟨1, q⟩ : FactorExtension S) = S.action q := by
  rw [conjugation_eq]
  change MulAut.conj 1 * S.action q = S.action q
  rw [map_one, one_mul]

end PolycyclicRecognition.FactorExtension

end OAI
