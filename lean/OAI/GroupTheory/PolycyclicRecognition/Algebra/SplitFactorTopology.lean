import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionTopology
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectProductTopology
import Mathlib.GroupTheory.GroupExtension.Basic

namespace OAI

/-! # The topological semidirect decomposition of a split factor system -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] factorExtensionTopology semidirectProductTopology
variable {N Q : Type*} [Group N] [Group Q]
  (S : NonabelianFactorSystem N Q) (s : (FactorExtension.groupExtension S).Splitting)

abbrev splitFactorEquiv : (N ⋊[s.conjAct] Q) ≃* FactorExtension S :=
  s.semidirectProductMulEquiv

@[simp] theorem splitFactorEquiv_left (a : N ⋊[s.conjAct] Q) :
    (splitFactorEquiv S s a).left = a.left * (s a.right).left := by
  change (a.left * S.action 1 (s a.right).left) * S.factor 1 (s a.right).right = _
  rw [S.action_one, MulAut.one_apply, S.factor_one_left, mul_one]

@[simp] theorem splitFactorEquiv_right (a : N ⋊[s.conjAct] Q) :
    (splitFactorEquiv S s a).right = a.right := by
  change 1 * (s a.right).right = a.right
  rw [one_mul]
  exact s.rightInverse_rightHom a.right

@[simp] theorem splitFactorEquiv_symm_right (a : FactorExtension S) :
    ((splitFactorEquiv S s).symm a).right = a.right := by
  have h := congrArg FactorExtension.right ((splitFactorEquiv S s).apply_symm_apply a)
  exact (splitFactorEquiv_right S s _).symm.trans h

@[simp] theorem splitFactorEquiv_symm_left (a : FactorExtension S) :
    ((splitFactorEquiv S s).symm a).left = a.left * (s a.right).left⁻¹ := by
  have h := congrArg FactorExtension.left ((splitFactorEquiv S s).apply_symm_apply a)
  rw [splitFactorEquiv_left, splitFactorEquiv_symm_right] at h
  exact eq_mul_inv_iff_mul_eq.mpr h

variable [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [DiscreteTopology Q]
include S s

theorem splitFactorEquiv_continuous (hA : ∀ q, Continuous (S.action q)) :
    Continuous (splitFactorEquiv S s) := by
  let := factorExtensionTopologicalGroup S hA
  have hs : Continuous s := continuous_of_discreteTopology
  exact ((continuous_factor_inl S).comp (continuous_semidirect_left s.conjAct)).mul
    (hs.comp (continuous_semidirect_right s.conjAct))

theorem splitFactorEquiv_symm_continuous : Continuous (splitFactorEquiv S s).symm := by
  have hs : Continuous s := continuous_of_discreteTopology
  apply continuous_induced_rng.2
  change Continuous (fun a : FactorExtension S =>
    (((splitFactorEquiv S s).symm a).left, ((splitFactorEquiv S s).symm a).right))
  simp only [splitFactorEquiv_symm_left, splitFactorEquiv_symm_right]
  exact (continuous_factor_left S |>.mul
    ((continuous_factor_left S).comp (hs.comp (continuous_factor_right S))).inv).prodMk
      (continuous_factor_right S)

end PolycyclicRecognition

end

end OAI
