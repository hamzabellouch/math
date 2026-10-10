import OAI.Combinatorics.CompleteCrossing.Polynomials
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

namespace OAI

/-! The support form, injectivity criterion, and support-space dimension. -/

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

theorem collision_nonzero_on_support {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n) (a : SupportCoord J) :
    evalFour (node a.val.1.1) (node a.val.1.2) (node a.val.2.1) (node a.val.2.2)
      collisionFactor ≠ 0 := by
  rcases (Finset.mem_filter.mp a.property).2 with ⟨_, _, h02, h03, h12, h13, _⟩
  simpa [evalFour, collisionFactor, Matrix.cons_val_two, Matrix.cons_val_three] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hn.ne h02))
      (sub_ne_zero.mpr (hn.ne h03))) (sub_ne_zero.mpr (hn.ne h12)))
      (sub_ne_zero.mpr (hn.ne h13))

lemma support_diagonal_nonzero {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n) (a : SupportCoord J) :
    supportDiagonal node J a ≠ 0 := by
  rcases (Finset.mem_filter.mp a.property).2 with ⟨h01, h23, _, _, _, _, hJ⟩
  have hc := collision_nonzero_on_support node hn J a
  have hf : evalFour (node a.val.1.1) (node a.val.1.2) (node a.val.2.1)
      (node a.val.2.2) fullDifference ≠ 0 := by
    simpa [fullDifference, evalFour, Matrix.cons_val_two, Matrix.cons_val_three] using
      mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hn.ne (ne_of_lt h01)))
        (sub_ne_zero.mpr (hn.ne (ne_of_lt h23)))) hc
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hJ
    (weight_nonzero node hn _)) (weight_nonzero node hn _))
      (weight_nonzero node hn _)) (weight_nonzero node hn _)) hf

theorem support_bilinear_nondegenerate {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n) :
    (supportBilinear node J).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => support_diagonal_nonzero node hn J a

theorem isotropic_dimension {ι : Type*} [Fintype ι]
    (B : LinearMap.BilinForm ℝ (ι → ℝ)) (hB : B.Nondegenerate)
    (W : Submodule ℝ (ι → ℝ)) (hW : W ≤ B.orthogonal W) :
    2 * Module.finrank ℝ W ≤ Fintype.card ι := by
  have hle := Submodule.finrank_mono hW
  rw [LinearMap.BilinForm.finrank_orthogonal hB] at hle
  have hdim := Submodule.finrank_le W
  have hv : Module.finrank ℝ (ι → ℝ) = Fintype.card ι := by simp
  rw [hv] at hle hdim
  omega

end Paper170

end
end

section

noncomputable section
namespace Paper170

@[simp] lemma evalFour_mul (x u y v : ℝ) (P Q : Poly4) :
    evalFour x u y v (P * Q) = evalFour x u y v P * evalFour x u y v Q :=
  map_mul (MvPolynomial.aeval ![x, u, y, v]) P Q

lemma support_evaluation_injective_of_collision {n s : ℕ} (hs : 2 ≤ s)
    (node : Fin n → ℝ) (hn : Function.Injective node) (J : CrossingTensor n)
    (hdiv : ∀ P : endpointSymmetricSpace s,
      supportEvaluation s node J P = 0 → collisionFactor ∣ P.val) :
    Function.Injective (supportEvaluation s node J) := by
  have hzero : ∀ d (P : endpointSymmetricSpace s), P.val.degreeOf 0 = d →
      supportEvaluation s node J P = 0 → P.val = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro P hd hP
      by_contra hP0
      obtain ⟨Q, hQ0, heq, hQmem, _, hQdeg⟩ := collision_quotient s hs P.val
        P.property hP0 (hdiv P hP)
      have hQ : supportEvaluation s node J ⟨Q, hQmem⟩ = 0 := by
        funext a
        have hp := congrFun hP a
        change evalFour (node a.val.1.1) (node a.val.1.2)
          (node a.val.2.1) (node a.val.2.2) P.val = 0 at hp
        rw [heq, evalFour_mul] at hp
        exact (mul_eq_zero.mp hp).resolve_left (collision_nonzero_on_support node hn J a)
      exact hQ0 (ih (Q.degreeOf 0) (by omega) ⟨Q, hQmem⟩ rfl hQ)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro P hP
  exact Subtype.ext (hzero _ P rfl hP)

end Paper170

end
end

section

noncomputable section
namespace Paper170

lemma support_cardinality_of_injective_isotropic {n s : ℕ} (hs : 2 ≤ s)
    (node : Fin n → ℝ) (hn : Function.Injective node) (J : CrossingTensor n)
    (hi : Function.Injective (supportEvaluation s node J))
    (ho : ∀ P Q : endpointSymmetricSpace s,
      supportBilinear node J (supportEvaluation s node J P) (supportEvaluation s node J Q) = 0) :
    2 * (Nat.choose s 2) ^ 2 ≤ (supportedPairs J).card := by
  let := symmetric_space_finite s
  let f := supportEvaluation s node J
  have hr : f.range ≤ (supportBilinear node J).orthogonal f.range := by
    rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩
    exact ho Q P
  have hd := isotropic_dimension (supportBilinear node J)
    (support_bilinear_nondegenerate node hn J) f.range hr
  have he : Module.finrank ℝ f.range = Module.finrank ℝ (endpointSymmetricSpace s) :=
    (LinearEquiv.ofInjective f hi).finrank_eq.symm
  rw [he, symmetric_space_dimension s hs, Fintype.card_coe] at hd
  exact hd

end Paper170

end
end

end OAI
