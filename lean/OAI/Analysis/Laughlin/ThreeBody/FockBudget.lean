import OAI.Analysis.Laughlin.ThreeBody.FockComparison

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory Filter
open scoped BigOperators Matrix

theorem complexThreeGram_sub_one_spectral (Q : ℕ) (hQ : 2 ≤ Q) :
    complexThreeGram Q-1 = ∑ z : Fin (Q+1), (gramEigenvalueFormula Q z.val : ℂ) •
      (threeSpinProjector Q hQ z).map Complex.ofReal := by
  ext i j
  have h := congrArg Complex.ofReal (congrFun (congrFun (source_threeBody_spectral_decomposition Q hQ) i) j)
  simpa only [Matrix.sub_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Complex.ofReal_sub,Complex.ofReal_sum,Complex.ofReal_mul,Matrix.one_apply,
    apply_ite,Complex.ofReal_one,Complex.ofReal_zero,complexThreeGram,Matrix.map_apply] using h

theorem physical_threeBody_budget_eventually :
    ∀ᶠ Q : ℕ in atTop, ∃ _ : 15 ≤ Q, ∀ x : Space Q,
      (2*Q-2+1 : ℕ) * (∫ g, contractionForm Q (sourceThreeEnd Q)
        ((physicalThreeBodyMatrix Q).map Complex.ofReal) (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re -
          deltaFormula Q * sourceFockEnergy Q x ≤
      (contractionForm Q (sourceThreeEnd Q) (complexThreeGram Q-1) x).re := by
  filter_upwards [physical_threeBody_Fock_comparison_eventually] with Q h
  obtain ⟨hQ,h⟩ := h
  refine ⟨hQ,fun x => ?_⟩
  have hlo := h x
  have htail := physical_threeBody_tail_sum Q (by omega) x
  rw [complexThreeGram_sub_one_spectral Q (by omega),contractionForm_sum,Complex.re_sum]
  simp only [contractionForm_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  let f := fun z : Fin (Q+1) => gramEigenvalueFormula Q z.val *
    (contractionForm Q (sourceThreeEnd Q) ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x).re
  have he : (∑ z, f z) = (∑ z, if z.val ≤ 15 then f z else 0) +
      (∑ z, if 16 ≤ z.val then f z else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases h15 : z.val ≤ 15
    · simp [h15,show ¬16 ≤ z.val by omega]
    · simp [h15,show 16 ≤ z.val by omega]
  change _ ≤ ∑ z, f z
  rw [he]
  change _ ≤ ∑ z, if z.val ≤ 15 then f z else 0 at hlo
  change _ ≤ ∑ z, if 16 ≤ z.val then f z else 0 at htail
  linarith

end Laughlin.Fock

end OAI
