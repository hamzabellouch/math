import OAI.GroupTheory.PolycyclicRecognition.Algebra.OrderedCentralWords
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralBilinearRealization

namespace OAI

/-! # The bilinear law obtained by collecting an ordered word -/

noncomputable section
namespace PolycyclicRecognition
variable {d e : ℕ}

def triangularBilinear (c : Fin d → Fin d → Fin e → ℤ) :
    (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℤ) →ₗ[ℤ] (Fin e → ℤ) :=
  coefficientBilinear (fun k i j => if j < i then c i j k else 0)

theorem triangularFactor_ofAdd (c : Fin d → Fin d → Fin e → ℤ) (x y : Fin d → ℤ) :
    triangularFactor (fun i j => Multiplicative.ofAdd (c i j)) x y =
      Multiplicative.ofAdd (triangularBilinear c x y) := by
  calc
    triangularFactor (fun i j => Multiplicative.ofAdd (c i j)) x y =
        ∏ i, ∏ j, Multiplicative.ofAdd (if j < i then (x i * y j) • c i j else 0) := by
      unfold triangularFactor
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro j _
      split_ifs
      · exact (ofAdd_zsmul _ _).symm
      · rfl
    _ = Multiplicative.ofAdd (∑ i, ∑ j, if j < i then (x i * y j) • c i j else 0) := by
      simp only [ofAdd_sum]
    _ = Multiplicative.ofAdd (triangularBilinear c x y) := by
      congr 1
      ext k
      change (∑ i, ∑ j, if j < i then (x i * y j) • c i j else 0) k =
        ∑ i, ∑ j, (if j < i then c i j k else 0) * x i * y j
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j < i
      · simp only [h, ite_true, Pi.smul_apply, smul_eq_mul]
        ring
      · simp [h]

end PolycyclicRecognition

end

end OAI
