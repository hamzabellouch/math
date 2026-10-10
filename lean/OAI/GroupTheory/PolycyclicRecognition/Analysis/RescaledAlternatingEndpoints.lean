import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlternatingProductImage
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BoxCoordinateChanges
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledWordEndpoints
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoordinateChartSampling

namespace OAI

/-! # The alternating coordinate map is the actual nilpotent product -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {L G : Type*} [LieRing L] [LieAlgebra ℝ L] [Group G]

theorem exp_basis_alternatingProduct {n h c : ℕ}
    (b b₁ b₂ : Basis (Fin n) ℝ L) (Exp : L → G)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (z : Fin h → (Fin n → ℝ) × (Fin n → ℝ)) :
    Exp (b.equivFun.symm (alternatingCoordinateProduct a (basisBracket b)
      (boxCoordinateChange b b₁) (boxCoordinateChange b b₂) z)) =
      (List.ofFn (fun j => Exp (b₁.equivFun.symm (z j).1) *
        Exp (b₂.equivFun.symm (z j).2))).prod := by
  unfold alternatingCoordinateProduct
  rw [exp_basis_listProduct b Exp hzero a hm, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply]
  rw [exp_basis_dynkinProduct b Exp a hm]
  simp only [boxCoordinateChange_apply, LinearEquiv.symm_apply_apply]

theorem exp_flatAlternatingProduct {m n h c : ℕ}
    (b b₁ b₂ : Basis (Fin n) ℝ L) (Exp : L → G)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin h → (Fin n → ℝ) × (Fin n → ℝ)))
    (x : Fin m → ℝ) :
    Exp (b.equivFun.symm (flatAlternatingProduct a e
      (basisBracket b, boxCoordinateChange b b₁, boxCoordinateChange b b₂) x)) =
      (List.ofFn (fun j => Exp (b₁.equivFun.symm (e x j).1) *
        Exp (b₂.equivFun.symm (e x j).2))).prod :=
  exp_basis_alternatingProduct b b₁ b₂ Exp hzero a hm (e x)

end PolycyclicRecognition

end

end OAI
