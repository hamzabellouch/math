import OAI.NumberTheory.Ostmann.Tree.DifferenceConvolution

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem sum_three_rotate {I J K R : Type*} [Fintype I] [Fintype J] [Fintype K]
    [AddCommMonoid R] (f : I → J → K → R) :
    (∑ i,∑ j,∑ k,f i j k)=∑ k,∑ i,∑ j,f i j k := by
  calc
    _ = ∑ i,∑ k,∑ j,f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem doubleMellin_mean (f : ZMod p → (ZMod p)ˣ → (ZMod p)ˣ → ℂ)
    (χ ψ : MulChar (ZMod p) ℂ) :
    doubleMellin (fun lam mu => mean (fun d => f d lam mu)) χ ψ=
      mean (fun d => doubleMellin (f d) χ ψ) := by
  simp only [doubleMellin,mean,mellin_const_mul,mellin_sum]

theorem doubleMellin_mean_energy (f : (ZMod p)ˣ → (ZMod p)ˣ → ZMod p → ℂ) :
    (Fintype.card (ZMod p)ˣ:ℝ)⁻¹^2*
      (∑ lam : (ZMod p)ˣ,∑ mu : (ZMod p)ˣ,l2Sq (f lam mu)) =
      ∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,
        l2Sq (fun y => doubleMellin (fun lam mu => f lam mu y) χ ψ) := by
  symm
  simp only [l2Sq,← Finset.mul_sum]
  rw [sum_three_rotate]
  simp_rw [doubleMellin_parseval]
  rw [← Finset.mul_sum]
  have hs := sum_three_rotate (fun lam mu y => ‖f lam mu y‖^2)
  rw [← hs]
  ring

end
end Ostmann.FiniteField

end OAI
