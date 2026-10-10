import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeRegroup

namespace OAI

/-! Exact angular product regrouping across the whole height tail. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_tailPrimeTupleRegrouped_tail (i j : ℕ) (ξ H T X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :
    (∑ v ∈ Finset.range (heightWindowCount H T),
      tailPrimeTupleRegrouped i j ℓ ξ H (T*(3/2:ℝ)^v) X k s) =
      envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ X k s)
        (largeTupleOtherSupport ξ X k s) (fun b => theta ℓ b*largeTupleSelectedCoefficient ξ X k s b)
        (fun a => theta ℓ a*largeTupleOtherCoefficient ξ X k s a) primeProductEnvelope H T X := by
  unfold tailPrimeTupleRegrouped envelopeCutoffBilinearTail
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  simp only [productGaussHeightWindowKernel,theta_mul]
  ring

end CubicFirstMoment

end

end OAI
