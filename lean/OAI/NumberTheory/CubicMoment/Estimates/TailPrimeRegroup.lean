import OAI.NumberTheory.CubicMoment.Estimates.UpperTailTuple
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleKernelIntegral
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedTailEnvelope

namespace OAI

/-! Exact prime-tuple regrouping for the Gauss height tail. The original
product envelope and finite weights survive both support changes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tailPrimeTupleIndependentSum (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (H U X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) : ℂ :=
  ∑ f ∈ Fintype.piFinset (fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X k)
      (largeTupleNormScale k)),
    (∏ a, largeTupleCoordinateWeight ξ X k a (norm (f a)/largeTupleNormScale k a))*
      productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (∏ a, f a)

theorem tailPrimeTuplePiece_full (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (H U X : ℝ)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hb : ∀ a, 2*largeTupleNormScale (fun a => (k a).val) a ≤ Real.exp primeProductWeights.radius*X) :
    tailPrimeTuplePiece i j ℓ ξ H U X k =
      ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
        tailPrimeTupleIndependentSum i j ℓ ξ H U X (fun a => (k a).val) := by
  unfold tailPrimeTuplePiece tailPrimeTupleIndependentSum
  congr 1
  have he := independent_tuple_sum_sum_type
    (fun _ : Fin i ⊕ Fin j => primeCutoff (Real.exp primeProductWeights.radius*X))
    (fun q => (∏ a, largeTupleCoordinateWeight ξ X (fun a => (k a).val) a
      (norm (largeTupleVector q a)/largeTupleNormScale (fun a => (k a).val) a))*
      productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (∏ a, largeTupleVector q a))
  simp_rw [largeTupleVector_split] at he
  rw [independent_tuple_sum_support
    (fun _ : Fin i ⊕ Fin j => primeCutoff (Real.exp primeProductWeights.radius*X))
    (fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X (fun a => (k a).val))
      (largeTupleNormScale (fun a => (k a).val)))
    (fun a p => largeTupleCoordinateWeight ξ X (fun a => (k a).val) a
      (norm p/largeTupleNormScale (fun a => (k a).val) a))
    (fun f => productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (∏ a, f a))
    (largeTuple_coordinate_support ξ X (fun a => (k a).val) hb)] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro q _hq
  simp only [largeTupleVector_norm,largeTupleVector_prod,largeTupleCoordinateWeight_product]
  unfold tailPrimeTupleTerm
  ring


def tailPrimeTupleRegrouped (i j : ℕ) (ℓ : ℤ) (ξ H U X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) : ℂ :=
  ∑ b ∈ largeTupleSelectedSupport ξ X k s,
    ∑ a ∈ largeTupleOtherSupport ξ X k s,
      largeTupleSelectedCoefficient ξ X k s b*largeTupleOtherCoefficient ξ X k s a*
        productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (b*a)

theorem tailPrimeTupleIndependent_regroup (i j : ℕ) (ℓ : ℤ) (ξ H U X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :
    tailPrimeTupleIndependentSum i j ℓ ξ H U X k =
      tailPrimeTupleRegrouped i j ℓ ξ H U X k s := by
  have he := independent_prime_tuple_kernel s
    (fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X k) (largeTupleNormScale k))
    (fun a p => largeTupleCoordinateWeight ξ X k a (norm p/largeTupleNormScale k a))
    (fun a p hp => (fullPrimeSupport_prime 2 (largeTupleCoordinateWeight ξ X k)
      (largeTupleNormScale k) a p hp).1)
    (productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X) (by
      intro n hn hns
      have hz : gauss n = 0 := norm_eq_zero.mp (by rw [norm_gauss hn,ite_eq_right hns])
      simp only [productGaussHeightWindowKernel,hz,mul_zero,zero_mul])
  have hS : (fun a : s => fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X k)
      (largeTupleNormScale k) a) =
      fullPrimeSupport 2 (fun a : s => largeTupleCoordinateWeight ξ X k a)
        (fun a : s => largeTupleNormScale k a) := rfl
  have hT : (fun a : {a : Fin i ⊕ Fin j // a ∉ s} =>
      fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X k) (largeTupleNormScale k) a) =
      fullPrimeSupport 2
        (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleCoordinateWeight ξ X k a)
        (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleNormScale k a) := rfl
  rw [hS,hT] at he
  simpa only [tailPrimeTupleIndependentSum,tailPrimeTupleRegrouped,
    largeTupleSelectedSupport,largeTupleOtherSupport,largeTupleSelectedCoefficient,
    largeTupleOtherCoefficient,fullSquarefreePrimeSupport,fullPrimeCoefficient,
    isCoprime_one_right,and_true] using he

theorem tailPrimeTupleRegrouped_tail (i j : ℕ) (ξ H T X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :
    (∑ v ∈ Finset.range (heightWindowCount H T),
      tailPrimeTupleRegrouped i j 0 ξ H (T*(3/2:ℝ)^v) X k s) =
      envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ X k s)
        (largeTupleOtherSupport ξ X k s) (largeTupleSelectedCoefficient ξ X k s)
        (largeTupleOtherCoefficient ξ X k s) primeProductEnvelope H T X := by
  unfold tailPrimeTupleRegrouped envelopeCutoffBilinearTail
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  simp only [productGaussHeightWindowKernel,theta_zero,one_mul]
  ring

end CubicFirstMoment

end

end OAI
