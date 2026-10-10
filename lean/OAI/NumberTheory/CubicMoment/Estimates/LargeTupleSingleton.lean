import OAI.NumberTheory.CubicMoment.Estimates.UniquePrimeSupport
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleKernelIntegral
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleRestrictedWeights
import OAI.NumberTheory.CubicMoment.Estimates.CenteredProductSymmetry

namespace OAI

/-! Exact identification of a singleton coordinate of the actual large
tuple with the one-prime coefficient. The other coordinates and the
smooth total-product weight are retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma largeTupleSmoothedPolynomial_singleton {i j : ℕ}
    (a : Fin i ⊕ Fin j) (ℓ : ℤ) (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (u : ℝ) :
    largeTupleSmoothedPolynomial ℓ ξ X k {a} u =
      centeredProductSmoothed (largeTupleOtherSupport ξ X k {a})
        (fullSquarefreePrimeSupport 2
          (fun _ : Unit => largeTupleCoordinateWeight ξ X k a)
          (fun _ => largeTupleNormScale k a) 1)
        (largeTupleOtherCoefficient ξ X k {a})
        (fullPrimeCoefficient 2 (fun _ : Unit => largeTupleCoordinateWeight ξ X k a)
          (fun _ => largeTupleNormScale k a)) ℓ primeProductEnvelope X u := by
  let : Unique ({a} : Finset (Fin i ⊕ Fin j)) :=
    { default := ⟨a,by simp⟩
      uniq := fun b => Subtype.ext (Finset.mem_singleton.mp b.property) }
  have hs : largeTupleSelectedSupport ξ X k {a} =
      fullSquarefreePrimeSupport 2
        (fun _ : Unit => largeTupleCoordinateWeight ξ X k a)
        (fun _ => largeTupleNormScale k a) 1 := by
    rw [largeTupleSelectedSupport,fullSquarefreePrimeSupport_unique,
      fullSquarefreePrimeSupport_unit]
    rfl
  have hc (p : Eisenstein) (hp : p ∈ largeTupleSelectedSupport ξ X k {a}) :
      largeTupleSelectedCoefficient ξ X k {a} p =
        fullPrimeCoefficient 2 (fun _ : Unit => largeTupleCoordinateWeight ξ X k a)
          (fun _ => largeTupleNormScale k a) p := by
    have hp' : p ∈ fullPrimeSupport 2
        (fun _ : Unit => largeTupleCoordinateWeight ξ X k a)
        (fun _ => largeTupleNormScale k a) () := by
      rw [hs,fullSquarefreePrimeSupport_unit] at hp
      exact hp
    rw [largeTupleSelectedCoefficient,fullPrimeCoefficient_unique (by exact hp'),
      fullPrimeCoefficient_unit hp']
    rfl
  unfold largeTupleSmoothedPolynomial
  rw [centeredProductSmoothed_swap]
  unfold centeredProductSmoothed
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr hs
  intro p hp
  rw [hc p (hs.symm ▸ hp)]

lemma triple_other_card {i j : ℕ} (hij : i+j = 3) (a : Fin i ⊕ Fin j) :
    Fintype.card {b : Fin i ⊕ Fin j // b ∉ ({a} : Finset _)} = 2 := by
  rw [Fintype.card_subtype_compl]
  simp [hij]

end CubicFirstMoment

end

end OAI
