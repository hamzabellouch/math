import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailProductEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeHeckeGroup

namespace OAI

/-! The enlarged-conductor height estimate on the original grouped prime
coordinates, with the full product envelope and every Mellin shift retained. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem tailPrime_middle_group {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
    (hHuxley : HuxleyAdditiveLargeSieve)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (k : ℕ) :
    ∃ K B₀ : ℝ, 0 < K ∧
      ∀ (z : largeTupleBoxIndex i j) (H T : ℝ),
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      B₀ ≤ B → (2*(2:ℝ)^s.card*B)^(27/25:ℝ) ≤ A →
      A ≤ B^(19/10:ℝ) → (2*(2:ℝ)^s.card*B)^(1/50:ℝ) ≤ T →
      1 ≤ H → H ≤ B^3 →
      ‖envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
        (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
        (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
        (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s)
        primeProductEnvelope H T z.1.1‖ ≤
          K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  obtain ⟨K,B₀,hK,hbound⟩ := primeGroupTail_full_prime_envelope_tail
    hHuxley hMV hC (by norm_num : (1:ℝ) ≤ 2)
    (largeTupleRestrictedLength (fun a => a ∉ s)) (largeTupleGroupLength s)
    (largeTupleRestrictedWeight (fun a => a ∉ s) ξ) (largeTupleGroupWeight ξ s)
    (largeTupleRestrictedLength_one (fun a => a ∉ s)) (largeTupleGroupLength_one s)
    (largeTupleRestrictedLogWeights (fun a => a ∉ s) ξ) (largeTupleGroupLogWeights ξ s)
    (fun z a _x hx => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 a hx) k
    primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth
  refine ⟨K,B₀,hK,?_⟩
  intro z H T
  dsimp only
  intro hB hAlow hAhigh hT hH hHcube
  have hb := hbound z
    (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleNormScale z.1.2 a)
    (fun a : s => largeTupleNormScale z.1.2 a) 1 1 H T z.1.1
  simp only [largeTupleRestrictedLength_notMem,Fintype.card_coe] at hb
  have hh := hb hB (largeTupleRestrictedLength_notMem s z)
    (Finset.prod_coe_sort s (fun a => largeTupleNormScale z.1.2 a))
    (fun a => z.property a) (fun a => z.property a)
    hAlow hAhigh hT hH hHcube z.1.1.property
  rw [envelopeCutoffBilinearTail_swap]
  exact hh

end CubicFirstMoment

end

end OAI
