import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailHighProduct
import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeHeckeGroup

namespace OAI

/-! The power-width tail specialized to every actual prime group. The
positive width exponent is chosen before the arities and the group. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem tailPrime_high_group_uniform
    (hHuxley : HuxleyAdditiveLargeSieve)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (i j : ℕ) (s : Finset (Fin i ⊕ Fin j)) (ξ : ℝ) (k : ℕ),
      ∃ K B₀ : ℝ, 0 < K ∧
      ∀ (z : largeTupleBoxIndex i j) (H T : ℝ),
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      B₀ ≤ B → 4*(2*(2:ℝ)^s.card*B)^(3/2:ℝ) ≤ A →
      (2:ℝ)^(Fintype.card {x : Fin i ⊕ Fin j // x ∉ s})*A ≤
        B^(2+γ) → A ≤ B^3 →
      (2*(2:ℝ)^s.card*B)^(1/50:ℝ) ≤ T →
      1 ≤ H → H ≤ B^3 →
      ‖envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
        (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
        (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
        (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s)
        primeProductEnvelope H T z.1.1‖ ≤
          K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  obtain ⟨γ,hγ,huniform⟩ := high_full_prime_envelope_tail_uniform hMV hC hHuxley
  refine ⟨γ,hγ,?_⟩
  intro i j s ξ k
  obtain ⟨K,B₀,hK,hbound⟩ := huniform s {x : Fin i ⊕ Fin j // x ∉ s}
    2 (by norm_num) k primeProductEnvelope primeProductEnvelope_compact
    primeProductEnvelope_positive primeProductEnvelope_smooth
  refine ⟨K,B₀,hK,?_⟩
  intro z H T
  dsimp only
  intro hB hAlow hAhigh hA3 hT hH hHcube
  have hb := hbound (largeTupleRestrictedWeight (fun x => x ∉ s) ξ z)
    (largeTupleGroupWeight ξ s z)
    (fun x : {x : Fin i ⊕ Fin j // x ∉ s} => largeTupleNormScale z.1.2 x)
    (fun x : s => largeTupleNormScale z.1.2 x) z.1.1 T H
    (fun x => z.property x) (fun x => z.property x)
    (fun x _y hy => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 x hy)
    (fun x _y hy => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 x hy)
    (fun x _y hy => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 x hy)
    (fun x _y hy => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 x hy)
    (fun x y => largeTupleCoordinateWeight_norm ξ z.1.1 z.1.2 x y)
    (fun x y => largeTupleCoordinateWeight_norm ξ z.1.1 z.1.2 x y)
  have hprodA : (∏ x : {x : Fin i ⊕ Fin j // x ∉ s}, largeTupleNormScale z.1.2 x) =
      largeTupleGroupLength (Finset.univ\s) z := largeTupleRestrictedLength_notMem s z
  have hprodB : (∏ x : s, largeTupleNormScale z.1.2 x) = largeTupleGroupLength s z :=
    Finset.prod_coe_sort s (fun x => largeTupleNormScale z.1.2 x)
  simp only [hprodA,hprodB,Fintype.card_coe] at hb
  have hh := hb hB hAlow hAhigh hA3 z.1.1.property hT hH hHcube
  rw [envelopeCutoffBilinearTail_swap]
  exact hh

end CubicFirstMoment

end

end OAI
