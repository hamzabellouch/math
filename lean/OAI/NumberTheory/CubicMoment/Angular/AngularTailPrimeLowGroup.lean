import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeTailLowProduct
import OAI.NumberTheory.CubicMoment.Angular.AngularTailPrimeHeckeGroup

namespace OAI

/-! The logarithmic-height localization tail specialized to the actual
prime groups, retaining all coordinates and the product envelope. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_tailPrime_low_group {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
    (hHuxley : HuxleyAdditiveLargeSieve)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hpnt : PrimaryPrimePNT) (k a : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (z : largeTupleBoxIndex i j) (H T : ℝ),
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      (65536:ℝ)^2 ≤ B → 4*(2*(2:ℝ)^s.card*B)^(3/2:ℝ) ≤ A →
      (2:ℝ)^(Fintype.card {x : Fin i ⊕ Fin j // x ∉ s})*A ≤
        B^2*(1+Real.log B)^(3*a) → A ≤ B^3 →
      (1+Real.log (2*(2:ℝ)^s.card*B))^Ct ≤ T →
      1 ≤ H → H ≤ B^3 →
      ‖envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
        (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
        (fun b => theta ℓ b*largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s b)
        (fun a => theta ℓ a*largeTupleOtherCoefficient ξ z.1.1 z.1.2 s a)
        primeProductEnvelope H T z.1.1‖ ≤
          K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  obtain ⟨K,Ct,hK,hbound⟩ := angular_low_full_prime_envelope_tail ℓ
    (ι := s) (κ := {x : Fin i ⊕ Fin j // x ∉ s})
    hMV hC hHuxley hpnt (by norm_num : (1:ℝ) ≤ 2) k a
    primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth
  refine ⟨K,Ct,hK,?_⟩
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
