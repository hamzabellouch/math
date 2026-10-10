import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailHeckeMean
import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailWindow
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleRestrictedWeights
import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeTailGeometry

namespace OAI

/-! Specialization of the full-envelope Hecke tail to the literal
independent coordinates supplied by a surviving prime tuple. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma productGaussWindow_swap (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) (H T X : ℝ) :
    productGaussWindow P S α β ℓ W H T X = productGaussWindow S P β α ℓ W H T X := by
  unfold productGaussWindow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm b a]
  ring

theorem tailPrime_hecke_window {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (k : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (z : largeTupleBoxIndex i j) (H T : ℝ),
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      B₀ ≤ B → (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
      B^(1-η/16) ≤ A → A ≤ B^2/(1+Real.log B)^G →
      (1+Real.log B)^m ≤ T → 0 < H → T ≤ B^(7/20:ℝ) →
      ‖productGaussWindow (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
        (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
        (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
        (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s)
        0 primeProductEnvelope H T z.1.1‖ ≤
          K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  obtain ⟨η,G,K,B₀,m,hη,hηone,hK,hbound⟩ := full_prime_product_smoothed_height
    hpub hHuxley hperiod hMV hC (by positivity : (0:ℝ) < ξ/2)
    (by linarith : ξ/2 ≤ 1) (by norm_num : (1:ℝ) ≤ 2) hGI hGQ
    (largeTupleRestrictedLength (fun a => a ∉ s)) (largeTupleGroupLength s)
    (largeTupleRestrictedWeight (fun a => a ∉ s) ξ) (largeTupleGroupWeight ξ s)
    (largeTupleRestrictedLength_one (fun a => a ∉ s)) (largeTupleGroupLength_one s)
    (largeTupleRestrictedLogWeights (fun a => a ∉ s) ξ) (largeTupleGroupLogWeights ξ s)
    (fun z a _x hx => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_low ξ z.1.1 z.1.2 a hx)
    (fun z a _x hx => largeTupleCoordinateWeight_high ξ z.1.1 z.1.2 a hx)
    (fun z a x => largeTupleCoordinateWeight_norm ξ z.1.1 z.1.2 a x)
    (fun z a x => largeTupleCoordinateWeight_norm ξ z.1.1 z.1.2 a x)
    primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth k
  refine ⟨η,G,2*K,B₀,m,hη,hηone,by positivity,?_⟩
  intro z H T
  dsimp only
  intro hB hrough hAlow hAhigh hT hH hTtop
  have hb := hbound z
    (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleNormScale z.1.2 a)
    (fun a : s => largeTupleNormScale z.1.2 a) z.1.1 T
  simp only [largeTupleRestrictedLength_notMem] at hb
  have hh := hb hB (largeTupleRestrictedLength_notMem s z)
    (Finset.prod_coe_sort s (fun a => largeTupleNormScale z.1.2 a))
    (fun a => z.property a) hrough
    ((Real.rpow_le_rpow_of_exponent_le (largeTupleGroupLength_one s z)
      (by linarith : 1-η/4 ≤ 1-η/16)).trans hAlow)
    hAhigh z.1.1.property hT hTtop
  have hTp : 0 < T := (pow_pos (by
    linarith [Real.log_nonneg (largeTupleGroupLength_one s z)] :
      0 < 1+Real.log (largeTupleGroupLength s z)) m).trans_le hT
  rw [productGaussWindow_swap]
  apply (productGaussWindow_bound _ _ _ _ 0 primeProductEnvelope hH hTp z.1.1).trans
  exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
