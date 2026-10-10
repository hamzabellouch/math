import OAI.NumberTheory.Ostmann.QuadraticCenter.LiftProductCount
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericProductLift
import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessEvent

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

def quadraticWitnessProducts (P : Finset ℕ) (k L : ℕ) [NeZero L]
    (A : ∀ p : ℕ, Finset (ZMod p)) (X K : ℝ) (t : ℕ → ℤ) : Finset ℕ := by
  classical
  exact (primeProductSamples P k).filter (primeProductWitness L A X K t)

theorem eventually_witness_products_fixed_lift_moment :
    ∀ᶠ T : ℝ in atTop, ∀ Z z L : ℕ, ∀ [NeZero L],
      2 ≤ Z → T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      Squarefree L → (L:ℝ) ≤ (Z:ℝ)^(1/50:ℝ) →
      ∀ (A : ∀ p : ℕ,Finset (ZMod p)) (P : Finset ℕ) (k : ℕ),
      (∀ p ∈ P,Nat.Prime p) → ∀ X : ℝ,0 < X →
      (∀ q ∈ primeProductSamples P k,
        (Z:ℝ)^10 ≤ (q:ℝ)/X ∧ (q:ℝ)/X ≤ (Z:ℝ)^13) →
      ∀ t : ℕ → ℤ, ∃ a : ℕ,1 ≤ a ∧ a ≤ quadraticLiftMultiplierBound Z ∧
        k.factorial*(quadraticWitnessProducts P k L A X (auxiliaryK Z z) t).card ≤
          quadraticLiftMultiplierBound Z *
            ∑ n ∈ Finset.Icc (-(quadraticLiftHeight X Z:ℤ)) (quadraticLiftHeight X Z),
              (matchingPrimes P a n t).card.descFactorial k := by
  classical
  filter_upwards [eventually_divisor_quadratic_bounded_lift] with T hT
  intro Z z L _ hZ hZl hZu hz hzl hzu hL hLZ A P k hP X hX hscale t
  have hZp : (0:ℝ)<Z := by exact_mod_cast (show 0<Z by omega)
  have hAcap : 0 < quadraticLiftMultiplierBound Z := by
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hZp _)
  apply exists_fixed_multiplier_lift_moment hP
    (Finset.filter_subset _ _) (quadraticLiftMultiplierBound Z) (quadraticLiftHeight X Z) hAcap t
  intro q hq
  obtain ⟨hqs,hevent⟩ := Finset.mem_filter.mp hq
  obtain ⟨s,hs,d,hd,v,hv,hlarge⟩ := hevent
  have hsI := Finset.mem_Ico.mp (Finset.mem_filter.mp hs).1
  have hqpos : 0 < q := (primeProductSamples_primeFactors hP hqs).1.ne_zero.bot_lt
  have hr := hscale q hqs
  exact hT Z z L hZ hZl hZu hz hzl hzu hL (Nat.pos_of_neZero L) hLZ A
    (adaptiveInverse q) s v d q hsI.1 hsI.2.le hv hd hqpos X hX hr.1 hr.2
    (centerCorrection q L (primeProductCenter q t)) t hlarge

end Ostmann.QuadraticCenter

end

end OAI
