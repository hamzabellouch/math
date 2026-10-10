import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCharacterRows
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedFilteredCore
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedMellinRows
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSmallDivisorMass
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorScale
import OAI.NumberTheory.CubicMoment.Estimates.PrimeSubsetNormTail

namespace OAI

/-! Sum the hybrid core bound over actual short divisor rows. The rough
lower cutoff is used only in the elementary small-core term; the two
hybrid terms are summed by convergent norm series. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_small_divisor_mass (ℓ : ℤ) (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X w z l b u M V B R : ℝ)
      (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
      (e : Eisenstein) (U : Finset Eisenstein) (A : Finset (Finset Eisenstein))
      (H : Finset Eisenstein),
      0 < b → 0 < V → 0 ≤ B → 0 < R → (∀ p ∈ U, primaryPrime p) →
      A ⊆ U.powerset →
      (∀ s ∈ A, R < norm (∏ p ∈ s,p) ∧ 65536 ≤ b/norm (∏ p ∈ s,p) ∧
        8*B ≤ (b/norm (∏ p ∈ s,p))^(3/4:ℝ)) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖angularStoppedRowCoefficient ℓ X w z u W selected n‖ ≤ M) →
      (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      (∑ s ∈ A, ∑ v ∈ H,
        ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => (∏ p ∈ s,p) ∣ n),
          angularStoppedRowCoefficient ℓ X w z u W selected n*cubicSymbol n v‖^2) ≤
      104976*V*B^(1/3:ℝ)*b^2*M^2*R^(-(1/2:ℝ))*
        (∑' n : Eisenstein, norm n^(-(3/2:ℝ)))+
      K*((largeCoreDyadicIndices V B).card:ℝ)*B^(1/3:ℝ)*M^2*(
        b^2*(V/5832)^(-(1/4:ℝ))*(∑' n : Eisenstein, norm n^(-2:ℝ))+
        b^(2-1/20000:ℝ)*(∑' n : Eisenstein, norm n^(-(2-1/20000:ℝ)))) := by
  obtain ⟨K,hK,hbound⟩ := angular_stopped_filtered_core_blocks ℓ (ι := ι) hHuxley
  refine ⟨K,hK,?_⟩
  intro X w z l b u M V B R W selected e U A H hb hV hB hR hU hA hrows hcoeff hH
  let L := 104976*V*B^(1/3:ℝ)*b^2*M^2
  let P := K*((largeCoreDyadicIndices V B).card:ℝ)*B^(1/3:ℝ)*M^2
  let E := (V/5832)^(-(1/4:ℝ))
  let f := fun s : Finset Eisenstein =>
    L*norm (∏ p ∈ s,p)^(-2:ℝ)+P*(b^2*E*norm (∏ p ∈ s,p)^(-2:ℝ)+
      b^(2-1/20000:ℝ)*norm (∏ p ∈ s,p)^(-(2-1/20000:ℝ)))
  have hrow (s : Finset Eisenstein) (hs : s ∈ A) :
      (∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
        (fun n => (∏ p ∈ s,p) ∣ n),
        angularStoppedRowCoefficient ℓ X w z u W selected n*cubicSymbol n v‖^2) ≤ f s := by
    have hsp := primary_finset_prod s (fun p => p)
      (fun p hp => (hU p (Finset.mem_powerset.mp (hA hs) hp)).1)
    have hq := norm_pos_of_ne_zero (primary_ne_zero hsp)
    have hm := hbound X w z l b u M V B W selected e (∏ p ∈ s,p)
      hsp hb.le hV hB (hrows s hs).2.1 (hrows s hs).2.2 hcoeff H hH
    have hsquare : (b/norm (∏ p ∈ s,p))^2 =
        b^2*norm (∏ p ∈ s,p)^(-2:ℝ) := by
      rw [Real.rpow_neg hq.le,Real.rpow_two,div_pow,div_eq_mul_inv]
    have hpower := quotient_power_times_self hb hq (1-1/20000:ℝ)
    rw [show (1-1/20000:ℝ)+1 = 2-1/20000 by ring] at hpower
    apply hm.trans_eq
    dsimp [f,L,P,E]
    rw [hsquare]
    calc
      _ = 104976*V*B^(1/3:ℝ)*(b^2*norm (∏ p ∈ s,p)^(-2:ℝ))*M^2+
          K*((largeCoreDyadicIndices V B).card:ℝ)*B^(1/3:ℝ)*M^2*
          ((b/norm (∏ p ∈ s,p))^2*(V/5832)^(-(1/4:ℝ))+
            (b/norm (∏ p ∈ s,p))^(1-1/20000:ℝ)*(b/norm (∏ p ∈ s,p))) := by ring
      _ = _ := by rw [hsquare,hpower]; ring
  have hsmall : (∑ s ∈ A, norm (∏ p ∈ s,p)^(-2:ℝ)) ≤
      R^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ))) := by
    apply le_trans _ (primary_prime_subset_norm_tail U hU hR)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      exact Finset.mem_filter.mpr ⟨hA hs,(hrows s hs).1⟩
    · intro s _ _
      exact Real.rpow_nonneg (norm_nonneg _) _
  have htwo : (∑ s ∈ A, norm (∏ p ∈ s,p)^(-2:ℝ)) ≤
      ∑' n : Eisenstein, norm n^(-2:ℝ) :=
    primary_prime_subset_norm_sum (s := 2) U hU A hA (by norm_num)
  have hpower : (∑ s ∈ A, norm (∏ p ∈ s,p)^(-(2-1/20000:ℝ))) ≤
      ∑' n : Eisenstein, norm n^(-(2-1/20000:ℝ)) :=
    primary_prime_subset_norm_sum (s := 2-1/20000) U hU A hA (by norm_num)
  calc
    _ ≤ ∑ s ∈ A, f s := Finset.sum_le_sum hrow
    _ = L*(∑ s ∈ A, norm (∏ p ∈ s,p)^(-2:ℝ))+
        P*(b^2*E*(∑ s ∈ A, norm (∏ p ∈ s,p)^(-2:ℝ))+
          b^(2-1/20000:ℝ)*(∑ s ∈ A, norm (∏ p ∈ s,p)^(-(2-1/20000:ℝ)))) := by
      dsimp [f]
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]
    _ ≤ L*(R^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ))))+
        P*(b^2*E*(∑' n : Eisenstein, norm n^(-2:ℝ))+
          b^(2-1/20000:ℝ)*(∑' n : Eisenstein, norm n^(-(2-1/20000:ℝ)))) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hsmall (by dsimp [L]; positivity))
        (mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left htwo (by dsimp [E]; positivity))
          (mul_le_mul_of_nonneg_left hpower (by positivity))) (by dsimp [P]; positivity))
    _ = _ := by dsimp [L,P,E]; ring

end CubicFirstMoment

end

end OAI
