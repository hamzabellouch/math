import OAI.NumberTheory.Jacobsthal.Partitions.IntervalPairCount
import OAI.NumberTheory.Jacobsthal.Primes.PrimeHitRepresentative

namespace OAI

namespace Erdos970

section

namespace ErdosRandomVariance
attribute [local instance] Classical.propDecidable

noncomputable def sieveProduct (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1-(1 : ℝ)/p)
noncomputable def pairKernel (P : Finset ℕ) (i j : ℕ) : ℝ :=
  ∏ p ∈ P, (((1 : ℝ)/p)*congruenceIndicator p i j+(1-2/(p : ℝ)))
noncomputable def pairCoefficient (P S : Finset ℕ) : ℝ :=
  (∏ p ∈ S, (1 : ℝ)/p)*(∏ p ∈ P \ S, (1-2/(p : ℝ)))

theorem prime_indicator_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (i j : ℕ) :
    (∏ p ∈ P, congruenceIndicator p i j) = congruenceIndicator (∏ p ∈ P,p) i j := by
  by_cases h : Nat.ModEq (∏ p ∈ P,p) i j
  · have hh := (ErdosInverseHits.modEq_prime_product_iff P hP i j).mp h
    rw [show congruenceIndicator (∏ p ∈ P,p) i j = 1 by simp [congruenceIndicator,h]]
    apply Finset.prod_eq_one
    intro p hp
    simp [congruenceIndicator,hh p hp]
  · have hn : ¬∀ p ∈ P, Nat.ModEq p i j :=
      fun hh => h ((ErdosInverseHits.modEq_prime_product_iff P hP i j).mpr hh)
    push Not at hn
    obtain ⟨p,hp,hn⟩ := hn
    rw [show congruenceIndicator (∏ p ∈ P,p) i j = 0 by simp [congruenceIndicator,h]]
    apply Finset.prod_eq_zero hp
    simp [congruenceIndicator,hn]

theorem pairCoefficient_nonneg (P S : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) :
    0 ≤ pairCoefficient P S := by
  unfold pairCoefficient
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun p _ => by positivity)
  · apply Finset.prod_nonneg
    intro p hp
    have hh := hP p (Finset.mem_sdiff.mp hp).1
    apply sub_nonneg.mpr
    exact (div_le_one (show (0 : ℝ) < p by exact_mod_cast hh.pos)).mpr (by exact_mod_cast hh.two_le)

theorem pairKernel_expansion (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) (i j : ℕ) :
    pairKernel P i j = ∑ S ∈ P.powerset,
      pairCoefficient P S*congruenceIndicator (∏ p ∈ S,p) i j := by
  rw [pairKernel, Finset.prod_add]
  apply Finset.sum_congr rfl
  intro S hS
  have hpS : ∀ p ∈ S,p.Prime := fun p hp => hP p ((Finset.mem_powerset.mp hS) hp)
  rw [Finset.prod_mul_distrib, prime_indicator_product S hpS]
  unfold pairCoefficient
  ring

theorem pairCoefficient_sum (P : Finset ℕ) :
    (∑ S ∈ P.powerset, pairCoefficient P S) = sieveProduct P := by
  unfold pairCoefficient sieveProduct
  rw [← Finset.prod_add]
  apply Finset.prod_congr rfl
  intro p _
  ring

theorem pairCoefficient_div_product (P S : Finset ℕ) :
    pairCoefficient P S/((∏ p ∈ S,p : ℕ) : ℝ) =
      (∏ p ∈ S, ((1 : ℝ)/p)^2)*(∏ p ∈ P \ S, (1-2/(p : ℝ))) := by
  unfold pairCoefficient
  rw [Nat.cast_prod]
  calc
    _ = ((∏ p ∈ S,(1 : ℝ)/p)/(∏ p ∈ S,(p : ℝ)))*(∏ p ∈ P \ S,(1-2/(p : ℝ))) := by ring
    _ = _ := by
      rw [← Finset.prod_div_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro p _
      ring

theorem pairCoefficient_normalized_sum (P : Finset ℕ) :
    (∑ S ∈ P.powerset, pairCoefficient P S/((∏ p ∈ S,p : ℕ) : ℝ)) = (sieveProduct P)^2 := by
  simp only [pairCoefficient_div_product]
  rw [← Finset.prod_add]
  unfold sieveProduct
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  ring

theorem pairKernel_diagonal (P : Finset ℕ) (i : ℕ) : pairKernel P i i = sieveProduct P := by
  unfold pairKernel sieveProduct
  apply Finset.prod_congr rfl
  intro p _
  simp only [congruenceIndicator, Nat.ModEq.refl, ite_true, mul_one]
  ring

theorem pairKernel_parity_zero (P : Finset ℕ) (h2 : 2 ∈ P) (i j : ℕ)
    (hodd : ¬Nat.ModEq 2 i j) : pairKernel P i j = 0 := by
  unfold pairKernel
  apply Finset.prod_eq_zero h2
  norm_num [congruenceIndicator,hodd]

theorem pairKernel_interval_sum (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) (J : ℕ) :
    (∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, pairKernel P i j) ≤
      ((J : ℝ)*sieveProduct P)^2+(J : ℝ)*sieveProduct P := by
  have hexpand :
      (∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, pairKernel P i j) =
      ∑ S ∈ P.powerset, pairCoefficient P S*
        (∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, congruenceIndicator (∏ p ∈ S,p) i j) := by
    simp only [pairKernel_expansion P hP]
    have hs (i : ℕ) :
        (∑ j ∈ Finset.range J, ∑ S ∈ P.powerset,
          pairCoefficient P S*congruenceIndicator (∏ p ∈ S,p) i j) =
        ∑ S ∈ P.powerset, ∑ j ∈ Finset.range J,
          pairCoefficient P S*congruenceIndicator (∏ p ∈ S,p) i j := Finset.sum_comm
    simp only [hs]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [hexpand]
  calc
    _ ≤ ∑ S ∈ P.powerset, pairCoefficient P S*((J : ℝ)^2/((∏ p ∈ S,p : ℕ) : ℝ)+J) := by
      apply Finset.sum_le_sum
      intro S hS
      have hprod : 0 < ∏ p ∈ S,p := Finset.prod_pos
        (fun p hp => (hP p ((Finset.mem_powerset.mp hS) hp)).pos)
      exact mul_le_mul_of_nonneg_left (interval_pair_congruence_bound J _ hprod) (pairCoefficient_nonneg P S hP)
    _ = (J : ℝ)^2*(∑ S ∈ P.powerset,pairCoefficient P S/((∏ p ∈ S,p : ℕ) : ℝ))+
        (J : ℝ)*(∑ S ∈ P.powerset,pairCoefficient P S) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = _ := by rw [pairCoefficient_normalized_sum,pairCoefficient_sum]; ring

end ErdosRandomVariance

end

end Erdos970

end OAI
