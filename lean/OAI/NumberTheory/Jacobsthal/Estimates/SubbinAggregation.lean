import OAI.NumberTheory.Jacobsthal.Primes.CanonicalTagPrimePartition
import OAI.NumberTheory.Jacobsthal.Primes.IntervalPrimesDefinition

namespace OAI

namespace Erdos970


namespace ErdosStoppedSubbinAggregation
open ErdosTagSubbins ErdosInversePrimeBin Erdos970Dependency.SiegelWalfisz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem subbin_eq_intervalPrimes {R theta : ℝ} {N i : ℕ}
    (hR : 0 < R) (ht : 0 < theta) (hN : 0 < N) :
    subbin R theta N i = intervalPrimes (left R theta N i) (step R theta N) 1 0 := by
  ext p
  rw [mem_subbin hR ht hN,mem_intervalPrimes,right_eq_left_add]
  simp [Int.ModEq]

theorem primeBin_eq_intervalPrimes {R theta : ℝ} (hR : 0 < R) (ht : 0 < theta) :
    primeBin R theta = intervalPrimes R (theta*R) 1 0 := by
  ext p
  rw [mem_primeBin hR.le ht.le,mem_intervalPrimes]
  have he : (1+theta)*R = R+theta*R := by ring
  simp [he,Int.ModEq]

theorem aggregate_subbin_lower {R theta c V : ℝ} {N : ℕ}
    (hR : 0 < R) (ht : 0 < theta) (hN : 0 < N) (hc : 0 ≤ c) (hV : 0 ≤ V)
    (reward weight : ℕ → ℝ) (localWeight : Fin N → ℝ)
    (hweight : ∀ i : Fin N,∀ p ∈ subbin R theta N i,weight p ≤ localWeight i)
    (hlower : ∀ i : Fin N,
      c*((subbin R theta N i).card : ℝ)*localWeight i*V ≤
        ∑ p ∈ subbin R theta N i,reward p) :
    c*V*(∑ p ∈ primeBin R theta,weight p) ≤ ∑ p ∈ primeBin R theta,reward p := by
  rw [sum_partition hR ht hN weight,sum_partition hR ht hN reward,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  have hsum : (∑ p ∈ subbin R theta N i,weight p) ≤
      ((subbin R theta N i).card : ℝ)*localWeight i := by
    calc
      _ ≤ ∑ _p ∈ subbin R theta N i,localWeight i := Finset.sum_le_sum (hweight i)
      _ = _ := by simp
  calc
    _ ≤ c*V*(((subbin R theta N i).card : ℝ)*localWeight i) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hc hV)
    _ = c*((subbin R theta N i).card : ℝ)*localWeight i*V := by ring
    _ ≤ _ := hlower i

theorem reference_length_le {Y q R p : ℝ} (hY : 0 ≤ Y) (hq : 0 < q)
    (hR : 0 < R) (hp : R ≤ p) : Y/(p*q) ≤ Y/(R*q) :=
  div_le_div_of_nonneg_left hY (mul_pos hR hq) (mul_le_mul_of_nonneg_right hp hq.le)

theorem aggregate_reference_lower {R theta Y q V : ℝ} {N : ℕ}
    (hR : 0 < R) (ht : 0 < theta) (hN : 0 < N)
    (hY : 0 ≤ Y) (hq : 0 < q) (hV : 0 ≤ V) (reward : ℕ → ℝ)
    (hlower : ∀ i : Fin N,
      (39/100 : ℝ)*((subbin R theta N i).card : ℝ)*(Y/(left R theta N i*q))*V ≤
        ∑ p ∈ subbin R theta N i,reward p) :
    (39/100 : ℝ)*V*(∑ p ∈ primeBin R theta,Y/((p : ℝ)*q)) ≤
      ∑ p ∈ primeBin R theta,reward p := by
  apply aggregate_subbin_lower hR ht hN (by norm_num) hV reward
    (fun p => Y/((p : ℝ)*q)) (fun i => Y/(left R theta N i*q)) _ hlower
  intro i p hp
  exact reference_length_le hY hq (left_pos hR ht hN) ((mem_subbin hR ht hN).mp hp).2.1.le

theorem aggregate_interval_reference_lower {R theta Y q V : ℝ} {N : ℕ}
    (hR : 0 < R) (ht : 0 < theta) (hN : 0 < N)
    (hY : 0 ≤ Y) (hq : 0 < q) (hV : 0 ≤ V) (reward : ℕ → ℝ)
    (hlower : ∀ i : Fin N,
      (39/100 : ℝ)*((intervalPrimes (left R theta N i) (step R theta N) 1 0).card : ℝ)*
        (Y/(left R theta N i*q))*V ≤
        ∑ p ∈ intervalPrimes (left R theta N i) (step R theta N) 1 0,reward p) :
    (39/100 : ℝ)*V*(∑ p ∈ intervalPrimes R (theta*R) 1 0,Y/((p : ℝ)*q)) ≤
      ∑ p ∈ intervalPrimes R (theta*R) 1 0,reward p := by
  rw [← primeBin_eq_intervalPrimes hR ht]
  apply aggregate_reference_lower hR ht hN hY hq hV reward
  intro i
  simpa only [subbin_eq_intervalPrimes hR ht hN] using hlower i

end ErdosStoppedSubbinAggregation


end Erdos970

end OAI
