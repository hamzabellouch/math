import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeMoment

namespace OAI

/-! The classical mean-value recurrence from a finite supply of primes.
All analytic prime-supply requirements appear as elementary bounds on P. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_distinct_moment_total {s k m N ℓ : ℕ} (hs : 0<s) (hk : 2≤k)
    (hm : m=s+k) (L : Fin ℓ → Fin m) (hL : Function.Injective L)
    (hN : (4*(ℓ:ℝ)^2)^2<(N:ℝ)) :
    halaszVinogradovCount m k N ≤
      2*halaszFiberEnergy (halaszGoodLongTuples (N := N) L) (halaszVinogradovFrequency k) := by
  obtain ⟨n,hn⟩ : ∃ n, m=n+2 := ⟨m-2,by omega⟩
  have hnk : n+2=s+k := hn.symm.trans hm
  clear hm
  subst m
  exact halasz_distinct_moment hs hk hnk L hL hN

theorem halasz_vinogradov_prime_sum {s k N R : ℕ} (hs : 0<s) (hk : 2≤k)
    (hsize : (4*(k:ℝ)^2)^2<(N:ℝ)) (hkR : k<R) (hNR : N<R^k)
    (P : Finset ℕ) (hP : ∀ p∈P, p.Prime ∧ R≤p)
    (hcard : 2*(k^2*k)<P.card) :
    halaszVinogradovCount (k+s) k N ≤
      2*∑ p∈P, p^(2*s)*((k^k*p^(k*(k-1)/2))*
        (N^k*halaszVinogradovCount s k (N/p+1))) := by
  let L : Fin k → Fin (k+s) := fun i => i.castAdd s
  have hL : Function.Injective L := Fin.castAdd_injective k s
  have hD := halasz_distinct_moment_total hs hk (Nat.add_comm k s) L hL hsize
  have hC := halasz_distinct_energy_prime_cover (k := k) (N := N)
    (by omega : 0<R) hNR.le P hP hcard L
  apply hD.trans
  apply Nat.mul_le_mul_left 2
  apply hC.trans
  apply sum_le_sum
  intro p hp
  have : Fact p.Prime := ⟨(hP p hp).1⟩
  have hNp : N<p^k := hNR.trans_le (Nat.pow_le_pow_left (hP p hp).2 k)
  exact halasz_residue_good_moment hs (by omega) (lt_of_lt_of_le hkR (hP p hp).2) hNp

end TwoPointCorrelations

end OAI
