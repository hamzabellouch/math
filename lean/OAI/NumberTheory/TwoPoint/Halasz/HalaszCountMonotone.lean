import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeRecurrence

namespace OAI

/-! Monotonicity in the summation endpoint, needed to give the short
moment one common endpoint after summing over the selected primes. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem halasz_vinogradov_count_mono (s k : ℕ) {N M : ℕ} (hNM : N≤M) :
    halaszVinogradovCount s k N≤halaszVinogradovCount s k M := by
  let e : (Fin s → Fin N) → (Fin s → Fin M) := fun x i => (x i).castLE hNM
  have he : Function.Injective e := by
    intro x y h
    funext i
    exact Fin.castLE_injective hNM (congrFun h i)
  have hf (x : Fin s → Fin N) :
      halaszNatPowerFrequency k (e x)=halaszNatPowerFrequency k x := rfl
  have hm := halasz_fiber_energy_mono
    (subset_univ ((univ : Finset (Fin s → Fin N)).image e)) (halaszNatPowerFrequency k)
  rw [halasz_nat_power_energy] at hm
  have ht := halasz_fiber_energy_transfer (univ : Finset (Fin s → Fin N)) e he.injOn
    (halaszNatPowerFrequency k) (halaszNatPowerFrequency k) (fun x _ => hf x)
  rw [halasz_nat_power_energy] at ht
  apply ht.trans_le
  convert hm using 1
  congr 1
  ext x
  simp only [mem_image]

theorem halasz_vinogradov_prime_recurrence {s k N R B : ℕ} (hs : 0<s) (hk : 2≤k)
    (hsize : (4*(k:ℝ)^2)^2<(N:ℝ)) (hkR : k<R) (hNR : N<R^k)
    (P : Finset ℕ) (hP : ∀ p∈P, p.Prime ∧ R≤p ∧ p≤B)
    (hcard : 2*(k^2*k)<P.card) :
    halaszVinogradovCount (k+s) k N ≤
      2*P.card*(B^(2*s)*((k^k*B^(k*(k-1)/2))*
        (N^k*halaszVinogradovCount s k (N/R+1)))) := by
  have h := halasz_vinogradov_prime_sum hs hk hsize hkR hNR P
    (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1⟩) hcard
  have hb : ∀ p∈P, p^(2*s)*((k^k*p^(k*(k-1)/2))*
      (N^k*halaszVinogradovCount s k (N/p+1))) ≤
      B^(2*s)*((k^k*B^(k*(k-1)/2))*(N^k*halaszVinogradovCount s k (N/R+1))) := by
    intro p hp
    have hpB := (hP p hp).2.2
    have hdiv : N/p+1≤N/R+1 := Nat.add_le_add_right
      (Nat.div_le_div_left (hP p hp).2.1 (by omega : 0<R)) 1
    have hcount := halasz_vinogradov_count_mono s k hdiv
    gcongr
  apply h.trans
  have hsum := sum_le_sum hb
  simp only [sum_const,nsmul_eq_mul] at hsum
  calc
    _ ≤ 2*(P.card*(B^(2*s)*((k^k*B^(k*(k-1)/2))*
      (N^k*halaszVinogradovCount s k (N/R+1))))) := Nat.mul_le_mul_left 2 hsum
    _ = _ := by ring

end TwoPointCorrelations

end OAI
