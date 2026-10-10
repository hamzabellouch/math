import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import OAI.NumberTheory.Jacobsthal.Partitions.DilationCoordinates
import OAI.NumberTheory.Jacobsthal.Primes.PrimePowerBound
import OAI.NumberTheory.Jacobsthal.Sieve.KloostermanCRT
import OAI.NumberTheory.Jacobsthal.Sieve.ResidueGCDBounds

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman

def frequencyGcd (N : ℕ) (h k : ℤ) : ℕ := Nat.gcd N (Int.gcd h k)

theorem dvd_frequencyGcd_iff (d N : ℕ) (h k : ℤ) :
    d ∣ frequencyGcd N h k ↔ d ∣ N ∧ (d : ℤ) ∣ h ∧ (d : ℤ) ∣ k := by
  simp only [frequencyGcd, Int.gcd_def, Nat.dvd_gcd_iff, Int.natCast_dvd]

theorem frequencyGcd_scale (N : ℕ) (c A B h k : ℤ)
    (hab : (N : ℤ)*A + c*B = 1) :
    frequencyGcd N (c*h) (c*k) = frequencyGcd N h k := by
  apply Nat.dvd_antisymm
  · obtain ⟨hdN, hdh, hdk⟩ := (dvd_frequencyGcd_iff _ _ _ _).mp
      (dvd_refl (frequencyGcd N (c*h) (c*k)))
    have hdN' : (frequencyGcd N (c*h) (c*k) : ℤ) ∣ N := by exact_mod_cast hdN
    apply (dvd_frequencyGcd_iff _ _ _ _).mpr
    refine ⟨hdN, ?_, ?_⟩
    · have hd := dvd_add (dvd_mul_of_dvd_left hdN' (A*h)) (dvd_mul_of_dvd_right hdh B)
      have heq : (N : ℤ)*(A*h) + B*(c*h) = h := by
        linear_combination h * hab
      rwa [heq] at hd
    · have hd := dvd_add (dvd_mul_of_dvd_left hdN' (A*k)) (dvd_mul_of_dvd_right hdk B)
      have heq : (N : ℤ)*(A*k) + B*(c*k) = k := by
        linear_combination k * hab
      rwa [heq] at hd
  · obtain ⟨hdN, hdh, hdk⟩ := (dvd_frequencyGcd_iff _ _ _ _).mp
      (dvd_refl (frequencyGcd N h k))
    exact (dvd_frequencyGcd_iff _ _ _ _).mpr
      ⟨hdN, dvd_mul_of_dvd_right hdh c, dvd_mul_of_dvd_right hdk c⟩

theorem frequencyGcd_coprime_mul (m n : ℕ) (hmn : m.Coprime n) (h k : ℤ) :
    frequencyGcd (m*n) h k = frequencyGcd m h k * frequencyGcd n h k := by
  apply Nat.dvd_antisymm
  · have hg : frequencyGcd (m*n) h k ∣ m*n := Nat.gcd_dvd_left _ _
    have heq := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hmn).mpr hg
    have hd : Nat.gcd (frequencyGcd (m*n) h k) m ∣ frequencyGcd m h k := by
      apply Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
      exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have he : Nat.gcd (frequencyGcd (m*n) h k) n ∣ frequencyGcd n h k := by
      apply Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
      exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    rw [← heq]
    exact Nat.mul_dvd_mul hd he
  · have hd : frequencyGcd m h k ∣ frequencyGcd (m*n) h k := by
      apply Nat.dvd_gcd
      · exact (Nat.gcd_dvd_left _ _).trans (dvd_mul_right m n)
      · exact Nat.gcd_dvd_right _ _
    have he : frequencyGcd n h k ∣ frequencyGcd (m*n) h k := by
      apply Nat.dvd_gcd
      · exact (Nat.gcd_dvd_left _ _).trans (dvd_mul_left n m)
      · exact Nat.gcd_dvd_right _ _
    exact (hmn.of_dvd (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)).mul_dvd_of_dvd_of_dvd hd he

end ErdosKloosterman

end

section

namespace ErdosKloosterman

noncomputable def envelope (N : ℕ) (h k : ℤ) : ℝ :=
  (N.divisors.card : ℝ)^2 * (N : ℝ)^((3 : ℝ)/4) *
    (frequencyGcd N h k : ℝ)^((1 : ℝ)/4)

theorem envelope_nonneg (N : ℕ) (h k : ℤ) : 0 ≤ envelope N h k := by
  unfold envelope
  positivity

theorem envelope_coprime_mul (m n : ℕ) (hmn : m.Coprime n) (h k : ℤ) :
    envelope (m*n) h k = envelope m h k * envelope n h k := by
  unfold envelope
  rw [hmn.card_divisors_mul, frequencyGcd_coprime_mul m n hmn]
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n),
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

theorem envelope_scale (N : ℕ) (c A B h k : ℤ)
    (hab : (N : ℤ)*A + c*B = 1) :
    envelope N (c*h) (c*k) = envelope N h k := by
  unfold envelope
  rw [frequencyGcd_scale N c A B h k hab]

theorem envelope_crt_scaled (m n : ℕ) (hmn : m.Coprime n) (h k : ℤ) :
    envelope m (Nat.gcdB m n*h) (Nat.gcdB m n*k) *
      envelope n (Nat.gcdA m n*h) (Nat.gcdA m n*k) = envelope (m*n) h k := by
  have hab : (m : ℤ)*Nat.gcdA m n + (n : ℤ)*Nat.gcdB m n = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hmn.gcd_eq_one]
    rfl
  rw [envelope_scale m (Nat.gcdB m n) (Nat.gcdA m n) n h k (by nlinarith [hab]),
      envelope_scale n (Nat.gcdA m n) (Nat.gcdB m n) m h k (by nlinarith [hab]),
      envelope_coprime_mul m n hmn]

theorem standardSum_one (h k : ℤ) : standardSum 1 h k = 1 := by
  let : DecidableEq (ZMod 1) := Classical.decEq _
  have h0 : (h : ZMod 1) = 0 := Subsingleton.elim _ _
  have k0 : (k : ZMod 1) = 0 := Subsingleton.elim _ _
  have hc : Fintype.card (ZMod 1)ˣ = 1 := Fintype.card_unique
  simp only [standardSum, h0, k0, sum_zero_zero, hc, Nat.cast_one]

theorem envelope_one (h k : ℤ) : envelope 1 h k = 1 := by
  simp [envelope, frequencyGcd]

def BoundAt (N : ℕ) : Prop := ∀ [NeZero N] (h k : ℤ),
  ‖standardSum N h k‖ ≤ envelope N h k

theorem boundAt_zero : BoundAt 0 := by
  intro h0 h k
  exact False.elim (NeZero.ne 0 rfl)

theorem boundAt_one : BoundAt 1 := by
  intro _ h k
  simp [standardSum_one, envelope_one]

theorem boundAt_coprime (m n : ℕ) (hm : 1 < m) (hn : 1 < n) (hmn : m.Coprime n)
    (hbm : BoundAt m) (hbn : BoundAt n) : BoundAt (m*n) := by
  let : NeZero m := ⟨by omega⟩
  let : NeZero n := ⟨by omega⟩
  intro _ h k
  rw [norm_standardSum_crt m n hmn]
  calc
    _ ≤ envelope m (Nat.gcdB m n*h) (Nat.gcdB m n*k) *
        envelope n (Nat.gcdA m n*h) (Nat.gcdA m n*k) :=
      mul_le_mul (hbm _ _) (hbn _ _) (norm_nonneg _) (envelope_nonneg _ _ _)
    _ = _ := envelope_crt_scaled m n hmn h k

theorem boundAt_all_of_prime_powers
    (local_bound : ∀ p a : ℕ, p.Prime → 0 < a → BoundAt (p^a)) :
    ∀ N : ℕ, BoundAt N :=
  Nat.recOnPosPrimePosCoprime local_bound boundAt_zero boundAt_one boundAt_coprime

end ErdosKloosterman

end

section

open scoped BigOperators
namespace ErdosHyperbolaIdentities

attribute [local instance] Classical.decEq

private theorem restricted_phase (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c u : (ZMod (H*T))ˣ) (h k : ZMod (H*T)) (j : ZMod T) :
    ZMod.stdAddChar (-j*(a : ZMod T)) *
      ZMod.stdAddChar ((h+(H : ZMod (H*T))*(j.val : ZMod (H*T)))*(u : ZMod (H*T)) +
        (k*(c : ZMod (H*T)))*(↑u⁻¹ : ZMod (H*T))) =
      ZMod.stdAddChar (h*(u : ZMod (H*T)) + k*(c : ZMod (H*T))*(↑u⁻¹ : ZMod (H*T))) *
        ZMod.stdAddChar (j*((ZMod.unitsMap (dvd_mul_left T H) u : ZMod T)-(a : ZMod T))) := by
  have he : (h+(H : ZMod (H*T))*(j.val : ZMod (H*T)))*(u : ZMod (H*T)) +
      (k*(c : ZMod (H*T)))*(↑u⁻¹ : ZMod (H*T)) =
      (h*(u : ZMod (H*T)) + k*(c : ZMod (H*T))*(↑u⁻¹ : ZMod (H*T))) +
        (H : ZMod (H*T))*((j.val : ZMod (H*T))*(u : ZMod (H*T))) := by ring
  rw [he, AddChar.map_add_eq_mul, ErdosKloosterman.PrimePower.standard_character_reduction]
  have hred : ErdosKloosterman.PrimePower.reduction H T
      ((j.val : ZMod (H*T))*(u : ZMod (H*T))) =
      j*(ZMod.unitsMap (dvd_mul_left T H) u : ZMod T) := by
    simp only [map_mul, map_natCast, ZMod.natCast_zmod_val,
      ErdosKloosterman.PrimePower.reduction, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe]
  rw [hred]
  have hc : ZMod.stdAddChar (-j*(a : ZMod T)) *
      ZMod.stdAddChar (j*(ZMod.unitsMap (dvd_mul_left T H) u : ZMod T)) =
      ZMod.stdAddChar (j*((ZMod.unitsMap (dvd_mul_left T H) u : ZMod T)-(a : ZMod T))) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc
    _ = ZMod.stdAddChar (h*(u : ZMod (H*T)) + k*(c : ZMod (H*T))*(↑u⁻¹ : ZMod (H*T))) *
        (ZMod.stdAddChar (-j*(a : ZMod T)) *
          ZMod.stdAddChar (j*(ZMod.unitsMap (dvd_mul_left T H) u : ZMod T))) := by ring
    _ = _ := by rw [hc]

theorem restricted_average_mul (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (h k : ZMod (H*T)) :
    (∑ j : ZMod T, ZMod.stdAddChar (-j*(a : ZMod T)) *
      ErdosKloosterman.sum ZMod.stdAddChar
        (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))) (k*(c : ZMod (H*T)))) =
      (T : ℂ) * restrictedSum (H*T) T (dvd_mul_left T H) a c h k := by
  unfold ErdosKloosterman.sum
  simp_rw [Finset.mul_sum, restricted_phase]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar T)]
  have he (u : (ZMod (H*T))ˣ) :
      ((ZMod.unitsMap (dvd_mul_left T H) u : ZMod T)-(a : ZMod T) = 0) ↔
        ZMod.unitsMap (dvd_mul_left T H) u = a := by rw [sub_eq_zero, Units.val_inj]
  simp_rw [he]
  simp [restrictedSum, unitClass, Finset.sum_filter, Finset.mul_sum, mul_comm]
  apply Finset.sum_congr (by ext u; simp)
  intro u _
  rfl

theorem restricted_average (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (h k : ZMod (H*T)) :
    restrictedSum (H*T) T (dvd_mul_left T H) a c h k =
      (∑ j : ZMod T, ZMod.stdAddChar (-j*(a : ZMod T)) *
        ErdosKloosterman.sum ZMod.stdAddChar
          (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))) (k*(c : ZMod (H*T))))/(T : ℂ) := by
  have hT : (T : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne T
  apply (eq_div_iff hT).mpr
  simpa only [mul_comm] using (restricted_average_mul H T a c h k).symm

end ErdosHyperbolaIdentities

end

section

namespace ErdosKloosterman

theorem boundAt_prime_power (p a : ℕ) (hp : p.Prime) (ha : 0 < a) : BoundAt (p^a) := by
  let : Fact p.Prime := ⟨hp⟩
  intro _ h k
  have hc : (p^a).divisors.card = a+1 := by
    rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  simpa only [envelope, frequencyGcd, hc] using
    PrimePower.standardSum_prime_power_bound p a ha h k

theorem standardSum_bound (N : ℕ) [NeZero N] (h k : ℤ) :
    ‖standardSum N h k‖ ≤
      (N.divisors.card : ℝ)^2 * (N : ℝ)^((3 : ℝ)/4) *
        ((Nat.gcd N (Int.gcd h k) : ℕ) : ℝ)^((1 : ℝ)/4) :=
  boundAt_all_of_prime_powers boundAt_prime_power N h k

theorem standardSum_bound_half_gcd (N : ℕ) [NeZero N] (h k : ℤ) :
    ‖standardSum N h k‖ ≤
      (N.divisors.card : ℝ)^2 * (N : ℝ)^((3 : ℝ)/4) *
        ((Nat.gcd N (Int.gcd h k) : ℕ) : ℝ)^((1 : ℝ)/2) := by
  have hg : 0 < Nat.gcd N (Int.gcd h k) := Nat.gcd_pos_of_pos_left _ (NeZero.pos N)
  have hg1 : (1 : ℝ) ≤ ((Nat.gcd N (Int.gcd h k) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hg)
  exact (standardSum_bound N h k).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hg1 (by norm_num)) (by positivity))

end ErdosKloosterman

end

section

namespace ErdosHyperbolaError

noncomputable def completeScale (N : ℕ) : ℝ :=
  (N.divisors.card : ℝ)^2 * (N : ℝ)^((3 : ℝ)/4)

theorem completeScale_nonneg (N : ℕ) : 0 ≤ completeScale N := by
  unfold completeScale
  positivity

theorem sum_as_standard (N : ℕ) [NeZero N] (h k : ZMod N) :
    ErdosKloosterman.sum ZMod.stdAddChar h k =
      ErdosKloosterman.standardSum N (h.val : ℤ) (k.val : ℤ) := by
  simp only [ErdosKloosterman.standardSum, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem norm_sum_le_sqrt_second (N : ℕ) [NeZero N] (h k : ZMod N) :
    ‖ErdosKloosterman.sum ZMod.stdAddChar h k‖ ≤
      completeScale N * Real.sqrt (Nat.gcd k.val N) := by
  have hb := ErdosKloosterman.standardSum_bound_half_gcd N (h.val : ℤ) (k.val : ℤ)
  rw [← sum_as_standard N h k] at hb
  simp only [Int.gcd_def, Int.natAbs_natCast, ← Real.sqrt_eq_rpow] at hb
  have hg : (Nat.gcd N (Nat.gcd h.val k.val) : ℝ) ≤ Nat.gcd k.val N := by
    exact_mod_cast gcd_three_le_second N h.val k.val (NeZero.pos N)
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) (completeScale_nonneg N))

theorem norm_sum_le_sqrt_first (N : ℕ) [NeZero N] (h k : ZMod N) :
    ‖ErdosKloosterman.sum ZMod.stdAddChar h k‖ ≤
      completeScale N * Real.sqrt (Nat.gcd h.val N) := by
  rw [ErdosKloosterman.sum_swap]
  exact norm_sum_le_sqrt_second N k h

end ErdosHyperbolaError

end

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def logFactor (N : ℕ) : ℝ :=
  ErdosHyperbola.harmonicConstant * Real.log (2*(N : ℝ))

noncomputable def errorBase (N T : ℕ) : ℝ :=
  completeScale N * (N.divisors.card : ℝ) * Real.sqrt T * (logFactor N)^2

theorem logFactor_one_le (N : ℕ) [NeZero N] : 1 ≤ logFactor N := by
  have hm : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, NeZero.pos N⟩
  have hh := Finset.single_le_sum (s := Finset.Icc 1 N) (f := fun n : ℕ => 1/(n : ℝ))
    (fun _ _ => by positivity) hm
  have hh' : (1 : ℝ) ≤ ErdosHyperbola.harmonicWeight N := by
    simpa only [Nat.cast_one, div_one, ErdosHyperbola.harmonicWeight] using hh
  exact hh'.trans (ErdosHyperbola.harmonicWeight_log_le N (NeZero.pos N))

theorem divisorCount_one_le (N : ℕ) [NeZero N] : (1 : ℝ) ≤ N.divisors.card := by
  have hp : 0 < N.divisors.card := Finset.card_pos.mpr
    ⟨1, Nat.mem_divisors.mpr ⟨one_dvd N, NeZero.ne N⟩⟩
  exact_mod_cast hp

theorem completeScale_one_le (N : ℕ) [NeZero N] : 1 ≤ completeScale N := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hp : (1 : ℝ) ≤ (N : ℝ)^((3 : ℝ)/4) := Real.one_le_rpow hN (by norm_num)
  have hd : (1 : ℝ) ≤ (N.divisors.card : ℝ)^2 := one_le_pow₀ (divisorCount_one_le N)
  exact one_le_mul_of_one_le_of_one_le hd hp

theorem sqrt_modulus_one_le (T : ℕ) [NeZero T] : 1 ≤ Real.sqrt T := by
  have hT : (1 : ℝ) ≤ T := by exact_mod_cast NeZero.pos T
  simpa using Real.sqrt_le_sqrt hT

theorem errorBase_one_le (N T : ℕ) [NeZero N] [NeZero T] : 1 ≤ errorBase N T := by
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (completeScale_one_le N) (divisorCount_one_le N))
      (sqrt_modulus_one_le T)) (one_le_pow₀ (logFactor_one_le N))

theorem errorBase_nonneg (N T : ℕ) : 0 ≤ errorBase N T := by
  unfold errorBase
  exact mul_nonneg (mul_nonneg (mul_nonneg (completeScale_nonneg N) (Nat.cast_nonneg _))
    (Real.sqrt_nonneg _)) (sq_nonneg _)

theorem l1Norm_le_logFactor (N : ℕ) [NeZero N] (P : ProgressionInterval) (hP : P.step.Coprime N) :
    l1Norm N P ≤ 2*(N : ℝ)*logFactor N := by
  calc
    _ ≤ _ := l1Norm_le N P hP
    _ = _ := by unfold logFactor; ring

theorem gcdL1Norm_le_logFactor (N : ℕ) [NeZero N] (P : ProgressionInterval) (hP : P.step.Coprime N) :
    gcdL1Norm N P ≤ 2*(N : ℝ)*(N.divisors.card : ℝ)*logFactor N := by
  calc
    _ ≤ _ := gcdL1Norm_le N P hP
    _ = _ := by unfold logFactor; ring

theorem errorBase_explicit (N T : ℕ) :
    errorBase N T = ErdosHyperbola.harmonicConstant^2 * (N.divisors.card : ℝ)^3 *
      (Real.log (2*(N : ℝ)))^2 * (N : ℝ)^((3 : ℝ)/4) * Real.sqrt T := by
  unfold errorBase logFactor completeScale
  ring

end ErdosHyperbolaError

end

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

theorem restrictedSum_norm_le_average (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (h k : ZMod (H*T)) :
    ‖restrictedSum (H*T) T (dvd_mul_left T H) a c h k‖ ≤
      (∑ j : ZMod T, ‖ErdosKloosterman.sum ZMod.stdAddChar
        (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))) (k*(c : ZMod (H*T)))‖)/(T : ℝ) := by
  rw [restricted_average, norm_div]
  have ht : ‖(T : ℂ)‖ = (T : ℝ) := by simp
  rw [ht]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg T)
  calc
    _ ≤ ∑ j : ZMod T, ‖ZMod.stdAddChar (-j*(a : ZMod T)) *
        ErdosKloosterman.sum ZMod.stdAddChar
          (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))) (k*(c : ZMod (H*T)))‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul, AddChar.norm_apply, one_mul]

theorem restrictedSum_norm_le_second (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (h k : ZMod (H*T)) :
    ‖restrictedSum (H*T) T (dvd_mul_left T H) a c h k‖ ≤
      completeScale (H*T) * Real.sqrt (Nat.gcd k.val (H*T)) := by
  calc
    _ ≤ _ := restrictedSum_norm_le_average H T a c h k
    _ ≤ (∑ _j : ZMod T, completeScale (H*T) * Real.sqrt (Nat.gcd k.val (H*T)))/(T : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg T)
      apply Finset.sum_le_sum
      intro j _
      have hb := norm_sum_le_sqrt_second (H*T)
        (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))) (k*(c : ZMod (H*T)))
      rw [ErdosHyperbola.gcd_mul_unit] at hb
      exact hb
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      have ht : (T : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne T
      field_simp

theorem restrictedSum_norm_le_first (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (h k : ZMod (H*T)) :
    ‖restrictedSum (H*T) T (dvd_mul_left T H) a c h k‖ ≤
      completeScale (H*T) * Real.sqrt T * Real.sqrt (Nat.gcd h.val (H*T)) := by
  calc
    _ ≤ _ := restrictedSum_norm_le_average H T a c h k
    _ ≤ (∑ _j : ZMod T, completeScale (H*T) * Real.sqrt T *
        Real.sqrt (Nat.gcd h.val (H*T)))/(T : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg T)
      apply Finset.sum_le_sum
      intro j _
      have hg : (Nat.gcd (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))).val (H*T) : ℝ) ≤
          (T : ℝ) * Nat.gcd h.val (H*T) := by
        exact_mod_cast shifted_gcd_le H T h j
      calc
        _ ≤ _ := norm_sum_le_sqrt_first (H*T)
          (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))) (k*(c : ZMod (H*T)))
        _ ≤ completeScale (H*T) * Real.sqrt ((T : ℝ)*Nat.gcd h.val (H*T)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) (completeScale_nonneg _)
        _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg T)]; ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      have ht : (T : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne T
      field_simp

end ErdosHyperbolaError

end

section

namespace ErdosHyperbolaError

theorem axis_quadrant_budget (D d s t n U V : ℝ) (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hn : 1 ≤ n) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    D*((2*n*d*t)*(U+1)+s*(2*n*d*t)*(V+1)+(2*n*t)*(2*n*d*t))/n^2 ≤
      8*(D*d*s*t^2)*(1+U/n+V/n) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have ht2 : t ≤ t^2 := by nlinarith
  have hst : t ≤ s*t^2 := by
    calc
      _ ≤ t^2 := ht2
      _ = 1*t^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (sq_nonneg t)
  let E := D*d*s*t^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hA : D*((2*n*d*t)*(U+1)) ≤ 2*E*n*(U+1) := by
    calc
      _ = (2*D*n*d)*(U+1)*t := by ring
      _ ≤ (2*D*n*d)*(U+1)*(s*t^2) := mul_le_mul_of_nonneg_left hst (by positivity)
      _ = _ := by dsimp [E]; ring
  have hB : D*(s*(2*n*d*t)*(V+1)) ≤ 2*E*n*(V+1) := by
    calc
      _ = (2*D*s*n*d)*(V+1)*t := by ring
      _ ≤ (2*D*s*n*d)*(V+1)*t^2 := mul_le_mul_of_nonneg_left ht2 (by positivity)
      _ = _ := by dsimp [E]; ring
  have hC : D*((2*n*t)*(2*n*d*t)) ≤ 4*E*n^2 := by
    calc
      _ = (4*D*d*n^2*t^2)*1 := by ring
      _ ≤ (4*D*d*n^2*t^2)*s := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by dsimp [E]; ring
  have hpoly : 2*n*(U+1)+2*n*(V+1)+4*n^2 ≤ 8*(n^2+n*U+n*V) := by
    have hn2 : n ≤ n^2 := by nlinarith
    nlinarith [mul_nonneg hn0.le hU, mul_nonneg hn0.le hV]
  have hsum : D*((2*n*d*t)*(U+1)+s*(2*n*d*t)*(V+1)+(2*n*t)*(2*n*d*t)) ≤
      8*E*(n^2+n*U+n*V) := by
    calc
      _ = D*((2*n*d*t)*(U+1))+D*(s*(2*n*d*t)*(V+1))+D*((2*n*t)*(2*n*d*t)) := by ring
      _ ≤ 2*E*n*(U+1)+2*E*n*(V+1)+4*E*n^2 := add_le_add (add_le_add hA hB) hC
      _ = E*(2*n*(U+1)+2*n*(V+1)+4*n^2) := by ring
      _ ≤ E*(8*(n^2+n*U+n*V)) := mul_le_mul_of_nonneg_left hpoly hE
      _ = _ := by ring
  calc
    _ ≤ (8*E*(n^2+n*U+n*V))/n^2 := div_le_div_of_nonneg_right hsum (sq_nonneg n)
    _ = _ := by dsimp [E]; field_simp [hn0.ne']

theorem rounding_absorb (N T : ℕ) [NeZero N] [NeZero T] (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (U+V+1)/(N : ℝ) ≤ errorBase N T*(1+U/(N : ℝ)+V/(N : ℝ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hshape : 0 ≤ 1+U/(N : ℝ)+V/(N : ℝ) := by positivity
  calc
    _ = 1/(N : ℝ)+U/(N : ℝ)+V/(N : ℝ) := by ring
    _ ≤ 1+U/(N : ℝ)+V/(N : ℝ) :=
      add_le_add (add_le_add ((div_le_one hN).mpr hN1) le_rfl) le_rfl
    _ = 1*(1+U/(N : ℝ)+V/(N : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (errorBase_one_le N T) hshape

end ErdosHyperbolaError

end

end Erdos970

end OAI
