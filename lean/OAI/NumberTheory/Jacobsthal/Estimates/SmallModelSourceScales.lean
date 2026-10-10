import Mathlib.NumberTheory.Chebyshev
import OAI.NumberTheory.Jacobsthal.Estimates.CorrectionFloorRemainder
import OAI.NumberTheory.Jacobsthal.Estimates.ReciprocalEnvelope
import OAI.NumberTheory.Jacobsthal.Estimates.SourcePairRemainder
import OAI.NumberTheory.Jacobsthal.Partitions.CellLengthLower
import OAI.NumberTheory.Jacobsthal.Partitions.ParentEdgeCoordinates
import OAI.NumberTheory.Jacobsthal.Sieve.ClosedEulerIndividualUpper

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseFrozen
open NumberTheoryLean ErdosInverseHits

noncomputable def frozenCoordinates (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ)
    (a : ℕ → ℕ) : Finset ℕ :=
  ProgressionSmallSieve.progressionSurvivors N ⌊w⌋₊ (b+(q : ℤ)*v) (p*q) a

theorem mem_frozenCoordinates (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ)
    (a : ℕ → ℕ) (j : ℕ) :
    j ∈ frozenCoordinates N w p q b v a ↔ j < N ∧
      ∀ t ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊,
        ¬Int.ModEq (t : ℤ) (b+(q : ℤ)*(v+(p : ℤ)*j)) (a t : ℤ) := by
  rw [frozenCoordinates,ProgressionSmallSieve.progressionSurvivors,SievePartition.mem_survivors]
  simp only [Finset.mem_range,ProgressionSmallSieve.progressionHit,Nat.cast_mul]
  have heq : b+(q : ℤ)*v+(p : ℤ)*q*j = b+(q : ℤ)*(v+(p : ℤ)*j) := by ring
  rw [heq]

theorem frozenCoordinates_eq_of_modEq (N : ℕ) (w : ℝ) (p q q0 M : ℕ)
    (b b0 v v0 : ℤ) (a : ℕ → ℕ)
    (hM : ∀ t ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊,t ∣ M)
    (hq : Int.ModEq (M : ℤ) (q : ℤ) (q0 : ℤ))
    (hb : Int.ModEq (M : ℤ) b b0) (hv : Int.ModEq (M : ℤ) v v0) :
    frozenCoordinates N w p q b v a = frozenCoordinates N w p q0 b0 v0 a := by
  classical
  ext j
  rw [mem_frozenCoordinates,mem_frozenCoordinates]
  apply and_congr_right
  intro _
  apply forall₂_congr
  intro t ht
  have heval := hb.add (hq.mul (hv.add_right ((p : ℤ)*j)))
  have hdiv : (t : ℤ) ∣ (M : ℤ) := by exact_mod_cast hM t ht
  have he := heval.of_dvd hdiv
  exact not_congr ⟨fun h => he.symm.trans h,fun h => he.trans h⟩

end ErdosInverseFrozen

end

section

namespace ErdosInverseEuler
open NumberTheoryLean

noncomputable def smallModulus (w : ℝ) : ℕ := IntervalBoundingSieve.cutoffProduct ⌊w⌋₊

theorem smallModulus_pos (w : ℝ) : 0 < smallModulus w := by
  unfold smallModulus IntervalBoundingSieve.cutoffProduct
  exact Finset.prod_pos (fun p hp => (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1.pos)

theorem log_smallModulus_eq_theta (w : ℝ) : Real.log (smallModulus w : ℝ) = Chebyshev.theta w := by
  have hn : ∀ p ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊,(p : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1.ne_zero
  unfold smallModulus IntervalBoundingSieve.cutoffProduct
  rw [Nat.cast_prod,Real.log_prod hn,cutoffPrimes_eq_filtered_Ioc]
  rfl

theorem log_smallModulus_le (w : ℝ) (hw : 0 ≤ w) :
    Real.log (smallModulus w : ℝ) ≤ Real.log 4*w := by
  rw [log_smallModulus_eq_theta]
  exact Chebyshev.theta_le_log4_mul_x hw

theorem smallModulus_le_exp (w : ℝ) (hw : 0 ≤ w) :
    (smallModulus w : ℝ) ≤ Real.exp (Real.log 4*w) := by
  have hp : (0 : ℝ) < smallModulus w := by exact_mod_cast smallModulus_pos w
  calc
    (smallModulus w : ℝ) = Real.exp (Real.log (smallModulus w : ℝ)) := (Real.exp_log hp).symm
    _ ≤ _ := Real.exp_le_exp.mpr (log_smallModulus_le w hw)

end ErdosInverseEuler

end

section

namespace ErdosInverseFrozen
open NumberTheoryLean ErdosInverseHits ErdosInverseEuler ErdosInverseCounts

theorem cutoffPrime_dvd_smallModulus (w : ℝ) (t : ℕ)
    (ht : t ∈ LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) : t ∣ smallModulus w := by
  unfold smallModulus IntervalBoundingSieve.cutoffProduct
  exact Finset.dvd_prod_of_mem id ht

theorem parentCoordinates_eq_pattern (Y : ℕ) (w : ℝ) (a : ℕ → ℕ)
    (p q : ℕ) [NeZero p] (hqp : q.Coprime p) (hq : Squarefree q) :
    parentSurvivorCoordinates Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a p q hqp hq =
      frozenCoordinates (hitLength Y (p*q) (sourceParentBase p q hqp hq a)) w p q
        (primeHitRepresentative q hq a) (parentSlope p q hqp (a p) (primeHitRepresentative q hq a)) a := by
  classical
  ext j
  rw [mem_frozenCoordinates]
  simp only [parentSurvivorCoordinates,Finset.mem_filter,Finset.mem_range]
  apply and_congr_right
  intro _
  apply forall₂_congr
  intro t _
  have hpoint : ((sourceParentBase p q hqp hq a+p*q*j : ℕ) : ℤ) =
      (primeHitRepresentative q hq a : ℤ)+(q : ℤ)*
        ((parentSlope p q hqp (a p) (primeHitRepresentative q hq a) : ℕ)+(p : ℤ)*j) := by
    unfold sourceParentBase
    push_cast
    ring
  rw [← hpoint]
  exact not_congr Int.natCast_modEq_iff.symm

theorem parentCoordinates_eq_frozen_center (Y : ℕ) (w : ℝ) (a : ℕ → ℕ)
    (p q q0 : ℕ) [NeZero p] (hqp : q.Coprime p) (hq : Squarefree q) (b0 v : ℤ)
    (hqq : Int.ModEq (smallModulus w : ℤ) (q : ℤ) (q0 : ℤ))
    (hbb : Int.ModEq (smallModulus w : ℤ) (primeHitRepresentative q hq a : ℤ) b0)
    (hsv : Int.ModEq (smallModulus w : ℤ)
      (parentSlope p q hqp (a p) (primeHitRepresentative q hq a) : ℤ) v) :
    parentSurvivorCoordinates Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a p q hqp hq =
      frozenCoordinates (hitLength Y (p*q) (sourceParentBase p q hqp hq a)) w p q0 b0 v a := by
  rw [parentCoordinates_eq_pattern]
  exact frozenCoordinates_eq_of_modEq _ w p q q0 (smallModulus w) _ b0 _ v a
    (cutoffPrime_dvd_smallModulus w) hqq hbb hsv

theorem actual_parent_count_frozen (Y : ℕ) (w : ℝ) (a : ℕ → ℕ)
    (p q q0 : ℕ) [NeZero p] (hp : p.Prime) (hqp : q.Coprime p) (hq : Squarefree q) (b0 v : ℤ)
    (hqq : Int.ModEq (smallModulus w : ℤ) (q : ℤ) (q0 : ℤ))
    (hbb : Int.ModEq (smallModulus w : ℤ) (primeHitRepresentative q hq a : ℤ) b0)
    (hsv : Int.ModEq (smallModulus w : ℤ)
      (parentSlope p q hqp (a p) (primeHitRepresentative q hq a) : ℤ) v) :
    modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a (p*q) =
      ((frozenCoordinates (hitLength Y (p*q) (sourceParentBase p q hqp hq a)) w p q0 b0 v a).card : ℤ) := by
  rw [modulusCount_eq_parent_card Y _ a p q hp hqp hq,
    parentCoordinates_eq_frozen_center Y w a p q q0 hqp hq b0 v hqq hbb hsv]

theorem actual_child_count_frozen (Y : ℕ) (w : ℝ) (a : ℕ → ℕ)
    (p q q0 u : ℕ) [NeZero p] (hp : p.Prime) (hu : u.Prime) (hqp : q.Coprime p)
    (hq : Squarefree q) (hpu : p.Coprime u) (hqu : q.Coprime u) (b0 v : ℤ)
    (hqq : Int.ModEq (smallModulus w : ℤ) (q : ℤ) (q0 : ℤ))
    (hbb : Int.ModEq (smallModulus w : ℤ) (primeHitRepresentative q hq a : ℤ) b0)
    (hsv : Int.ModEq (smallModulus w : ℤ)
      (parentSlope p q hqp (a p) (primeHitRepresentative q hq a) : ℤ) v) :
    modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a (p*q*u) =
      (((frozenCoordinates (hitLength Y (p*q) (sourceParentBase p q hqp hq a)) w p q0 b0 v a).filter
        (fun j : ℕ => (j : ZMod u) = parentEdgeResidue p q u hqp hq hpu hqu a)).card : ℤ) := by
  classical
  rw [modulusCount_eq_edge_card Y _ a p q u hp hu hqp hq hpu hqu,
    parentCoordinates_eq_frozen_center Y w a p q q0 hqp hq b0 v hqq hbb hsv]

end ErdosInverseFrozen

end

section

namespace ErdosVarianceSmallModel
open NumberTheoryLean ErdosInverseEuler ErdosHyperbolaError
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def divisorPrimes (w : ℝ) (H : ℕ) : Finset ℕ :=
  (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊).filter (fun t => t ∣ H)
noncomputable def coprimePrimes (w : ℝ) (H : ℕ) : Finset ℕ :=
  (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊).filter (fun t => ¬t ∣ H)
noncomputable def divisorModulus (w : ℝ) (H : ℕ) : ℕ := ∏ t ∈ divisorPrimes w H,t
noncomputable def coprimeModulus (w : ℝ) (H : ℕ) : ℕ := ∏ t ∈ coprimePrimes w H,t

theorem divisorModulus_pos (w : ℝ) (H : ℕ) : 0 < divisorModulus w H :=
  Finset.prod_pos (fun _t ht => (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1.pos)

theorem coprimeModulus_pos (w : ℝ) (H : ℕ) : 0 < coprimeModulus w H :=
  Finset.prod_pos (fun _t ht => (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1.pos)

theorem pattern_moduli_product (w : ℝ) (H : ℕ) :
    divisorModulus w H*coprimeModulus w H = smallModulus w := by
  unfold divisorModulus coprimeModulus divisorPrimes coprimePrimes
  rw [Finset.prod_filter_mul_prod_filter_not]
  rfl

theorem divisorModulus_dvd_H (w : ℝ) (H : ℕ) : divisorModulus w H ∣ H := by
  apply Finset.prod_primes_dvd
  · intro t ht
    exact (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1).1.prime
  · intro t ht
    exact (Finset.mem_filter.mp ht).2

theorem coprimeModulus_coprime_H (w : ℝ) (H : ℕ) : (coprimeModulus w H).Coprime H := by
  apply Nat.coprime_prod_left_iff.mpr
  intro t ht
  have hh := Finset.mem_filter.mp ht
  exact (LargePrimeDeletion.mem_cutoffPrimes.mp hh.1).1.coprime_iff_not_dvd.mpr hh.2

theorem pattern_moduli_coprime (w : ℝ) (H : ℕ) : (divisorModulus w H).Coprime (coprimeModulus w H) :=
  (coprimeModulus_coprime_H w H).symm.of_dvd_left (divisorModulus_dvd_H w H)

theorem effective_pattern_coprime (w : ℝ) (H : ℕ) :
    (H*divisorModulus w H).Coprime (coprimeModulus w H) :=
  (coprimeModulus_coprime_H w H).symm.mul_left (pattern_moduli_coprime w H)

theorem pattern_totient (w : ℝ) (H : ℕ) :
    (H*divisorModulus w H*coprimeModulus w H).totient =
      H.totient*divisorModulus w H*(coprimeModulus w H).totient := by
  rw [Nat.totient_mul (effective_pattern_coprime w H),
    source_totient_product H (divisorModulus w H) (divisorModulus_dvd_H w H) (divisorModulus_pos w H)]
  ring

theorem pattern_modulus_size (w : ℝ) (H : ℕ) :
    H*divisorModulus w H*coprimeModulus w H = H*smallModulus w := by
  rw [Nat.mul_assoc,pattern_moduli_product]

theorem prime_coprime_small_pattern (w : ℝ) (hw : 0 ≤ w) (H p : ℕ)
    (hp : p.Prime) (hwp : w < (p : ℝ)) : p.Coprime (coprimeModulus w H) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro t ht
  have hh := LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_filter.mp ht).1
  have htw := (Nat.le_floor_iff hw).mp hh.2
  apply (Nat.coprime_primes hp hh.1).mpr
  intro he
  subst t
  linarith

end ErdosVarianceSmallModel

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseEuler
open ErdosInverseBoxHeight

theorem sourceW_tendsto_atTop : Tendsto sourceW atTop atTop := by
  have hs := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1/2)).bound zero_lt_one
  have hlow : (fun z : ℝ => (Real.log z)^((1 : ℝ)/2)) ≤ᶠ[atTop] sourceW := by
    filter_upwards [Real.tendsto_log_atTop.eventually hs,
      Real.tendsto_log_atTop.eventually_gt_atTop 1] with z hz hL
    have hL0 : 0 < Real.log z := by linarith
    have hLL : 0 < Real.log (Real.log z) := Real.log_pos hL
    have hh : (Real.log (Real.log z))^2 ≤ (Real.log z)^((1 : ℝ)/2) := by
      simpa only [Real.norm_eq_abs,Real.rpow_two,abs_of_nonneg (sq_nonneg (Real.log (Real.log z))),
        abs_of_nonneg (Real.rpow_nonneg hL0.le ((1 : ℝ)/2)),one_mul] using hz
    have hp : (Real.log z)^((1 : ℝ)/2)*(Real.log z)^((1 : ℝ)/2) = Real.log z := by
      rw [← Real.rpow_add hL0]
      norm_num
    apply (le_div_iff₀ (sq_pos_of_pos hLL)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hL0.le ((1 : ℝ)/2))]
  exact tendsto_atTop_mono' atTop hlow ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp Real.tendsto_log_atTop)

theorem sourceZ_le_rpow (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ sourceZ z ≤ z^eps := by
  have hh := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 1 (1/eps))
  filter_upwards [hh,eventually_gt_atTop (1 : ℝ)] with z hLL hz
  have hL0 : 0 < Real.log z := Real.log_pos hz
  have hLL1 : 1 ≤ Real.log (Real.log z) := (le_max_left _ _).trans hLL
  have hLL0 : 0 < Real.log (Real.log z) := by linarith
  have hpay : 1 ≤ Real.log (Real.log z)*eps := (div_le_iff₀ heps).mp ((le_max_right _ _).trans hLL)
  refine ⟨hz,?_⟩
  rw [sourceZ,Real.rpow_def_of_pos (by linarith : 0 < z)]
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hLL0).mpr
  nlinarith [mul_le_mul_of_nonneg_left hpay hL0.le]

theorem smallModulus_source_power (k : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, (smallModulus (sourceW z) : ℝ)^k ≤ (sourceZ z)^eps := by
  have hh := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
    (max 1 ((k : ℝ)*Real.log 4/eps))
  filter_upwards [hh,Real.tendsto_log_atTop.eventually_gt_atTop 1] with z hLL hL
  have hL0 : 0 < Real.log z := by linarith
  have hLL1 : 1 ≤ Real.log (Real.log z) := (le_max_left _ _).trans hLL
  have hLL0 : 0 < Real.log (Real.log z) := by linarith
  have hW0 : 0 ≤ sourceW z := div_nonneg hL0.le (sq_nonneg _)
  have hpay : (k : ℝ)*Real.log 4 ≤ Real.log (Real.log z)*eps :=
    (div_le_iff₀ heps).mp ((le_max_right _ _).trans hLL)
  have hscale : (k : ℝ)*(Real.log 4*sourceW z) ≤ (Real.log z/Real.log (Real.log z))*eps := by
    calc
      _ = ((k : ℝ)*Real.log 4*Real.log z)/(Real.log (Real.log z))^2 := by unfold sourceW;ring
      _ ≤ (Real.log (Real.log z)*eps*Real.log z)/(Real.log (Real.log z))^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpay hL0.le) (sq_nonneg _)
      _ = _ := by field_simp
  calc
    _ ≤ (Real.exp (Real.log 4*sourceW z))^k := pow_le_pow_left₀ (Nat.cast_nonneg _) (smallModulus_le_exp _ hW0) k
    _ = Real.exp ((k : ℝ)*(Real.log 4*sourceW z)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((Real.log z/Real.log (Real.log z))*eps) := Real.exp_le_exp.mpr hscale
    _ = (sourceZ z)^eps := Real.exp_mul _ _

end ErdosInverseEuler

end

section

namespace ErdosVarianceSmallModel

instance (w : ℝ) (H : ℕ) : NeZero (divisorModulus w H) := ⟨(divisorModulus_pos w H).ne'⟩
instance (w : ℝ) (H : ℕ) : NeZero (coprimeModulus w H) := ⟨(coprimeModulus_pos w H).ne'⟩

abbrev Pattern (w : ℝ) (H : ℕ) := (ZMod (coprimeModulus w H))ˣ × ZMod (divisorModulus w H)
abbrev ModelPoint (w : ℝ) (H : ℕ) := ℤ × Pattern w H

theorem pattern_card (w : ℝ) (H : ℕ) :
    Fintype.card (Pattern w H) = divisorModulus w H*(coprimeModulus w H).totient := by
  simp only [Pattern,Fintype.card_prod,ZMod.card_units_eq_totient,ZMod.card]
  ring

end ErdosVarianceSmallModel

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseEuler
open ErdosInverseBoxHeight

theorem exp_loglog_sq_le_sourceZ (C eps : ℝ) (hC : 0 ≤ C) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,
      Real.exp (C*(Real.log (Real.log z))^2) ≤ (sourceZ z)^eps := by
  have hC1 : 0 < C+1 := by linarith
  have hs := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) zero_lt_one).bound
    (div_pos heps hC1)
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_gt_atTop 1]
    with z hz hLL hL
  have hLL0 : 0 < Real.log (Real.log z) := by change 1 ≤ Real.log (Real.log z) at hLL;linarith
  have hL0 : 0 < Real.log z := by linarith
  have hcube : (Real.log (Real.log z))^3 ≤ (eps/(C+1))*Real.log z := by
    simpa only [Real.norm_eq_abs,Real.rpow_ofNat,Real.rpow_one,
      abs_of_nonneg (pow_nonneg hLL0.le 3),abs_of_nonneg hL0.le] using hz
  have hpay : C*(Real.log (Real.log z))^3 ≤ eps*Real.log z := by
    have hm := (le_div_iff₀ hC1).mp (show (Real.log (Real.log z))^3 ≤ (eps*Real.log z)/(C+1) by
      simpa only [div_mul_eq_mul_div] using hcube)
    nlinarith [pow_nonneg hLL0.le 3]
  rw [sourceZ,← Real.exp_mul]
  apply Real.exp_le_exp.mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hLL0).mpr
  nlinarith only [hpay]

theorem log_pow_le_sourceZ (r : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, (Real.log z)^r ≤ (sourceZ z)^eps := by
  filter_upwards [exp_loglog_sq_le_sourceZ r eps (Nat.cast_nonneg _) heps,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_gt_atTop 1]
    with z hz hLL hL
  have hLL1 : 1 ≤ Real.log (Real.log z) := hLL
  have hLL0 : 0 < Real.log (Real.log z) := by linarith
  have hL0 : 0 < Real.log z := by linarith
  calc
    (Real.log z)^r = (Real.exp (Real.log (Real.log z)))^r := by rw [Real.exp_log hL0]
    _ = Real.exp ((r : ℝ)*Real.log (Real.log z)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((r : ℝ)*(Real.log (Real.log z))^2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg _)
    _ ≤ _ := hz

theorem sourceZ_tendsto_atTop : Tendsto sourceZ atTop atTop := by
  have hlow : (fun z : ℝ => Real.log z) ≤ᶠ[atTop] sourceZ := by
    filter_upwards [log_pow_le_sourceZ 1 1 zero_lt_one] with z hz
    simpa only [pow_one,Real.rpow_one] using hz
  exact tendsto_atTop_mono' atTop hlow Real.tendsto_log_atTop

theorem smallModulus_mul_log_power (k r : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,
      (smallModulus (sourceW z) : ℝ)^k*(Real.log z)^r ≤ (sourceZ z)^eps := by
  filter_upwards [smallModulus_source_power k (eps/2) (by positivity),
    log_pow_le_sourceZ r (eps/2) (by positivity),
    Real.tendsto_log_atTop.eventually_ge_atTop 0] with z hk hr hL
  calc
    _ ≤ (sourceZ z)^(eps/2)*(sourceZ z)^(eps/2) :=
      mul_le_mul hk hr (pow_nonneg hL _) (Real.rpow_nonneg (Real.exp_pos _).le _)
    _ = (sourceZ z)^(eps/2+eps/2) := (Real.rpow_add (Real.exp_pos _) _ _).symm
    _ = _ := by congr 1;ring

end ErdosInverseEuler

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseTail
open ErdosInverseBoxHeight ErdosInverseEuler

theorem source_common_length_regime (aStar xi : ℝ) (ha : 0 < aStar)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,2 ≤ sourceW z ∧
      ∀ (Y p q u : ℕ) (Qplus : ℝ),0 < p → 0 < q → 0 < u →
        (q : ℝ) ≤ Qplus → Qplus ≤ (1+xi)*(q : ℝ) →
        3*aStar/4 ≤ Real.log ((Y : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z) →
        3 ≤ xi*(commonParentLength Y p Qplus : ℝ) ∧
          (sourceW z)^(aStar/2) ≤ 2*xi*(commonParentLength Y p Qplus : ℝ)/(u : ℝ) := by
  have ht3 := (tendsto_rpow_atTop (by linarith : 0 < 3*aStar/4)).comp sourceW_tendsto_atTop
  have htq := (tendsto_rpow_atTop (by linarith : 0 < aStar/4)).comp sourceW_tendsto_atTop
  filter_upwards [sourceW_tendsto_atTop.eventually_ge_atTop 2,
    ht3.eventually_ge_atTop (max 4 (12/xi)),htq.eventually_ge_atTop (2/xi)] with z hw hv hquarter
  refine ⟨hw,?_⟩
  intro Y p q u Qplus hp hq hu hqQ hQq hlen
  change 2/xi ≤ (sourceW z)^(aStar/4) at hquarter
  have hwpos : 0 < sourceW z := by linarith
  have hv4 : 4 ≤ (sourceW z)^(3*aStar/4) := (le_max_left _ _).trans hv
  have hvpay : 12/xi ≤ (sourceW z)^(3*aStar/4) := (le_max_right _ _).trans hv
  have hgeo := common_length_from_log Y p q u hp hq hu Qplus xi (sourceW z) aStar
    hqQ hQq hxi.le hxi1 (by linarith) ha hlen
  rw [mul_div_assoc (2 : ℝ) (commonParentLength Y p Qplus : ℝ) (u : ℝ)] at hgeo
  have hJlow : (sourceW z)^(3*aStar/4)/4 ≤ (commonParentLength Y p Qplus : ℝ)/(u : ℝ) := by
    nlinarith
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hJup : (commonParentLength Y p Qplus : ℝ)/(u : ℝ) ≤ commonParentLength Y p Qplus :=
    div_le_self (Nat.cast_nonneg _) hu1
  have hJpay := mul_le_mul_of_nonneg_left hJlow hxi.le
  constructor
  · have hlarge := (div_le_iff₀ hxi).mp hvpay
    have hmono := mul_le_mul_of_nonneg_left hJup hxi.le
    nlinarith
  · have hquarterpay := (div_le_iff₀ hxi).mp hquarter
    have hhalf : 0 ≤ (sourceW z)^(aStar/2) := Real.rpow_nonneg hwpos.le _
    have hfactor : (sourceW z)^(aStar/2)*(sourceW z)^(aStar/4) = (sourceW z)^(3*aStar/4) := by
      rw [← Real.rpow_add hwpos]
      congr 1
      ring
    have hm := mul_le_mul_of_nonneg_left hquarterpay hhalf
    have hf := congrArg (fun x : ℝ => x*xi) hfactor
    have hpaid : (sourceW z)^(aStar/2) ≤ 2*xi*((commonParentLength Y p Qplus : ℝ)/(u : ℝ)) := by
      nlinarith [hf]
    simpa only [mul_div_assoc] using hpaid

end ErdosInverseTail

end

section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceSmallModel
open ErdosInverseBoxHeight ErdosInverseEuler

theorem source_Z_power_R (alpha beta : ℝ) (n : ℕ) (ha : 0 < alpha) (hb : 0 < beta) (hn : 0 < n) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R : ℝ,z^alpha ≤ R → (sourceZ z)^n ≤ R^beta := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  filter_upwards [sourceZ_le_rpow (alpha*beta/(n : ℝ)) (by positivity)] with z hz
  refine ⟨hz.1,?_⟩
  intro R hR
  have hz0 : 0 < z := by linarith [hz.1]
  calc
    _ ≤ (z^(alpha*beta/(n : ℝ)))^n := pow_le_pow_left₀ (Real.exp_pos _).le hz.2 n
    _ = z^(alpha*beta) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hz0.le]
      congr 1
      field_simp
    _ ≤ _ := by
      have hh := Real.rpow_le_rpow (Real.rpow_nonneg hz0.le alpha) hR hb.le
      simpa only [← Real.rpow_mul hz0.le] using hh

theorem primeWidth_lower_Z (R xi H C0 Z : ℝ) (hR : 0 < R) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hH : 0 < H) (hZ : 0 < Z) (hInv : 1/Z ≤ xi) (hRatio : totalScale R H C0/H ≤ Z^12) :
    R/Z^13 ≤ primeWidth R xi H C0 := by
  have hT := totalScale_pos R H C0 hH
  have hTbound := (div_le_iff₀ hH).mp hRatio
  calc
    _ = (R/Z^12)*(1/Z) := by field_simp
    _ ≤ (R/Z^12)*xi := mul_le_mul_of_nonneg_left hInv (by positivity)
    _ = xi*R/Z^12 := by ring
    _ ≤ xi*R*H/totalScale R H C0 := by
      apply (div_le_div_iff₀ (pow_pos hZ 12) hT).mpr
      have hh := mul_le_mul_of_nonneg_left hTbound (mul_pos hxi hR).le
      nlinarith
    _ ≤ _ := primeWidth_lower R xi H C0 hR hxi hxi1 hH

theorem source_prime_width_lower (alpha xi : ℝ) (ha : 0 < alpha) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R H C0 : ℝ,z^alpha ≤ R → 0 < H →
      totalScale R H C0/H ≤ (sourceZ z)^12 → R^((19 : ℝ)/20) ≤ primeWidth R xi H C0 := by
  filter_upwards [source_Z_power_R alpha (1/20) 13 ha (by norm_num) (by decide),
    sourceZ_tendsto_atTop.eventually_ge_atTop (1/xi)] with z hz hZxi
  refine ⟨hz.1,?_⟩
  intro R H C0 hRlo hH hRatio
  have hz0 : 0 < z := by linarith [hz.1]
  have hR : 0 < R := (Real.rpow_pos_of_pos hz0 alpha).trans_le hRlo
  have hZ : 0 < sourceZ z := Real.exp_pos _
  have hInv : 1/sourceZ z ≤ xi := by
    apply (div_le_iff₀ hZ).mpr
    have hh := (div_le_iff₀ hxi).mp hZxi
    nlinarith
  have hZX := primeWidth_lower_Z R xi H C0 (sourceZ z) hR hxi hxi1 hH hZ hInv hRatio
  apply le_trans _ hZX
  apply (le_div_iff₀ (pow_pos hZ 13)).mpr
  calc
    _ ≤ R^((19 : ℝ)/20)*R^((1 : ℝ)/20) :=
      mul_le_mul_of_nonneg_left (hz.2 R hRlo) (Real.rpow_nonneg hR.le _)
    _ = R := by rw [← Real.rpow_add hR];norm_num

theorem source_small_modulus_R (alpha : ℝ) (ha : 0 < alpha) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R : ℝ,z^alpha ≤ R → (smallModulus (sourceW z) : ℝ) ≤ R^((1 : ℝ)/20) := by
  filter_upwards [smallModulus_source_power 1 1 zero_lt_one,
    source_Z_power_R alpha (1/20) 1 ha (by norm_num) Nat.zero_lt_one] with z hM hR
  refine ⟨hR.1,?_⟩
  intro R hRlo
  have hh : (smallModulus (sourceW z) : ℝ) ≤ sourceZ z := by simpa only [pow_one,Real.rpow_one] using hM
  exact hh.trans (by simpa only [pow_one] using hR.2 R hRlo)

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
