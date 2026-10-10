import OAI.NumberTheory.CubicMoment.Estimates.ShortMoebiusFinite
import Mathlib.Data.Nat.Choose.Sum

namespace OAI

/-! Finite Euler exclusions on the complete ideal lattice. The full norm
ball includes the ramified prime; excluding it is an explicit choice of
prime set, and every rescaling factor is retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- All nonzero ideals of norm at most `Y`, including ideals above three. -/
def fullIdealBall (Y : ℝ) : Finset EisensteinIdealExponent :=
  (nonzeroNormBall Y).image idealExponentOf

@[simp] lemma mem_fullIdealBall {ν : EisensteinIdealExponent} {Y : ℝ} :
    ν ∈ fullIdealBall Y ↔ idealExponentNorm ν ≤ Y := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    rw [idealExponentOf_norm (mem_nonzeroNormBall.mp ha).2]
    exact (mem_nonzeroNormBall.mp ha).1
  · intro h
    exact Finset.mem_image.mpr ⟨idealExponentGenerator ν,
      mem_nonzeroNormBall.mpr ⟨by simpa only [idealExponentNorm,normNat_cast] using h,
        idealExponentGenerator_ne_zero ν⟩,idealExponentOf_generator ν⟩

/-- The squarefree product of a finite set of prime ideals. -/
def primeSetExponent (S : Finset EisensteinIdealPrime) : EisensteinIdealExponent :=
  ∑ p ∈ S, Finsupp.single p 1

@[simp] lemma primeSetExponent_apply (S : Finset EisensteinIdealPrime)
    (p : EisensteinIdealPrime) : primeSetExponent S p = if p ∈ S then 1 else 0 := by
  simp [primeSetExponent,Finsupp.single_apply]

lemma primeSetExponent_le_iff (S : Finset EisensteinIdealPrime) (ν : EisensteinIdealExponent) :
    primeSetExponent S ≤ ν ↔ ∀ p ∈ S, 0 < ν p := by
  constructor
  · intro h p hp
    have h1 := h p
    simpa only [primeSetExponent_apply,ite_eq_left hp,Nat.one_le_iff_ne_zero,
      Nat.pos_iff_ne_zero] using h1
  · intro h p
    by_cases hp : p ∈ S
    · simpa only [primeSetExponent_apply,ite_eq_left hp] using (Nat.succ_le_iff.mpr (h p hp))
    · simp [hp]

/-- Exact finite inclusion--exclusion for the prime-to-`S` condition. -/
lemma ideal_prime_exclusion_indicator (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) :
    (if ∀ p ∈ S, ν p = 0 then (1:ℂ) else 0) =
      ∑ T ∈ S.powerset, if primeSetExponent T ≤ ν then (-1:ℂ)^T.card else 0 := by
  have he : S.powerset.filter (fun T => primeSetExponent T ≤ ν) =
      (S.filter (fun p => 0 < ν p)).powerset := by
    ext T
    simp only [Finset.mem_filter,Finset.mem_powerset,primeSetExponent_le_iff]
    constructor
    · rintro ⟨hTS,hpos⟩ p hp
      exact Finset.mem_filter.mpr ⟨hTS hp,hpos p hp⟩
    · intro h
      exact ⟨fun p hp => (Finset.mem_filter.mp (h hp)).1,
        fun p hp => (Finset.mem_filter.mp (h hp)).2⟩
  rw [← Finset.sum_filter,he]
  have hsum : (∑ T ∈ (S.filter (fun p => 0 < ν p)).powerset, (-1:ℂ)^T.card) =
      if S.filter (fun p => 0 < ν p) = ∅ then 1 else 0 := by
    exact_mod_cast (Finset.sum_powerset_neg_one_pow_card (x := S.filter (fun p => 0 < ν p)))
  rw [hsum]
  have hzero : S.filter (fun p => 0 < ν p) = ∅ ↔ ∀ p ∈ S, ν p = 0 := by
    simp only [Finset.filter_eq_empty_iff,Nat.not_lt,Nat.le_zero]
  simp only [hzero]

lemma idealNorm_shift_mem_iff (δ ν : EisensteinIdealExponent) (Y : ℝ) :
    δ+ν ∈ fullIdealBall Y ↔ ν ∈ fullIdealBall (Y/idealExponentNorm δ) := by
  simp only [mem_fullIdealBall,idealExponentNorm_add]
  rw [le_div_iff₀ (idealExponentNorm_pos δ)]
  rw [mul_comm]

lemma idealNorm_tsub_mem {δ ν : EisensteinIdealExponent} (hδ : δ ≤ ν)
    {Y : ℝ} (hν : ν ∈ fullIdealBall Y) :
    ν-δ ∈ fullIdealBall (Y/idealExponentNorm δ) := by
  apply (idealNorm_shift_mem_iff δ (ν-δ) Y).mp
  simpa only [add_tsub_cancel_of_le hδ] using hν

/-- An exact rescaled complete ideal sum for one divisor. Character
multiplicativity is explicit, and no Euler factor is silently deleted. -/
lemma fullIdealBall_shift_sum (δ : EisensteinIdealExponent) (Y : ℝ)
    (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν κ, χ (ν+κ) = χ ν*χ κ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) :
    (∑ ν ∈ fullIdealBall Y, if δ ≤ ν then χ ν*W (idealExponentNorm ν/Z) else 0) =
      χ δ * ∑ κ ∈ fullIdealBall (Y/idealExponentNorm δ),
        χ κ*W (idealExponentNorm κ/(Z/idealExponentNorm δ)) := by
  rw [← Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_bij' (fun ν _ => ν-δ) (fun κ _ => δ+κ)
  · intro ν hν
    exact idealNorm_tsub_mem (Finset.mem_filter.mp hν).2 (Finset.mem_filter.mp hν).1
  · intro κ hκ
    exact Finset.mem_filter.mpr ⟨(idealNorm_shift_mem_iff δ κ Y).mpr hκ,
      le_add_of_nonneg_right zero_le⟩
  · intro ν hν
    exact add_tsub_cancel_of_le (Finset.mem_filter.mp hν).2
  · intro κ hκ
    exact add_tsub_cancel_left δ κ
  · intro ν hν
    have hd := (Finset.mem_filter.mp hν).2
    have he : δ+(ν-δ) = ν := add_tsub_cancel_of_le hd
    have hnorm : idealExponentNorm ν/Z =
        idealExponentNorm (ν-δ)/(Z/idealExponentNorm δ) := by
      calc
        _ = (idealExponentNorm δ*idealExponentNorm (ν-δ))/Z := by
          rw [← idealExponentNorm_add,he]
        _ = _ := by field_simp [ne_of_gt hZ,ne_of_gt (idealExponentNorm_pos δ)]
    have hchar : χ ν = χ δ*χ (ν-δ) := (congrArg χ he).symm.trans (hχ _ _)
    rw [hchar,hnorm]
    ring

/-- Removing any finite set of local Euler factors is a finite sum of
complete ideal sums at the exact rescaled lengths. The finite set may
include the ramified prime; its norm and character factor are retained. -/
theorem fullIdealBall_euler_exclusion (S : Finset EisensteinIdealPrime)
    (Y : ℝ) (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν κ, χ (ν+κ) = χ ν*χ κ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) :
    (∑ ν ∈ fullIdealBall Y, if ∀ p ∈ S, ν p = 0 then χ ν*W (idealExponentNorm ν/Z) else 0) =
      ∑ T ∈ S.powerset, (-1:ℂ)^T.card*χ (primeSetExponent T)*
        ∑ κ ∈ fullIdealBall (Y/idealExponentNorm (primeSetExponent T)),
          χ κ*W (idealExponentNorm κ/(Z/idealExponentNorm (primeSetExponent T))) := by
  calc
    _ = ∑ ν ∈ fullIdealBall Y, ∑ T ∈ S.powerset,
        (if primeSetExponent T ≤ ν then (-1:ℂ)^T.card else 0)*
          (χ ν*W (idealExponentNorm ν/Z)) := by
      apply Finset.sum_congr rfl
      intro ν hν
      rw [← Finset.sum_mul,← ideal_prime_exclusion_indicator]
      split_ifs <;> simp
    _ = ∑ T ∈ S.powerset, ∑ ν ∈ fullIdealBall Y,
        (if primeSetExponent T ≤ ν then (-1:ℂ)^T.card else 0)*
          (χ ν*W (idealExponentNorm ν/Z)) := Finset.sum_comm
    _ = ∑ T ∈ S.powerset, (-1:ℂ)^T.card *
        (∑ ν ∈ fullIdealBall Y,
          if primeSetExponent T ≤ ν then χ ν*W (idealExponentNorm ν/Z) else 0) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν hν
      split_ifs <;> simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [fullIdealBall_shift_sum _ Y χ hχ W hZ]
      ring

lemma compactSupport_upper_cutoff (W : ℝ → ℂ) (hW : HasCompactSupport W) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, B < x → W x = 0 := by
  obtain ⟨R,hR⟩ := hW.isCompact.isBounded.exists_norm_le
  refine ⟨max R 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x hx
  by_contra hne
  have hbound := hR x (subset_tsupport W hne)
  have hRabs : |x| ≤ R := by simpa only [Real.norm_eq_abs] using hbound
  have hle : x ≤ max R 1 := (le_abs_self x).trans (hRabs.trans (le_max_left _ _))
  exact (not_le_of_gt hx) hle

/-- Compact norm support makes the complete ideal sum literally finite;
no analytic convergence hypothesis is required for this reduction. -/
lemma ideal_smooth_tsum_eq_ball (χ : EisensteinIdealExponent → ℂ) (W : ℝ → ℂ)
    {B Z : ℝ} (hZ : 0 < Z) (hW : ∀ x : ℝ, B < x → W x = 0) :
    (∑' ν, χ ν*W (idealExponentNorm ν/Z)) =
      ∑ ν ∈ fullIdealBall (B*Z), χ ν*W (idealExponentNorm ν/Z) := by
  apply tsum_eq_sum
  intro ν hν
  have hN : B*Z < idealExponentNorm ν := lt_of_not_ge (fun h => hν (mem_fullIdealBall.mpr h))
  rw [hW _ ((lt_div_iff₀ hZ).mpr hN),mul_zero]

/-- The actual complete smooth ideal sum, with finite Euler exclusions.
In particular, selecting the ramified prime in `S` restores or removes its
local factor through this formula with its exact norm and character value. -/
theorem smooth_ideal_euler_exclusion (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν κ, χ (ν+κ) = χ ν*χ κ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    {Z : ℝ} (hZ : 0 < Z) :
    (∑' ν, if ∀ p ∈ S, ν p = 0 then χ ν*W (idealExponentNorm ν/Z) else 0) =
      ∑ T ∈ S.powerset, (-1:ℂ)^T.card*χ (primeSetExponent T)*
        ∑' κ, χ κ*W (idealExponentNorm κ/(Z/idealExponentNorm (primeSetExponent T))) := by
  obtain ⟨B,_,hB⟩ := compactSupport_upper_cutoff W hW
  have hleft : (∑' ν, if ∀ p ∈ S, ν p = 0 then χ ν*W (idealExponentNorm ν/Z) else 0) =
      ∑ ν ∈ fullIdealBall (B*Z),
        if ∀ p ∈ S, ν p = 0 then χ ν*W (idealExponentNorm ν/Z) else 0 := by
    simpa only [ite_mul,zero_mul] using ideal_smooth_tsum_eq_ball
      (fun ν => if ∀ p ∈ S, ν p = 0 then χ ν else 0) W hZ hB
  rw [hleft,fullIdealBall_euler_exclusion S (B*Z) χ hχ W hZ]
  apply Finset.sum_congr rfl
  intro T hT
  have h := ideal_smooth_tsum_eq_ball χ W
    (div_pos hZ (idealExponentNorm_pos (primeSetExponent T))) hB
  have he : B*(Z/idealExponentNorm (primeSetExponent T)) =
      B*Z/idealExponentNorm (primeSetExponent T) := by ring
  simpa only [he] using congrArg (fun z : ℂ => (-1:ℂ)^T.card*χ (primeSetExponent T)*z) h.symm

@[simp] lemma idealExponentNorm_zero : idealExponentNorm 0 = 1 := by
  simp [idealExponentNorm,idealExponentGenerator,normNat,norm]

/-- The single local factor, applicable in particular to the prime above
three: the omitted factor is restored at exactly `Z/N(p)`. -/
theorem smooth_ideal_single_prime_exclusion (p : EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ0 : χ 0 = 1)
    (hχ : ∀ ν κ, χ (ν+κ) = χ ν*χ κ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    {Z : ℝ} (hZ : 0 < Z) :
    (∑' ν, if ν p = 0 then χ ν*W (idealExponentNorm ν/Z) else 0) =
      (∑' ν, χ ν*W (idealExponentNorm ν/Z)) -
      χ (Finsupp.single p 1)*
        ∑' ν, χ ν*W (idealExponentNorm ν/(Z/(normNat (idealPrimeRepresentative p):ℝ))) := by
  have h := smooth_ideal_euler_exclusion {p} χ hχ W hW hZ
  have hpowerset : ({p} : Finset EisensteinIdealPrime).powerset = {∅,{p}} := by
    ext T
    simp [Finset.mem_powerset,Finset.subset_singleton_iff]
  rw [hpowerset] at h
  simpa [primeSetExponent,hχ0,idealExponentNorm_single,sub_eq_add_neg,add_comm] using h

end CubicFirstMoment

end

end OAI
