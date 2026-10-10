import OAI.NumberTheory.CubicMoment.Estimates.IdealEulerExclusion
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerDivisors

namespace OAI

/-! The actual ramified Euler restriction in primary-element polynomials.
Prime-to-three ideals are identified arithmetically, then the complete
ideal-sum exclusion formula restores their missing local factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealPrime_dvd_iff {a : Eisenstein} (ha : a ≠ 0) (p : EisensteinIdealPrime) :
    idealPrimeRepresentative p ∣ a ↔ 0 < idealExponentOf a p := by
  constructor
  · intro hd
    have hle := idealExponentOf_le_of_dvd (idealPrimeRepresentative_irreducible p).ne_zero ha hd
    rw [idealExponentOf_primeRepresentative] at hle
    have h := hle p
    simp only [Finsupp.single_eq_same] at h
    omega
  · intro hp
    have hle : Finsupp.single p 1 ≤ idealExponentOf a :=
      Finsupp.single_le_iff.mpr (Nat.succ_le_iff.mpr hp)
    have hd := idealExponentGenerator_dvd_of_le hle
    have hsingle : idealExponentGenerator (Finsupp.single p 1) = idealPrimeRepresentative p := by
      simp [idealExponentGenerator,Finsupp.prod_single_index]
    rw [hsingle] at hd
    exact hd.trans (idealExponentOf_associated ha).dvd

/-- Coprimality is exactly disjoint prime-ideal support, with no omitted
ramified prime or assumption of squarefreeness. -/
lemma isCoprime_iff_idealExponent_disjoint {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsCoprime a b ↔ ∀ p : EisensteinIdealPrime, idealExponentOf a p = 0 ∨ idealExponentOf b p = 0 := by
  constructor
  · intro h p
    by_cases hpa : idealExponentOf a p = 0
    · exact Or.inl hpa
    · right
      by_contra hpb
      exact (idealPrimeRepresentative_irreducible p).not_isUnit
        (h.isRelPrime ((idealPrime_dvd_iff ha p).mpr (Nat.pos_of_ne_zero hpa))
          ((idealPrime_dvd_iff hb p).mpr (Nat.pos_of_ne_zero hpb)))
  · intro h
    apply IsRelPrime.isCoprime
    apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors ha).mpr
    intro d hda hdb hd
    let p : EisensteinIdealPrime := ⟨Associates.mk d,Associates.irreducible_mk.mpr hd.irreducible⟩
    have hassoc : Associated (idealPrimeRepresentative p) d := by
      apply Associates.mk_eq_mk_iff_associated.mp
      exact Associates.quotient_out p.val
    have hpa := (idealPrime_dvd_iff ha p).mp (hassoc.dvd.trans hda)
    have hpb := (idealPrime_dvd_iff hb p).mp (hassoc.dvd.trans hdb)
    rcases h p with h0 | h0
    · omega
    · omega

/-- All prime ideals dividing the rational integer three. -/
def ramifiedIdealPrimes : Finset EisensteinIdealPrime :=
  (idealExponentOf (3 : Eisenstein)).support

lemma idealGenerator_coprime_three_iff (ν : EisensteinIdealExponent) :
    IsCoprime (idealExponentGenerator ν) 3 ↔ ∀ p ∈ ramifiedIdealPrimes, ν p = 0 := by
  rw [isCoprime_iff_idealExponent_disjoint (idealExponentGenerator_ne_zero ν) (by norm_num),
    idealExponentOf_generator]
  constructor
  · intro h p hp
    rcases h p with hν | h3
    · exact hν
    · exact False.elim ((Finsupp.mem_support_iff.mp hp) h3)
  · intro h p
    by_cases hp : p ∈ ramifiedIdealPrimes
    · exact Or.inl (h p hp)
    · exact Or.inr (Finsupp.notMem_support_iff.mp hp)

/-- Primary normalization succeeds exactly on the ideals prime to three. -/
theorem idealPrimaryGenerator_primary_iff (ν : EisensteinIdealExponent) :
    primary (idealPrimaryGenerator ν) ↔ ∀ p ∈ ramifiedIdealPrimes, ν p = 0 := by
  rw [← idealGenerator_coprime_three_iff]
  constructor
  · intro h
    exact (primary_coprime_three h).of_isCoprime_of_dvd_left
      (primaryNormalize_associated (idealExponentGenerator ν)).dvd
  · intro h
    exact primaryNormalize_primary (residue_isUnit_of_isCoprime h.symm)

lemma primaryIdealBall_eq_full_filter (Y : ℝ) :
    primaryIdealBall Y = (fullIdealBall Y).filter (fun ν => ∀ p ∈ ramifiedIdealPrimes, ν p = 0) := by
  ext ν
  simp only [mem_primaryIdealBall,Finset.mem_filter,mem_fullIdealBall,
    idealPrimaryGenerator_primary_iff]
  exact and_comm

/-- The primary polynomial is the complete ideal polynomial with its
actual ramified Euler factors deleted. -/
theorem primaryIdealPolynomial_eq_ramified_filter (Y : ℝ) (A : EisensteinArithmeticFunction)
    (χ : Eisenstein → ℂ) :
    primaryIdealPolynomial Y A χ = ∑ ν ∈ fullIdealBall Y,
      if ∀ p ∈ ramifiedIdealPrimes, ν p = 0 then idealCharacterCoeff A χ ν else 0 := by
  rw [primaryIdealPolynomial,primaryIdealBall_eq_full_filter,Finset.sum_filter]

/-- Exact restoration of the missing ramified Euler factors for a
complete smooth Hecke-ideal character sum. -/
theorem primary_ideal_smooth_euler (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν κ, χ (ν+κ) = χ ν*χ κ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    {Z : ℝ} (hZ : 0 < Z) :
    (∑' ν, if primary (idealPrimaryGenerator ν) then χ ν*W (idealExponentNorm ν/Z) else 0) =
      ∑ T ∈ ramifiedIdealPrimes.powerset, (-1:ℂ)^T.card*χ (primeSetExponent T)*
        ∑' κ, χ κ*W (idealExponentNorm κ/(Z/idealExponentNorm (primeSetExponent T))) := by
  simpa only [idealPrimaryGenerator_primary_iff] using
    smooth_ideal_euler_exclusion ramifiedIdealPrimes χ hχ W hW hZ

lemma primaryIdealBall_sum_eq_elements (Y : ℝ) (f : EisensteinIdealExponent → ℂ) :
    (∑ ν ∈ primaryIdealBall Y, f ν) = ∑ a ∈ primaryElementBall Y, f (idealExponentOf a) := by
  unfold primaryIdealBall
  apply Finset.sum_image
  intro a ha b hb he
  exact idealExponentOf_inj_primary (mem_primaryElementBall.mp ha).1
    (mem_primaryElementBall.mp hb).1 he

lemma primary_ideal_smooth_tsum_eq_ball (χ : EisensteinIdealExponent → ℂ) (W : ℝ → ℂ)
    {B Z : ℝ} (hZ : 0 < Z) (hW : ∀ x : ℝ, B < x → W x = 0) :
    (∑' ν, if primary (idealPrimaryGenerator ν) then χ ν*W (idealExponentNorm ν/Z) else 0) =
      ∑ ν ∈ primaryIdealBall (B*Z), χ ν*W (idealExponentNorm ν/Z) := by
  have h := ideal_smooth_tsum_eq_ball
    (fun ν => if primary (idealPrimaryGenerator ν) then χ ν else 0) W hZ hW
  simp only [ite_mul,zero_mul] at h
  rw [h,primaryIdealBall_eq_full_filter,Finset.sum_filter]
  simp only [idealPrimaryGenerator_primary_iff]

lemma primary_element_smooth_tsum_eq_ball (χ : EisensteinIdealExponent → ℂ) (W : ℝ → ℂ)
    {B Z : ℝ} (hZ : 0 < Z) (hW : ∀ x : ℝ, B < x → W x = 0) :
    (∑' a : Eisenstein, if primary a then χ (idealExponentOf a)*W (norm a/Z) else 0) =
      ∑ a ∈ primaryElementBall (B*Z), χ (idealExponentOf a)*W (norm a/Z) := by
  calc
    _ = ∑ a ∈ primaryElementBall (B*Z),
        if primary a then χ (idealExponentOf a)*W (norm a/Z) else 0 := by
      apply tsum_eq_sum
      intro a ha
      by_cases hprim : primary a
      · have hN : B*Z < norm a := lt_of_not_ge (fun h => ha (mem_primaryElementBall.mpr ⟨hprim,h⟩))
        rw [ite_eq_left hprim,hW _ ((lt_div_iff₀ hZ).mpr hN),mul_zero]
      · rw [ite_eq_right hprim]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [ite_eq_left (mem_primaryElementBall.mp ha).1]

/-- The original primary-element smooth polynomial is exactly the smooth
ideal sum with the actual primes above three excluded. -/
theorem primary_element_ideal_smooth_eq (χ : EisensteinIdealExponent → ℂ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) :
    (∑' a : Eisenstein, if primary a then χ (idealExponentOf a)*W (norm a/Z) else 0) =
      ∑' ν, if primary (idealPrimaryGenerator ν) then χ ν*W (idealExponentNorm ν/Z) else 0 := by
  obtain ⟨B,_,hB⟩ := compactSupport_upper_cutoff W hW
  rw [primary_element_smooth_tsum_eq_ball χ W hZ hB,
    primary_ideal_smooth_tsum_eq_ball χ W hZ hB,primaryIdealBall_sum_eq_elements]
  apply Finset.sum_congr rfl
  intro a ha
  rw [idealExponentOf_norm (primary_ne_zero (mem_primaryElementBall.mp ha).1)]

/-- The actual primary-element sum with all omitted ramified factors
restored as complete ideal sums at the exact rescaled lengths. -/
theorem primary_element_smooth_euler (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν κ, χ (ν+κ) = χ ν*χ κ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    {Z : ℝ} (hZ : 0 < Z) :
    (∑' a : Eisenstein, if primary a then χ (idealExponentOf a)*W (norm a/Z) else 0) =
      ∑ T ∈ ramifiedIdealPrimes.powerset, (-1:ℂ)^T.card*χ (primeSetExponent T)*
        ∑' κ, χ κ*W (idealExponentNorm κ/(Z/idealExponentNorm (primeSetExponent T))) :=
  (primary_element_ideal_smooth_eq χ W hW hZ).trans (primary_ideal_smooth_euler χ hχ W hW hZ)

end CubicFirstMoment

end

end OAI
