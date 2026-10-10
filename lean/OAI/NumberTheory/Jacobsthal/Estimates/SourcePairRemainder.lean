import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Harmonic.NormalizedSpectralError
import OAI.NumberTheory.Jacobsthal.Harmonic.ZeroFrequencyBounds
import OAI.NumberTheory.Jacobsthal.Sieve.EulerProductRatio

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaError

theorem source_restriction_divides (H T : ℕ) (hH : 0 < H) (hT : Squarefree T)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ T → p ∣ H) : T ∣ H := by
  apply (Nat.factorization_le_iff_dvd hT.ne_zero hH.ne').mp
  intro p
  by_cases hp : p.Prime
  · by_cases hz : T.factorization p = 0
    · rw [hz]
      exact Nat.zero_le _
    · have hpd : p ∣ T := (hp.dvd_iff_one_le_factorization hT.ne_zero).mpr (Nat.pos_of_ne_zero hz)
      exact (hT.natFactorization_le_one p).trans
        ((hp.dvd_iff_one_le_factorization hH.ne').mp (hsupport p hp hpd))
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

theorem source_dilation_coprime (H T T1 l : ℕ) (hTH : T ∣ H) (hl : l.Coprime (H*T1)) :
    l.Coprime (H*T) ∧ l.Coprime T1 := by
  obtain ⟨hlH, hlT1⟩ := Nat.coprime_mul_iff_right.mp hl
  have hlT : l.Coprime T := Nat.Coprime.of_dvd_right hTH hlH
  exact ⟨hlH.mul_right hlT, hlT1⟩

theorem source_product_coprime (H T : ℕ) (hTH : T ∣ H) (C0 k0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) :
    IsCoprime (C0+(H : ℤ)*k0) ((H*T : ℕ) : ℤ) := by
  have hCH : Int.gcd (C0+(H : ℤ)*k0) (H : ℤ) = 1 := by
    rw [add_comm C0, Int.gcd_mul_left_add_left]
    exact hC0
  have hcop : (C0+(H : ℤ)*k0).natAbs.Coprime H := by
    rw [Nat.coprime_iff_gcd_eq_one]
    simpa only [Int.gcd_def, Int.natAbs_natCast] using hCH
  have hdiv : H*T ∣ H^2 := by
    simpa only [pow_two] using Nat.mul_dvd_mul_left H hTH
  have hcopN : (C0+(H : ℤ)*k0).natAbs.Coprime (H*T) :=
    Nat.Coprime.of_dvd_right hdiv (hcop.pow_right 2)
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  simpa only [Int.gcd_def, Int.natAbs_natCast] using hcopN.gcd_eq_one

theorem source_totient_product (H T : ℕ) (hTH : T ∣ H) (hT : 0 < T) :
    (H*T).totient = T*H.totient := by
  have h := Nat.totient_gcd_mul_totient_mul H T
  rw [Nat.gcd_eq_right_iff_dvd.mpr hTH] at h
  have he : T.totient*(H*T).totient = T.totient*(T*H.totient) := by
    calc
      _ = H.totient*T.totient*T := h
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr hT) he

end ErdosHyperbolaError

end

section

namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def reducedProduct (N l : ℕ) (hlN : l.Coprime N) (c : (ZMod N)ˣ) : (ZMod N)ˣ :=
  (ZMod.unitOfCoprime l hlN)⁻¹*c

noncomputable def reducedClass (N T l : ℕ) (hT : T ∣ N) (hlN : l.Coprime N)
    (a : (ZMod T)ˣ) : (ZMod T)ˣ :=
  (ZMod.unitsMap hT (ZMod.unitOfCoprime l hlN))⁻¹*a

noncomputable def dilatedPairs (N T : ℕ) [NeZero N] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) (P Q : ProgressionInterval) (l : ℕ) : Finset (ℤ × ℤ) :=
  (hyperbolaPairs N T a c P.points Q.points).filter fun xy => (l : ℤ) ∣ xy.1

theorem mem_dilatePair_iff (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) (P Q : ProgressionInterval)
    (l : ℕ) (hl : 0 < l) (hlN : l.Coprime N) (hlP : l.Coprime P.step) (x y : ℤ) :
    dilatePair l (x,y) ∈ hyperbolaPairs N T a c P.points Q.points ↔
      (x,y) ∈ hyperbolaPairs N T (reducedClass N T l hT hlN a) (reducedProduct N l hlN c)
        (pulledInterval P l hlP).points Q.points := by
  have hprod : (((l : ℤ)*x : ℤ) : ZMod N)*(y : ZMod N) = (c : ZMod N) ↔
      (x : ZMod N)*(y : ZMod N) = (reducedProduct N l hlN c : ZMod N) := by
    simp only [Int.cast_mul, Int.cast_natCast, reducedProduct, Units.val_mul]
    rw [← ZMod.coe_unitOfCoprime l hlN, mul_assoc, unit_mul_eq_iff]
  have hmap : (ZMod.unitsMap hT (ZMod.unitOfCoprime l hlN) : ZMod T) = (l : ZMod T) := by
    change (ZMod.castHom hT (ZMod T)) (ZMod.unitOfCoprime l hlN : ZMod N) = _
    rw [ZMod.coe_unitOfCoprime, map_natCast]
  have hclass : (((l : ℤ)*x : ℤ) : ZMod T) = (a : ZMod T) ↔
      (x : ZMod T) = (reducedClass N T l hT hlN a : ZMod T) := by
    simp only [Int.cast_mul, Int.cast_natCast, reducedClass, Units.val_mul]
    rw [← hmap, unit_mul_eq_iff]
  simp only [hyperbolaPairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, dilatePair]
  rw [hprod, hclass, mem_pulledInterval_iff P l hl hlP x]

theorem reduced_pairs_image (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) (P Q : ProgressionInterval)
    (l : ℕ) (hl : 0 < l) (hlN : l.Coprime N) (hlP : l.Coprime P.step) :
    (hyperbolaPairs N T (reducedClass N T l hT hlN a) (reducedProduct N l hlN c)
      (pulledInterval P l hlP).points Q.points).image (dilatePair l) =
      dilatedPairs N T a c P Q l := by
  apply Finset.Subset.antisymm
  · intro xy hxy
    obtain ⟨⟨x,y⟩, hred, rfl⟩ := Finset.mem_image.mp hxy
    apply Finset.mem_filter.mpr
    exact ⟨(mem_dilatePair_iff N T hT a c P Q l hl hlN hlP x y).mpr hred, ⟨x,rfl⟩⟩
  · rintro ⟨p,m⟩ hpm
    obtain ⟨horig, hdiv⟩ := Finset.mem_filter.mp hpm
    obtain ⟨x, rfl⟩ := hdiv
    exact Finset.mem_image.mpr ⟨(x,m),
      (mem_dilatePair_iff N T hT a c P Q l hl hlN hlP x m).mp horig, rfl⟩

theorem dilatedPairs_card (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) (P Q : ProgressionInterval)
    (l : ℕ) (hl : 0 < l) (hlN : l.Coprime N) (hlP : l.Coprime P.step) :
    (dilatedPairs N T a c P Q l).card =
      (hyperbolaPairs N T (reducedClass N T l hT hlN a) (reducedProduct N l hlN c)
        (pulledInterval P l hlP).points Q.points).card := by
  rw [← reduced_pairs_image N T hT a c P Q l hl hlN hlP,
    Finset.card_image_of_injective _ (dilatePair_injective l hl)]

end ErdosHyperbolaError

end

section

namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def realIntervalIntegers (x y : ℝ) (lc rc : Bool) : Finset ℤ :=
  (Finset.Icc ⌈x⌉ ⌊y⌋).filter fun z : ℤ =>
    (if lc then x ≤ (z : ℝ) else x < (z : ℝ)) ∧
    (if rc then (z : ℝ) ≤ y else (z : ℝ) < y)

noncomputable def sourcePairs (H T0 T1 : ℕ) (C0 k0 p0 p1 m1 : ℤ) (l : ℕ)
    (x0 x1 y0 y1 : ℝ) (lcI rcI lcJ rcJ : Bool) : Finset (ℤ × ℤ) :=
  ((realIntervalIntegers x0 x1 lcI rcI).product (realIntervalIntegers y0 y1 lcJ rcJ)).filter
    (fun pm : ℤ × ℤ => (l : ℤ) ∣ pm.1 ∧ Int.ModEq (T0 : ℤ) pm.1 p0 ∧
      Int.ModEq (T1 : ℤ) pm.1 p1 ∧ Int.ModEq (T1 : ℤ) pm.2 m1 ∧
      Int.ModEq ((H*T0 : ℕ) : ℤ) (pm.1*pm.2) (C0+(H : ℤ)*k0))

def sourceInterval (x y : ℝ) (lc rc : Bool) (T : ℕ) (r : ℤ) (hT : 0 < T) : ProgressionInterval where
  left := x
  right := y
  leftClosed := lc
  rightClosed := rc
  step := T
  residue := r
  step_pos := hT

theorem sourceInterval_points (x y : ℝ) (lc rc : Bool) (T : ℕ) (r : ℤ) (hT : 0 < T) :
    (sourceInterval x y lc rc T r hT).points =
      (realIntervalIntegers x y lc rc).filter (fun z => Int.ModEq (T : ℤ) z r) := by
  change ErdosHyperbolaFourier.progressionPoints x y lc rc T r = _
  rw [ErdosHyperbolaFourier.progressionPoints_eq_literal_filter x y lc rc T r hT]
  simp only [realIntervalIntegers, Finset.filter_filter, and_assoc]

theorem sourcePairs_eq_dilated (H T0 T1 : ℕ) [NeZero H] [NeZero T0]
    (C0 k0 p0 p1 m1 : ℤ) (l : ℕ) (x0 x1 y0 y1 : ℝ) (lcI rcI lcJ rcJ : Bool)
    (hT1 : 0 < T1) (a : (ZMod T0)ˣ) (c : (ZMod (H*T0))ˣ)
    (ha : (a : ZMod T0) = (p0 : ZMod T0))
    (hc : (c : ZMod (H*T0)) = ((C0+(H : ℤ)*k0 : ℤ) : ZMod (H*T0))) :
    sourcePairs H T0 T1 C0 k0 p0 p1 m1 l x0 x1 y0 y1 lcI rcI lcJ rcJ =
      dilatedPairs (H*T0) T0 a c
        (sourceInterval x0 x1 lcI rcI T1 p1 hT1) (sourceInterval y0 y1 lcJ rcJ T1 m1 hT1) l := by
  have hprod (p m : ℤ) : (p : ZMod (H*T0))*(m : ZMod (H*T0)) = (c : ZMod (H*T0)) ↔
      Int.ModEq ((H*T0 : ℕ) : ℤ) (p*m) (C0+(H : ℤ)*k0) := by
    rw [hc, ← Int.cast_mul, ZMod.intCast_eq_intCast_iff]
  have hclass (p : ℤ) : (p : ZMod T0) = (a : ZMod T0) ↔ Int.ModEq (T0 : ℤ) p p0 := by
    rw [ha, ZMod.intCast_eq_intCast_iff]
  ext ⟨p,m⟩
  simp only [sourcePairs, dilatedPairs, hyperbolaPairs, sourceInterval_points, Finset.mem_filter,
    Finset.product_eq_sprod, Finset.mem_product]
  rw [hprod, hclass]
  tauto

end ErdosHyperbolaError

end

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def zeroDensity (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (P Q : ProgressionInterval) : ℝ :=
  (P.points.card : ℝ)*(Q.points.card : ℝ)*restrictionCount H T a/((H*T : ℕ) : ℝ)^2

noncomputable def mainDensity (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (P Q : ProgressionInterval) : ℝ :=
  (intervalLength P/(P.step : ℝ))*(intervalLength Q/(Q.step : ℝ))*
    restrictionCount H T a/((H*T : ℕ) : ℝ)^2

theorem count_minus_zero_density (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (P Q : ProgressionInterval) :
    ((hyperbolaPairs (H*T) T a c P.points Q.points).card : ℂ) - (zeroDensity H T a P Q : ℂ) =
      ((∑ h : ZMod (H*T), ∑ k : ZMod (H*T), spectralTerm H T a c P Q h k)-
        spectralTerm H T a c P Q 0 0)/((H*T : ℕ) : ℂ)^2 := by
  have hc : ((hyperbolaPairs (H*T) T a c P.points Q.points).card : ℂ) =
      (∑ h : ZMod (H*T), ∑ k : ZMod (H*T), spectralTerm H T a c P Q h k)/((H*T : ℕ) : ℂ)^2 :=
    interval_count_eq_fourier (H*T) T (dvd_mul_left T H) a c P Q
  have hz : spectralTerm H T a c P Q 0 0 =
      (((P.points.card : ℝ)*(Q.points.card : ℝ)*restrictionCount H T a : ℝ) : ℂ) := by
    rw [spectralTerm, weight_zero_eq_count, weight_zero_eq_count, restricted_zero_eq_real]
    push_cast
    rfl
  rw [hc, hz]
  unfold zeroDensity
  push_cast
  ring

theorem count_spectral_error (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (P Q : ProgressionInterval)
    (hP : P.left ≤ P.right) (hQ : Q.left ≤ Q.right)
    (hPN : P.step.Coprime (H*T)) (hQN : Q.step.Coprime (H*T)) :
    |((hyperbolaPairs (H*T) T a c P.points Q.points).card : ℝ)-zeroDensity H T a P Q| ≤
      8*errorBase (H*T) T*(1+intervalLength P/((H*T : ℕ) : ℝ)+intervalLength Q/((H*T : ℕ) : ℝ)) := by
  have h := normalized_spectral_error H T a c P Q hP hQ hPN hQN
  have hN : ‖((H*T : ℕ) : ℂ)‖ = ((H*T : ℕ) : ℝ) := by simp
  have he : ‖((hyperbolaPairs (H*T) T a c P.points Q.points).card : ℂ)-
      (zeroDensity H T a P Q : ℂ)‖ =
      ‖(∑ h : ZMod (H*T), ∑ k : ZMod (H*T), spectralTerm H T a c P Q h k)-
        spectralTerm H T a c P Q 0 0‖/((H*T : ℕ) : ℝ)^2 := by
    rw [count_minus_zero_density, norm_div, norm_pow, hN]
  rw [← he] at h
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

theorem count_error_base (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (P Q : ProgressionInterval)
    (hP : P.left ≤ P.right) (hQ : Q.left ≤ Q.right)
    (hPN : P.step.Coprime (H*T)) (hQN : Q.step.Coprime (H*T)) :
    |((hyperbolaPairs (H*T) T a c P.points Q.points).card : ℝ)-mainDensity H T a P Q| ≤
      16*errorBase (H*T) T*(1+intervalLength P/((H*T : ℕ) : ℝ)+intervalLength Q/((H*T : ℕ) : ℝ)) := by
  have hshape : 0 ≤ 1+intervalLength P/((H*T : ℕ) : ℝ)+intervalLength Q/((H*T : ℕ) : ℝ) := by
    have hU := intervalLength_nonneg P hP
    have hV := intervalLength_nonneg Q hQ
    positivity
  calc
    _ ≤ |((hyperbolaPairs (H*T) T a c P.points Q.points).card : ℝ)-zeroDensity H T a P Q| +
        |zeroDensity H T a P Q-mainDensity H T a P Q| := abs_sub_le _ _ _
    _ ≤ 8*errorBase (H*T) T*(1+intervalLength P/((H*T : ℕ) : ℝ)+intervalLength Q/((H*T : ℕ) : ℝ)) +
        (intervalLength P+intervalLength Q+1)/((H*T : ℕ) : ℝ) :=
      add_le_add (count_spectral_error H T a c P Q hP hQ hPN hQN)
        (zero_frequency_rounding H T a P Q hP hQ)
    _ ≤ 8*errorBase (H*T) T*(1+intervalLength P/((H*T : ℕ) : ℝ)+intervalLength Q/((H*T : ℕ) : ℝ)) +
        errorBase (H*T) T*(1+intervalLength P/((H*T : ℕ) : ℝ)+intervalLength Q/((H*T : ℕ) : ℝ)) :=
      add_le_add le_rfl (rounding_absorb (H*T) T _ _ (intervalLength_nonneg P hP) (intervalLength_nonneg Q hQ))
    _ ≤ _ := by nlinarith [mul_nonneg (errorBase_nonneg (H*T) T) hshape]

theorem mainDensity_explicit (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (P Q : ProgressionInterval) :
    mainDensity H T a P Q =
      (intervalLength P/(P.step : ℝ))*(intervalLength Q/(Q.step : ℝ))*((H*T).totient : ℝ)/
        (((H*T : ℕ) : ℝ)^2*(T.totient : ℝ)) := by
  unfold mainDensity
  rw [restrictionCount_ratio]
  field_simp

noncomputable def completionConstant : ℝ := 16*ErdosHyperbola.harmonicConstant^2

theorem completionConstant_pos : 0 < completionConstant := by
  have h := ErdosHyperbola.harmonicConstant_pos
  unfold completionConstant
  positivity

theorem hyperbola_count_error (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (P Q : ProgressionInterval)
    (hP : P.left ≤ P.right) (hQ : Q.left ≤ Q.right)
    (hPN : P.step.Coprime (H*T)) (hQN : Q.step.Coprime (H*T)) :
    |((hyperbolaPairs (H*T) T a c P.points Q.points).card : ℝ)-
      (intervalLength P/(P.step : ℝ))*(intervalLength Q/(Q.step : ℝ))*((H*T).totient : ℝ)/
        (((H*T : ℕ) : ℝ)^2*(T.totient : ℝ))| ≤
      completionConstant*((H*T).divisors.card : ℝ)^3 * (Real.log (2*((H*T : ℕ) : ℝ)))^2 *
        (((H*T : ℕ) : ℝ)^((3 : ℝ)/4)) * Real.sqrt T *
          (1+intervalLength P/((H*T : ℕ) : ℝ)+intervalLength Q/((H*T : ℕ) : ℝ)) := by
  have h := count_error_base H T a c P Q hP hQ hPN hQN
  rw [mainDensity_explicit, errorBase_explicit] at h
  unfold completionConstant
  convert h using 1; ring

end ErdosHyperbolaError

end

section

namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

theorem dilated_hyperbola_count_error (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (P Q : ProgressionInterval)
    (hP : P.left ≤ P.right) (hQ : Q.left ≤ Q.right)
    (hPN : P.step.Coprime (H*T)) (hQN : Q.step.Coprime (H*T))
    (l : ℕ) (hl : 0 < l) (hlN : l.Coprime (H*T)) (hlP : l.Coprime P.step) :
    |((dilatedPairs (H*T) T a c P Q l).card : ℝ)-
      (intervalLength P*intervalLength Q*((H*T).totient : ℝ))/
        ((l : ℝ)*(P.step : ℝ)*(Q.step : ℝ)*((H*T : ℕ) : ℝ)^2*(T.totient : ℝ))| ≤
      completionConstant*((H*T).divisors.card : ℝ)^3 * (Real.log (2*((H*T : ℕ) : ℝ)))^2 *
        (((H*T : ℕ) : ℝ)^((3 : ℝ)/4)) * Real.sqrt T *
          (1+intervalLength P/((l : ℝ)*((H*T : ℕ) : ℝ))+intervalLength Q/((H*T : ℕ) : ℝ)) := by
  have h := hyperbola_count_error H T
    (reducedClass (H*T) T l (dvd_mul_left T H) hlN a)
    (reducedProduct (H*T) l hlN c) (pulledInterval P l hlP) Q
    (pulledInterval_ordered P hP l hl hlP) hQ hPN hQN
  rw [← dilatedPairs_card (H*T) T (dvd_mul_left T H) a c P Q l hl hlN hlP,
    pulledInterval_length] at h
  change |((dilatedPairs (H*T) T a c P Q l).card : ℝ)-
      (intervalLength P/(l : ℝ)/(P.step : ℝ))*(intervalLength Q/(Q.step : ℝ))*((H*T).totient : ℝ)/
        (((H*T : ℕ) : ℝ)^2*(T.totient : ℝ))| ≤
      completionConstant*((H*T).divisors.card : ℝ)^3 * (Real.log (2*((H*T : ℕ) : ℝ)))^2 *
        (((H*T : ℕ) : ℝ)^((3 : ℝ)/4)) * Real.sqrt T *
          (1+(intervalLength P/(l : ℝ))/((H*T : ℕ) : ℝ)+intervalLength Q/((H*T : ℕ) : ℝ)) at h
  have hlR : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have hPR : (P.step : ℝ) ≠ 0 := by exact_mod_cast P.step_pos.ne'
  have hQR : (Q.step : ℝ) ≠ 0 := by exact_mod_cast Q.step_pos.ne'
  have hNR : ((H*T : ℕ) : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (H*T)
  have hTR : (T.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos T)).ne'
  have hdensity :
      (intervalLength P/(l : ℝ)/(P.step : ℝ))*(intervalLength Q/(Q.step : ℝ))*((H*T).totient : ℝ)/
        (((H*T : ℕ) : ℝ)^2*(T.totient : ℝ)) =
      (intervalLength P*intervalLength Q*((H*T).totient : ℝ))/
        ((l : ℝ)*(P.step : ℝ)*(Q.step : ℝ)*((H*T : ℕ) : ℝ)^2*(T.totient : ℝ)) := by
    field_simp
  rw [hdensity, div_div] at h
  exact h

theorem dilated_hyperbola_count_error_same_step (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (P Q : ProgressionInterval)
    (hP : P.left ≤ P.right) (hQ : Q.left ≤ Q.right) (hsteps : P.step = Q.step)
    (hPN : P.step.Coprime (H*T)) (hQN : Q.step.Coprime (H*T))
    (l : ℕ) (hl : 0 < l) (hlN : l.Coprime (H*T)) (hlP : l.Coprime P.step) :
    |((dilatedPairs (H*T) T a c P Q l).card : ℝ)-
      (intervalLength P*intervalLength Q*((H*T).totient : ℝ))/
        ((l : ℝ)*(P.step : ℝ)^2*((H*T : ℕ) : ℝ)^2*(T.totient : ℝ))| ≤
      completionConstant*((H*T).divisors.card : ℝ)^3 * (Real.log (2*((H*T : ℕ) : ℝ)))^2 *
        (((H*T : ℕ) : ℝ)^((3 : ℝ)/4)) * Real.sqrt T *
          (1+intervalLength P/((l : ℝ)*((H*T : ℕ) : ℝ))+intervalLength Q/((H*T : ℕ) : ℝ)) := by
  have h := dilated_hyperbola_count_error H T a c P Q hP hQ hPN hQN l hl hlN hlP
  have he : (l : ℝ)*(P.step : ℝ)*(Q.step : ℝ)*((H*T : ℕ) : ℝ)^2*(T.totient : ℝ) =
      (l : ℝ)*(P.step : ℝ)^2*((H*T : ℕ) : ℝ)^2*(T.totient : ℝ) := by
    rw [← hsteps]
    ring
  rw [he] at h
  exact h

end ErdosHyperbolaError

end

section

namespace ErdosHyperbolaError

theorem source_hyperbola_count_error (H T0 T1 : ℕ) (hH : 2 ≤ H) (hT0 : 0 < T0) (hT1 : 0 < T1)
    (hSF : Squarefree T0) (hsupport : ∀ p : ℕ, p.Prime → p ∣ T0 → p ∣ H)
    (hT1N : T1.Coprime (H*T0)) (C0 k0 p0 p1 m1 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (hp0 : Int.gcd p0 (T0 : ℤ) = 1)
    (_hp1 : Int.gcd p1 (T1 : ℤ) = 1) (l : ℕ) (hl : 0 < l) (hlHT1 : l.Coprime (H*T1))
    (x0 x1 y0 y1 : ℝ) (hx : x0 ≤ x1) (hy : y0 ≤ y1) (lcI rcI lcJ rcJ : Bool) :
    |((sourcePairs H T0 T1 C0 k0 p0 p1 m1 l x0 x1 y0 y1 lcI rcI lcJ rcJ).card : ℝ)-
      ((x1-x0)*(y1-y0)*((H*T0).totient : ℝ))/
        ((l : ℝ)*(T1 : ℝ)^2*((H*T0 : ℕ) : ℝ)^2*(T0.totient : ℝ))| ≤
      completionConstant*((H*T0).divisors.card : ℝ)^3 * (Real.log (2*((H*T0 : ℕ) : ℝ)))^2 *
        (((H*T0 : ℕ) : ℝ)^((3 : ℝ)/4)) * Real.sqrt T0 *
          (1+(x1-x0)/((l : ℝ)*((H*T0 : ℕ) : ℝ))+(y1-y0)/((H*T0 : ℕ) : ℝ)) := by
  let : NeZero H := ⟨by omega⟩
  let : NeZero T0 := ⟨hT0.ne'⟩
  have hTH : T0 ∣ H := source_restriction_divides H T0 (by omega) hSF hsupport
  obtain ⟨hlN, hlT1⟩ := source_dilation_coprime H T0 T1 l hTH hlHT1
  let a : (ZMod T0)ˣ := ZMod.unitOfIsCoprime p0 (Int.isCoprime_iff_gcd_eq_one.mpr hp0)
  let c : (ZMod (H*T0))ˣ := ZMod.unitOfIsCoprime (C0+(H : ℤ)*k0)
    (source_product_coprime H T0 hTH C0 k0 hC0)
  have h := dilated_hyperbola_count_error_same_step H T0 a c
    (sourceInterval x0 x1 lcI rcI T1 p1 hT1) (sourceInterval y0 y1 lcJ rcJ T1 m1 hT1)
    hx hy rfl hT1N hT1N l hl hlN hlT1
  rw [← sourcePairs_eq_dilated H T0 T1 C0 k0 p0 p1 m1 l x0 x1 y0 y1 lcI rcI lcJ rcJ hT1 a c rfl rfl] at h
  exact h

end ErdosHyperbolaError

end

section

namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem signed_squarefree_dvd_iff (d : ℕ) (hd : Squarefree d) (n : ℤ) :
    (d : ℤ) ∣ n ↔ ∀ t ∈ d.primeFactors,(t : ℤ) ∣ n := by
  simpa only [Int.natCast_dvd] using (SmallSieveFinite.squarefree_dvd_iff_primeFactors
    (x := n.natAbs) hd)

theorem sourcePairs_divisor_filter (H T0 T1 : ℕ) (C0 k0 p0 p1 m1 : ℤ)
    (d : ℕ) (hd : Squarefree d) (x0 x1 y0 y1 : ℝ) (lcI rcI lcJ rcJ : Bool) :
    (sourcePairs H T0 T1 C0 k0 p0 p1 m1 1 x0 x1 y0 y1 lcI rcI lcJ rcJ).filter
      (fun pm => ∀ t ∈ d.primeFactors,(t : ℤ) ∣ pm.1) =
        sourcePairs H T0 T1 C0 k0 p0 p1 m1 d x0 x1 y0 y1 lcI rcI lcJ rcJ := by
  ext pm
  simp only [sourcePairs,Finset.mem_filter,Nat.cast_one,one_dvd,true_and,
    ← signed_squarefree_dvd_iff d hd]
  tauto

theorem sourcePairs_intersection_mass (H T0 T1 : ℕ) (C0 k0 p0 p1 m1 : ℤ)
    (d : ℕ) (hd : Squarefree d) (x0 x1 y0 y1 : ℝ) (lcI rcI lcJ rcJ : Bool) :
    BonferroniBlocks.intersectionMass
      (sourcePairs H T0 T1 C0 k0 p0 p1 m1 1 x0 x1 y0 y1 lcI rcI lcJ rcJ) (fun _ => 1)
      (fun t pm => (t : ℤ) ∣ pm.1) d.primeFactors =
        ((sourcePairs H T0 T1 C0 k0 p0 p1 m1 d x0 x1 y0 y1 lcI rcI lcJ rcJ).card : ℝ) := by
  rw [← sourcePairs_divisor_filter H T0 T1 C0 k0 p0 p1 m1 d hd x0 x1 y0 y1 lcI rcI lcJ rcJ,
    Finset.card_filter,Nat.cast_sum]
  simp only [BonferroniBlocks.intersectionMass,BonferroniBlocks.intersectionValue,one_mul,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro pm _hpm
  split_ifs <;> rfl

end ErdosVarianceLargeCount

end

section

namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def sourceMain (H T0 T1 : ℕ) (U V : ℝ) : ℝ :=
  U*V*((H*T0).totient : ℝ)/
    ((T1 : ℝ)^2*((H*T0 : ℕ) : ℝ)^2*(T0.totient : ℝ))

noncomputable def hyperbolaEnvelope (H T0 : ℕ) : ℝ :=
  completionConstant*((H*T0).divisors.card : ℝ)^3*(Real.log (2*((H*T0 : ℕ) : ℝ)))^2*
    (((H*T0 : ℕ) : ℝ)^((3 : ℝ)/4))*Real.sqrt T0

theorem source_pair_remainder_bound (H T0 T1 : ℕ) (hH : 2 ≤ H) (hT0 : 0 < T0) (hT1 : 0 < T1)
    (hSF : Squarefree T0) (hsupport : ∀ t : ℕ,t.Prime → t ∣ T0 → t ∣ H)
    (hT1N : T1.Coprime (H*T0)) (C0 k0 p0 p1 m1 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (hp0 : Int.gcd p0 (T0 : ℤ) = 1)
    (hp1 : Int.gcd p1 (T1 : ℤ) = 1) (d : ℕ) (hd : Squarefree d) (hdHT1 : d.Coprime (H*T1))
    (x0 x1 y0 y1 : ℝ) (hx : x0 ≤ x1) (hy : y0 ≤ y1) (lcI rcI lcJ rcJ : Bool) :
    |FundamentalBlockEstimate.integerRemainder
      (sourcePairs H T0 T1 C0 k0 p0 p1 m1 1 x0 x1 y0 y1 lcI rcI lcJ rcJ) (fun _ => 1)
      (fun t pm => (t : ℤ) ∣ pm.1) (sourceMain H T0 T1 (x1-x0) (y1-y0)) (fun t => 1/(t : ℝ)) d| ≤
      hyperbolaEnvelope H T0*(1+(x1-x0)/((d : ℝ)*((H*T0 : ℕ) : ℝ))+(y1-y0)/((H*T0 : ℕ) : ℝ)) := by
  have herr := source_hyperbola_count_error H T0 T1 hH hT0 hT1 hSF hsupport hT1N
    C0 k0 p0 p1 m1 hC0 hp0 hp1 d (Nat.pos_of_ne_zero hd.ne_zero) hdHT1
    x0 x1 y0 y1 hx hy lcI rcI lcJ rcJ
  unfold FundamentalBlockEstimate.integerRemainder BonferroniBlocks.intersectionRemainder
  have hprod : (∏ t ∈ d.primeFactors,1/(t : ℝ)) = 1/(d : ℝ) := by
    simpa only [one_div] using SmallSieveFinite.reciprocal_primeFactors_product hd
  rw [sourcePairs_intersection_mass H T0 T1 C0 k0 p0 p1 m1 d hd x0 x1 y0 y1 lcI rcI lcJ rcJ,hprod]
  have he : sourceMain H T0 T1 (x1-x0) (y1-y0)*(1/(d : ℝ)) =
      ((x1-x0)*(y1-y0)*((H*T0).totient : ℝ))/
        ((d : ℝ)*(T1 : ℝ)^2*((H*T0 : ℕ) : ℝ)^2*(T0.totient : ℝ)) := by
    dsimp [sourceMain]
    ring
  rw [he]
  exact herr

end ErdosVarianceLargeCount

end

end Erdos970

end OAI
