import Mathlib
import OAI.Computability.QuantumFactoring.RetentionDenominators

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial

noncomputable def firstRetention (n d j : ℕ) : ℚ :=
  modeCoeff n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)

lemma first_remainder_bounds {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n) (j : ℕ) :
    0≤firstRetention n d j ∧ firstRetention n d j≤1 ∧
      0≤ modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j) ∧
      modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)≤2/(2:ℚ)^(10*n) := by
  have hB : 2≤2^n := by simpa using Nat.pow_le_pow_right (show 0<2 by decide) hn
  have hs := majorantSum_bounds hB hd hdB j
  have hsl : 1/(128*(d:ℚ))≤ majorantSum ((2^n)^16) (2^n) d j := by
    apply (Rat.cast_le (K:=ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_one] using hs.1
  have hsu : majorantSum ((2^n)^16) (2^n) d j≤2 := by exact_mod_cast hs.2
  have hc := modeCoeff_bounds n hd hsl hsu
  exact ⟨hc.1,by change modeCoeff n _ _≤1; linarith [hc.2.1],hc.2.2⟩

lemma all_retention_bounds {n d : ℕ} (hn : 1≤n) (hd : 0<d) (hdB : d<2^n) (j : ℕ)
    {t : ℕ} (ht : t<d) :
    (0≤firstRetention n d j ∧ firstRetention n d j≤1) ∧
      (0≤discrepancyRetention n d j t ∧ discrepancyRetention n d j t≤1) ∧
      (0≤remainderRetention n d j ∧ remainderRetention n d j≤1) := by
  have hc := first_remainder_bounds hn hd hdB j
  have hB : 2≤2^n := by simpa using Nat.pow_le_pow_right (show 0<2 by decide) hn
  have hc₀ : (0:ℝ)≤(firstRetention n d j:ℝ) := by exact_mod_cast hc.1
  have hc₁ : (firstRetention n d j:ℝ)≤1 := by exact_mod_cast hc.2.1
  have hdisc := discrepancy_retention_bounds hB hd hdB ht j hc₀ hc₁
  have hdc : (discrepancyRetention n d j t:ℝ)=
      2*((2^n:ℕ):ℝ)^3*((majorant ((2^n)^16) (2^n) d j ((j*t)%d):ℝ)-
        residueProbability ((2^n)^16) d j t)*(firstRetention n d j:ℝ) := by
    simp only [discrepancyRetention,firstRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
      Rat.cast_sub,residueProbabilityRat_cast (by positivity : 0<(2^n)^16),Nat.cast_pow,Nat.cast_ofNat]
  rw [← hdc] at hdisc
  have hr₀ : (0:ℝ)≤(modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j):ℝ) := by
    exact_mod_cast hc.2.2.1
  have hr₁ : (modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j):ℝ)≤
      2/(2:ℝ)^(10*n) := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hc.2.2.2
    simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hh
  have hrem := remainder_retention_bounds hn hr₀ hr₁
  have hrc : (remainderRetention n d j:ℝ)=
      4*((2:ℝ)^n)^2*(modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j):ℝ) := by
    simp only [remainderRetention,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat]
  rw [← hrc] at hrem
  exact ⟨⟨hc.1,hc.2.1⟩,by exact_mod_cast hdisc,by exact_mod_cast hrem⟩

end ExactQuantumFactoring.OrderTrial


end

end OAI
