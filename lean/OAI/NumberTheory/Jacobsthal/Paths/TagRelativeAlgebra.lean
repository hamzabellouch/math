import OAI.NumberTheory.Jacobsthal.Primes.TagSmallPrimeData

namespace OAI

namespace Erdos970


namespace ErdosStoppedTagSieve

open ErdosUnitLifts

lemma actualClasses_fraction_real (D : ℕ) (hD : 0 < D) (A B : ℤ) (a : ℕ → ℤ)
    (hB : IsUnit (B:ZMod D)) :
    ((actualClasses D A B a).card:ℝ)/((D*radical D).totient:ℝ)=1/(D:ℝ) := by
  rw [actualClasses_card D hD A B a hB,totient_lift_modulus D hD,Nat.cast_mul]
  have hd : (D:ℝ)≠0 := by exact_mod_cast hD.ne'
  have ht : ((radical D).totient:ℝ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (radical_pos D)).ne'
  field_simp

lemma actualClasses_card_le (D : ℕ) (hD : 0 < D) (A B : ℤ) (a : ℕ → ℤ)
    (hB : IsUnit (B:ZMod D)) : (actualClasses D A B a).card ≤ D := by
  rw [actualClasses_card D hD A B a hB]
  exact (Nat.totient_le _).trans (Nat.le_of_dvd hD (radical_dvd D))

lemma lift_modulus_bound {w Cs : ℝ} (hw : 0 < w) {D : ℕ} (hD : 0 < D)
    (hDw : (D:ℝ) ≤ w^Cs) : (D*radical D:ℕ) ≤ w^(2*Cs) := by
  have hrad : (radical D:ℝ) ≤ D := by exact_mod_cast Nat.le_of_dvd hD (radical_dvd D)
  rw [Nat.cast_mul]
  calc
    _ ≤ w^Cs*w^Cs := mul_le_mul hDw (hrad.trans hDw) (Nat.cast_nonneg _) (Real.rpow_nonneg hw.le _)
    _ = _ := by rw [← Real.rpow_add hw]; congr 1; ring

lemma relative_remainder_bound (A D B N W Z P L R C u e xi : ℝ)
    (_hA0 : 0 ≤ A) (hAD : A ≤ D) (hD : 0 < D) (hDB : D ≤ B)
    (hZ : 0 < Z) (hP : 0 < P) (hL : 0 < L) (hR : 0 < R)
    (hC : 0 ≤ C) (hu : 0 ≤ u) (he : 0 ≤ e) (hxi : 0 < xi)
    (hN : xi*R/(64*Z*L) ≤ N) (hW : 1/P ≤ W) :
    A*C*R*u*e ≤ (N/D)*W*((64*C/xi)*B^2*Z*P*u*L*e) := by
  have hN0 : 0 < N := (by positivity : 0 < xi*R/(64*Z*L)).trans_le hN
  have hB : 0 < B := hD.trans_le hDB
  have hAD' : A*D ≤ B^2 := by
    have hh := mul_le_mul (hAD.trans hDB) hDB hD.le hB.le
    simpa only [pow_two] using hh
  have hN' : xi*R ≤ 64*Z*L*N := by
    have hh := (div_le_iff₀ (show 0 < 64*Z*L by positivity)).mp hN
    nlinarith
  have hW' : 1 ≤ P*W := by
    have hh := (div_le_iff₀ hP).mp hW
    simpa only [mul_comm] using hh
  have hChain : A*D*(xi*R) ≤ B^2*(64*Z*L*N)*(P*W) := by
    calc
      _ ≤ B^2*(xi*R) := mul_le_mul_of_nonneg_right hAD' (by positivity)
      _ ≤ B^2*(64*Z*L*N) := mul_le_mul_of_nonneg_left hN' (sq_nonneg B)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hW'
  have hh := mul_le_mul_of_nonneg_right hChain (mul_nonneg (mul_nonneg hC hu) he)
  apply (mul_le_mul_iff_left₀ (mul_pos hD hxi)).mp
  have hleft : (A*C*R*u*e)*(D*xi)=(A*D*(xi*R))*(C*u*e) := by ring
  have hright : ((N/D)*W*((64*C/xi)*B^2*Z*P*u*L*e))*(D*xi)=
      (B^2*(64*Z*L*N)*(P*W))*(C*u*e) := by
    field_simp
  rw [hleft,hright]
  exact hh

end ErdosStoppedTagSieve


end Erdos970

end OAI
