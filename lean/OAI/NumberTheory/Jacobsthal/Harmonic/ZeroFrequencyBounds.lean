import OAI.NumberTheory.Jacobsthal.Partitions.DilationCoordinates

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

noncomputable def restrictionCount (H T : ℕ) [NeZero H] [NeZero T] (a : (ZMod T)ˣ) : ℝ :=
  (unitClass (H*T) T (dvd_mul_left T H) a).card

theorem restrictionCount_nonneg (H T : ℕ) [NeZero H] [NeZero T] (a : (ZMod T)ˣ) :
    0 ≤ restrictionCount H T a := Nat.cast_nonneg _

theorem restrictionCount_le_modulus (H T : ℕ) [NeZero H] [NeZero T] (a : (ZMod T)ˣ) :
    restrictionCount H T a ≤ (H*T : ℕ) := by
  have hphi : 1 ≤ T.totient := Nat.succ_le_iff.mpr (Nat.totient_pos.mpr (NeZero.pos T))
  have hn : (unitClass (H*T) T (dvd_mul_left T H) a).card ≤ H*T := by
    calc
      _ = 1*(unitClass (H*T) T (dvd_mul_left T H) a).card := by simp
      _ ≤ T.totient*(unitClass (H*T) T (dvd_mul_left T H) a).card :=
        Nat.mul_le_mul_right _ hphi
      _ = (H*T).totient := unitClass_card_mul_totient (H*T) T (dvd_mul_left T H) a
      _ ≤ H*T := Nat.totient_le _
  unfold restrictionCount
  exact_mod_cast hn

theorem restrictionCount_ratio (H T : ℕ) [NeZero H] [NeZero T] (a : (ZMod T)ˣ) :
    restrictionCount H T a = ((H*T).totient : ℝ)/(T.totient : ℝ) := by
  have ht : (T.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos T)).ne'
  apply (eq_div_iff ht).mpr
  have h : (T.totient : ℝ)*restrictionCount H T a = (H*T).totient := by
    unfold restrictionCount
    exact_mod_cast unitClass_card_mul_totient (H*T) T (dvd_mul_left T H) a
  simpa only [mul_comm] using h

theorem restricted_zero_eq_real (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) :
    restrictedSum (H*T) T (dvd_mul_left T H) a c 0 0 = (restrictionCount H T a : ℂ) := by
  simpa only [restrictionCount, Complex.ofReal_natCast] using
    restrictedSum_zero (H*T) T (dvd_mul_left T H) a c

private theorem product_approx_error (a b u v : ℝ) (ha0 : 0 ≤ a) (hv0 : 0 ≤ v)
    (ha : |a-u| ≤ 1) (hb : |b-v| ≤ 1) : |a*b-u*v| ≤ u+v+1 := by
  have hau : a ≤ u+1 := by have h := (abs_le.mp ha).2; linarith
  calc
    _ = |a*(b-v)+v*(a-u)| := by congr 1; ring
    _ ≤ |a*(b-v)|+|v*(a-u)| := abs_add_le _ _
    _ = a*|b-v|+v*|a-u| := by rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hv0]
    _ ≤ a*1+v*1 := add_le_add (mul_le_mul_of_nonneg_left hb ha0) (mul_le_mul_of_nonneg_left ha hv0)
    _ ≤ _ := by linarith

theorem product_count_error (P Q : ProgressionInterval) (hP : P.left ≤ P.right) (hQ : Q.left ≤ Q.right) :
    |(P.points.card : ℝ)*(Q.points.card : ℝ)-
      (intervalLength P/(P.step : ℝ))*(intervalLength Q/(Q.step : ℝ))| ≤
        intervalLength P+intervalLength Q+1 := by
  have h := product_approx_error (P.points.card : ℝ) (Q.points.card : ℝ)
    (intervalLength P/(P.step : ℝ)) (intervalLength Q/(Q.step : ℝ)) (Nat.cast_nonneg _)
    (div_nonneg (intervalLength_nonneg Q hQ) (Nat.cast_nonneg _))
    (interval_count_error P hP) (interval_count_error Q hQ)
  exact h.trans (by linarith [interval_average_le_length P hP, interval_average_le_length Q hQ])

theorem zero_frequency_rounding (H T : ℕ) [NeZero H] [NeZero T] (a : (ZMod T)ˣ)
    (P Q : ProgressionInterval) (hP : P.left ≤ P.right) (hQ : Q.left ≤ Q.right) :
    |(P.points.card : ℝ)*(Q.points.card : ℝ)*restrictionCount H T a/((H*T : ℕ) : ℝ)^2 -
      (intervalLength P/(P.step : ℝ))*(intervalLength Q/(Q.step : ℝ))*
        restrictionCount H T a/((H*T : ℕ) : ℝ)^2| ≤
      (intervalLength P+intervalLength Q+1)/((H*T : ℕ) : ℝ) := by
  have hN : (0 : ℝ) < (H*T : ℕ) := by exact_mod_cast Nat.mul_pos (NeZero.pos H) (NeZero.pos T)
  have hz0 := restrictionCount_nonneg H T a
  have hzN := restrictionCount_le_modulus H T a
  have hU := intervalLength_nonneg P hP
  have hV := intervalLength_nonneg Q hQ
  calc
    _ = |(P.points.card : ℝ)*(Q.points.card : ℝ)-
        (intervalLength P/(P.step : ℝ))*(intervalLength Q/(Q.step : ℝ))| *
        restrictionCount H T a/((H*T : ℕ) : ℝ)^2 := by
      rw [← sub_div, ← sub_mul, abs_div, abs_mul, abs_of_nonneg hz0, abs_of_nonneg (sq_nonneg (((H*T : ℕ) : ℝ)))]
    _ ≤ (intervalLength P+intervalLength Q+1)*((H*T : ℕ) : ℝ)/((H*T : ℕ) : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul (product_count_error P Q hP hQ) hzN hz0 (by linarith)
    _ = _ := by field_simp

end ErdosHyperbolaError

end

end Erdos970

end OAI
