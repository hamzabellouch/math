import OAI.NumberTheory.DirichletL.Detector.PrimePhase

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay QuadraticAllOddCRT
local notation "O" => ActualEisensteinCubic.O

lemma residue_one_mod_four : residue (1 : O) = (1, 0) := by
  have he : (1 : O) = eval 1 0 := by simp [eval]
  rw [he, residue_eval]
  norm_num

lemma odd_residue_one : EisensteinEPrimaryPhase.odd (residue (1 : O)) := by
  rw [residue_one_mod_four]
  decide

lemma odd_residue_pow (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) (n : ℕ) :
    EisensteinEPrimaryPhase.odd (residue (a ^ n)) := by
  induction n with
  | zero => simpa only [pow_zero] using odd_residue_one
  | succ n ih =>
    rw [pow_succ, residue_mul]
    exact odd_mul _ _ ih ha

lemma reciprocitySign_symm (a b : O) : reciprocitySign a b = reciprocitySign b a := by
  simp only [reciprocitySign, quadraticRaySign_symm]

lemma reciprocitySign_one_left (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    reciprocitySign 1 a = 1 := by
  have ht : ∀ r : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.odd r →
      quadraticRaySign (1, 0) r = 1 := by decide
  unfold reciprocitySign
  rw [residue_one_mod_four]
  exact_mod_cast ht (residue a) ha

lemma reciprocitySign_mul_left (a b c : O) :
    reciprocitySign (a * b) c = reciprocitySign a c * reciprocitySign b c := by
  simp only [reciprocitySign, residue_mul, quadraticRaySign_mul_left, Int.cast_mul]

lemma reciprocitySign_pow_left (a b : O)
    (hb : EisensteinEPrimaryPhase.odd (residue b)) (n : ℕ) :
    reciprocitySign (a ^ n) b = reciprocitySign a b ^ n := by
  induction n with
  | zero => simp only [pow_zero, reciprocitySign_one_left b hb]
  | succ n ih => rw [pow_succ, reciprocitySign_mul_left, ih, pow_succ]

lemma reciprocitySign_pow_right (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) (n : ℕ) :
    reciprocitySign a (b ^ n) = reciprocitySign a b ^ n := by
  rw [reciprocitySign_symm, reciprocitySign_pow_left b a ha n, reciprocitySign_symm b a]

lemma G_one : G (1 : O) = 1 := by
  have hq : quadraticRayValue (residue (1 : O)) = 1 := by
    rw [residue_one_mod_four]
    change breveGaussianFourTerms 1 0 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num
  have he := G_cube (1 : O) odd_residue_one (cubicTwo_isUnit_of_odd 1 odd_residue_one)
  simpa only [one_pow, hq] using he

theorem G_pow (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) (n : ℕ) :
    G (a ^ n) = G a ^ n * reciprocitySign a a ^ (n.choose 2) := by
  induction n with
  | zero => simp [G_one]
  | succ n ih =>
    rw [pow_succ, G_mul (a ^ n) a (odd_residue_pow a ha n) ha, ih,
      reciprocitySign_pow_left a a ha n, Nat.choose_succ_succ, Nat.choose_one_right,
      pow_add, pow_succ]
    ring

theorem reciprocitySign_cube_self (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    reciprocitySign (a ^ 3) (a ^ 3) = reciprocitySign a a := by
  rw [reciprocitySign_cube_right (a ^ 3) a (odd_residue_pow a ha 3) ha,
    reciprocitySign_symm, reciprocitySign_cube_right a a ha ha]

theorem G_cube_power (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) (l : ℕ) :
    G (a ^ (3 * l)) = G (a ^ 3) ^ l * reciprocitySign a a ^ (l.choose 2) := by
  rw [pow_mul, G_pow (a ^ 3) (odd_residue_pow a ha 3), reciprocitySign_cube_self a ha]

theorem G_completed_prime_power (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (e l : ℕ) (he : e ≤ 1) :
    G (a ^ (e + 3 * l)) =
      G a ^ e * G (a ^ 3) ^ l * reciprocitySign a a ^ (e * l + l.choose 2) := by
  have hc : e = 0 ∨ e = 1 := by omega
  rcases hc with rfl | rfl
  · simpa only [zero_add, zero_mul, pow_zero, one_mul] using G_cube_power a ha l
  · rw [pow_add, pow_one, G_mul a (a ^ (3 * l)) ha (odd_residue_pow a ha _),
      G_cube_power a ha l, pow_mul, reciprocitySign_pow_right a (a ^ 3) ha l,
      reciprocitySign_cube_right a a ha ha]
    simp only [pow_one, one_mul, pow_add]
    ring

end SevenEighths.ProbePhase
end

end OAI
