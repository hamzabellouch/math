import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OAI.NumberTheory.Catalan.Energy.BarrierTailPairRational

namespace OAI


noncomputable section

namespace InternalCatalan

def barrierP2MainBase : ℂ := barrierComplex (92 / 1000) (92 / 100)

theorem barrierConjugatePair_neg_star_power_re (z r : ℂ) (k : ℕ) :
    ((barrierConjugatePair (-star z) r).map
      (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re =
      2 * (-1 : ℝ) ^ k * (r.re * (z ^ k).re + r.im * (z ^ k).im) := by
  rw [barrierConjugatePair_power_re]
  have hp : (-star z) ^ k = (((-1 : ℝ) ^ k : ℝ) : ℂ) * star (z ^ k) := by
    rw [Complex.ofReal_pow, neg_pow]
    simp only [Complex.ofReal_neg, Complex.ofReal_one, star_pow]
  rw [hp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

def barrierP2CoefficientFormula (k : ℕ) (x y : ℝ) : ℝ :=
  barrierFiniteCoeff barrierP2Finite k +
  (-9338452 / 100000000) * (85 / 100) ^ k +
  (-2141509 / 100000000) * (94 / 100) ^ k +
  2 * barrierAxisPhase (-66277922 / 200000000) (31907569 / 200000000) k * (7 / 10) ^ k +
  2 * barrierAxisPhase (-1231651 / 200000000) (-6002645 / 200000000) k * (85 / 100) ^ k +
  2 * ((-3225918 / 200000000) * x - (-8928234 / 200000000) * y) +
  2 * (-1) ^ k * ((-2105536 / 200000000) * x + (9091287 / 200000000) * y)

theorem barrierP2_eq_coefficientFormula (k : ℕ) (hk : k ≠ 0) :
    barrierP2 k = barrierP2CoefficientFormula k
      (barrierP2MainBase ^ k).re (barrierP2MainBase ^ k).im := by
  have ho : barrierComplex (-92 / 1000) (92 / 100) = -star barrierP2MainBase := by
    apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex, Complex.star_def]
  simp only [barrierP2, barrierTrial, ite_eq_right hk, barrierP2Tail,
    List.map_append, List.sum_append, Complex.add_re]
  rw [ho]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [barrierConjugatePair_neg_star_power_re]
  simp only [barrierConjugatePair_imaginary_power_re]
  simp only [barrierConjugatePair_power_re, barrierComplex_real_pow]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  change _ = barrierP2CoefficientFormula k
    ((barrierComplex (92 / 1000) (92 / 100)) ^ k).re
    ((barrierComplex (92 / 1000) (92 / 100)) ^ k).im
  norm_num [barrierP2CoefficientFormula, barrierP2MainBase, barrierComplex]
  ring





open scoped BigOperators

theorem barrierP2_exact_power_1 :
    barrierP2MainBase ^ 1 = barrierComplex (23 / 250) (23 / 25) := by
  norm_num [barrierP2MainBase, barrierComplex]

theorem barrierP2_norm_term_1 :
    barrierP2 1 ^ 2 / 1 < (32841741 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 1 (by norm_num), barrierP2_exact_power_1]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_2 :
    barrierP2MainBase ^ 2 = barrierComplex (-52371 / 62500) (529 / 3125) := by
  change barrierP2MainBase ^ (1 + 1) = _
  rw [pow_succ, barrierP2_exact_power_1]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_2 :
    barrierP2 2 ^ 2 / 2 < (17124183 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 2 (by norm_num), barrierP2_exact_power_2]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_3 :
    barrierP2MainBase ^ 3 = barrierComplex (-3637933 / 15625000) (-1180199 / 1562500) := by
  change barrierP2MainBase ^ (2 + 1) = _
  rw [pow_succ, barrierP2_exact_power_2]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_3 :
    barrierP2 3 ^ 2 / 3 < (1386970 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 3 (by norm_num), barrierP2_exact_power_3]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_4 :
    barrierP2MainBase ^ 4 = barrierComplex (2630785241 / 3906250000) (-27704259 / 97656250) := by
  change barrierP2MainBase ^ (3 + 1) = _
  rw [pow_succ, barrierP2_exact_power_3]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_4 :
    barrierP2 4 ^ 2 / 4 < (7952514 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 4 (by norm_num), barrierP2_exact_power_4]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_5 :
    barrierP2MainBase ^ 5 = barrierComplex (315387243343 / 976562500000) (11591853743 / 19531250000) := by
  change barrierP2MainBase ^ (4 + 1) = _
  rw [pow_succ, barrierP2_exact_power_4]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_5 :
    barrierP2 5 ^ 2 / 5 < (334056 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 5 (by norm_num), barrierP2_exact_power_5]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_6 :
    barrierP2MainBase ^ 6 = barrierComplex (-126052411447611 / 244140625000000) (4293484888667 / 12207031250000) := by
  change barrierP2MainBase ^ (5 + 1) = _
  rw [pow_succ, barrierP2_exact_power_5]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_6 :
    barrierP2 6 ^ 2 / 6 < (1082946 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 6 (by norm_num), barrierP2_exact_power_6]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_7 :
    barrierP2MainBase ^ 7 = barrierComplex (-22649235951163253 / 61035156250000000) (-2701705158416371 / 6103515625000000) := by
  change barrierP2MainBase ^ (6 + 1) = _
  rw [pow_succ, barrierP2_exact_power_6]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_7 :
    barrierP2 7 ^ 2 / 7 < (202802 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 7 (by norm_num), barrierP2_exact_power_7]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_8 :
    barrierP2MainBase ^ 8 = barrierComplex (5692989437480898481 / 15258789062500000000) (-72883955690041419 / 190734863281250000) := by
  change barrierP2MainBase ^ (7 + 1) = _
  rw [pow_succ, barrierP2_exact_power_7]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_8 :
    barrierP2 8 ^ 2 / 8 < (3030164 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 8 (by norm_num), barrierP2_exact_power_8]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_norm_block_8 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (0 + k + 1) ^ 2 / ((0 + k + 1 : ℕ) : ℝ)) ≤
      (63955376 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_1.le) barrierP2_norm_term_2.le) barrierP2_norm_term_3.le) barrierP2_norm_term_4.le) barrierP2_norm_term_5.le) barrierP2_norm_term_6.le) barrierP2_norm_term_7.le) barrierP2_norm_term_8.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_8 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (63955376 / 1000000000 : ℝ) := by
  simpa only [Nat.zero_add] using barrierP2_norm_block_8

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierP2_exact_power_9 :
    barrierP2MainBase ^ 9 = barrierComplex (1472003541758822774663 / 3814697265625000000000) (117528109215093043967 / 381469726562500000000) := by
  change barrierP2MainBase ^ (8 + 1) = _
  rw [pow_succ, barrierP2_exact_power_8]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_9 :
    barrierP2 9 ^ 2 / 9 < (106660 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 9 (by norm_num), barrierP2_exact_power_9]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_10 :
    barrierP2MainBase ^ 10 = barrierComplex (-236458569734261077306851 / 953674316406250000000000) (3655922797240006382849 / 9536743164062500000000) := by
  change barrierP2MainBase ^ (9 + 1) = _
  rw [pow_succ, barrierP2_exact_power_9]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_10 :
    barrierP2 10 ^ 2 / 10 < (490838 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 10 (by norm_num), barrierP2_exact_power_10]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_11 :
    barrierP2MainBase ^ 11 = barrierComplex (-89524771440408151583584573 / 238418579101562500000000000) (-4597684860522803310002303 / 23841857910156250000000000) := by
  change barrierP2MainBase ^ (10 + 1) = _
  rw [pow_succ, barrierP2_exact_power_10]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_11 :
    barrierP2 11 ^ 2 / 11 < (59971 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 11 (by norm_num), barrierP2_exact_power_11]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_12 :
    barrierP2MainBase ^ 12 = barrierComplex (8515605436073060126582851721 / 59604644775390625000000000000) (-541204123730352990638124537 / 1490116119384765625000000000) := by
  change barrierP2MainBase ^ (11 + 1) = _
  rw [pow_succ, barrierP2_exact_power_11]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_12 :
    barrierP2 12 ^ 2 / 12 < (962373 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 12 (by norm_num), barrierP2_exact_power_12]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_13 :
    barrierP2MainBase ^ 13 = barrierComplex (5174936863348927896782151329983 / 14901161193847656250000000000000) (146068145646487907772698132179 / 1490116119384765625000000000000) := by
  change barrierP2MainBase ^ (12 + 1) = _
  rw [pow_succ, barrierP2_exact_power_12]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_13 :
    barrierP2 13 ^ 2 / 13 < (33139 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 13 (by norm_num), barrierP2_exact_power_13]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_14 :
    barrierP2MainBase ^ 14 = barrierComplex (-216933187129896846251216223422091 / 3725290298461914062500000000000000) (61191557603447281752380768814863 / 186264514923095703125000000000000) := by
  change barrierP2MainBase ^ (13 + 1) = _
  rw [pow_succ, barrierP2_exact_power_13]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_14 :
    barrierP2 14 ^ 2 / 14 < (174740 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 14 (by norm_num), barrierP2_exact_power_14]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_15 :
    barrierP2MainBase ^ 15 = barrierComplex (-286470628279845123524729509687077893 / 931322574615478515625000000000000000) (-434930330845810500633691554644879 / 18626451492309570312500000000000000) := by
  change barrierP2MainBase ^ (14 + 1) = _
  rw [pow_succ, barrierP2_exact_power_14]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_15 :
    barrierP2 15 ^ 2 / 15 < (18967 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 15 (by norm_num), barrierP2_exact_power_15]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_16 :
    barrierP2MainBase ^ 16 = barrierComplex (-1587125645709617083781325844386683039 / 232830643653869628906250000000000000000) (-414927589905231628040103328224184539 / 1455191522836685180664062500000000000) := by
  change barrierP2MainBase ^ (15 + 1) = _
  rw [pow_succ, barrierP2_exact_power_15]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_16 :
    barrierP2 16 ^ 2 / 16 < (297779 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 16 (by norm_num), barrierP2_exact_power_16]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_norm_block_16 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (8 + k + 1) ^ 2 / ((8 + k + 1 : ℕ) : ℝ)) ≤
      (2144467 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_9.le) barrierP2_norm_term_10.le) barrierP2_norm_term_11.le) barrierP2_norm_term_12.le) barrierP2_norm_term_13.le) barrierP2_norm_term_14.le) barrierP2_norm_term_15.le) barrierP2_norm_term_16.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_16 :
    (∑ k ∈ Finset.range 16,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (66099843 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (8 + 8),
    barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierP2_norm_prefix_8 barrierP2_norm_block_16
  have hc : (63955376 / 1000000000 : ℝ) + 2144467 / 1000000000 =
      66099843 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierP2_exact_power_17 :
    barrierP2MainBase ^ 17 = barrierComplex (15232831418661202718948831984229097325303 / 58207660913467407226562500000000000000000) (-189197242936446432045728519207393620249 / 5820766091346740722656250000000000000000) := by
  change barrierP2MainBase ^ (16 + 1) = _
  rw [pow_succ, barrierP2_exact_power_16]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_17 :
    barrierP2 17 ^ 2 / 17 < (10260 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 17 (by norm_num), barrierP2_exact_power_17]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_18 :
    barrierP2MainBase ^ 18 = barrierComplex (785508781383034456240998729814274565054669 / 14551915228366851806640625000000000000000000) (173001793020834697299385689847749592608121 / 727595761418342590332031250000000000000000) := by
  change barrierP2MainBase ^ (17 + 1) = _
  rw [pow_succ, barrierP2_exact_power_17]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_18 :
    barrierP2 18 ^ 2 / 18 < (48895 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 18 (by norm_num), barrierP2_exact_power_18]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_19 :
    barrierP2MainBase ^ 19 = barrierComplex (-777741545924029815083631202513919811001099213 / 3637978807091712951660156250000000000000000000) (26024784450768188569314712518724796256230953 / 363797880709171295166015625000000000000000000) := by
  change barrierP2MainBase ^ (18 + 1) = _
  rw [pow_succ, barrierP2_exact_power_18]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_19 :
    barrierP2 19 ^ 2 / 19 < (6325 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 19 (by norm_num), barrierP2_exact_power_19]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_20 :
    barrierP2MainBase ^ 20 = barrierComplex (-77745059793019519456347356450887187042356473799 / 909494701772928237915039062500000000000000000000) (-864474275694250870491463963494474266956598499 / 4547473508864641189575195312500000000000000000) := by
  change barrierP2MainBase ^ (19 + 1) = _
  rw [pow_succ, barrierP2_exact_power_19]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_20 :
    barrierP2 20 ^ 2 / 20 < (82159 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 20 (by norm_num), barrierP2_exact_power_20]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_21 :
    barrierP2MainBase ^ 21 = barrierComplex (37977680306696091095111353122375410978029332056623 / 227373675443232059478759765625000000000000000000000) (-2185794542058804347922062621577863464774234206917 / 22737367544323205947875976562500000000000000000000) := by
  change barrierP2MainBase ^ (20 + 1) = _
  rw [pow_succ, barrierP2_exact_power_20]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_21 :
    barrierP2 21 ^ 2 / 21 < (3715 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 21 (by norm_num), barrierP2_exact_power_21]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_22 :
    barrierP2MainBase ^ 22 = barrierComplex (5900814093789260095408305151443720421475413313211429 / 56843418860808014869689941406250000000000000000000000) (411606686293328797592676840759171796402433625271619 / 2842170943040400743484497070312500000000000000000000) := by
  change barrierP2MainBase ^ (21 + 1) = _
  rw [pow_succ, barrierP2_exact_power_21]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_22 :
    barrierP2 22 ^ 2 / 22 < (7755 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 22 (by norm_num), barrierP2_exact_power_22]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_23 :
    barrierP2MainBase ^ 23 = barrierComplex (-1757672032792159486731922449008984693757260170045584533 / 14210854715202003717422485351562500000000000000000000000) (154652631726646106883654153158127472328446452966357341 / 1421085471520200371742248535156250000000000000000000000) := by
  change barrierP2MainBase ^ (22 + 1) = _
  rw [pow_succ, barrierP2_exact_power_22]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_23 :
    barrierP2 23 ^ 2 / 23 < (2457 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 23 (by norm_num), barrierP2_exact_power_23]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_24 :
    barrierP2MainBase ^ 24 = barrierComplex (-396127509725505714027238768590899834311843825733670328559 / 3552713678800500929355621337890625000000000000000000000000) (-4608680778063350967063771350571214511607839436602778177 / 44408920985006261616945266723632812500000000000000000000) := by
  change barrierP2MainBase ^ (23 + 1) = _
  rw [pow_succ, barrierP2_exact_power_23]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_24 :
    barrierP2 24 ^ 2 / 24 < (16454 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 24 (by norm_num), barrierP2_exact_power_24]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_norm_block_24 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (16 + k + 1) ^ 2 / ((16 + k + 1 : ℕ) : ℝ)) ≤
      (178020 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_17.le) barrierP2_norm_term_18.le) barrierP2_norm_term_19.le) barrierP2_norm_term_20.le) barrierP2_norm_term_21.le) barrierP2_norm_term_22.le) barrierP2_norm_term_23.le) barrierP2_norm_term_24.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_24 :
    (∑ k ∈ Finset.range 24,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (66277863 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (16 + 8),
    barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierP2_norm_prefix_16 barrierP2_norm_block_24
  have hc : (66099843 / 1000000000 : ℝ) + 178020 / 1000000000 =
      66277863 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierP2_exact_power_25 :
    barrierP2MainBase ^ 25 = barrierComplex (75688793592679026371346901172919650824411837641616700899943 / 888178419700125232338905334472656250000000000000000000000000) (-398357199474011520022649024243831986372330017928373149657 / 3552713678800500929355621337890625000000000000000000000000) := by
  change barrierP2MainBase ^ (24 + 1) = _
  rw [pow_succ, barrierP2_exact_power_24]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_25 :
    barrierP2 25 ^ 2 / 25 < (1416 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 25 (by norm_num), barrierP2_exact_power_25]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_26 :
    barrierP2MainBase ^ 26 = barrierComplex (24646381222387280007843297620997491185370448296638640225976189 / 222044604925031308084726333618164062500000000000000000000000000) (755893431467030491263977769018474288398691252724184779822957 / 11102230246251565404236316680908203125000000000000000000000000) := by
  change barrierP2MainBase ^ (25 + 1) = _
  rw [pow_succ, barrierP2_exact_power_25]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_26 :
    barrierP2 26 ^ 2 / 26 < (35 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 26 (by norm_num), barrierP2_exact_power_26]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_27 :
    barrierP2MainBase ^ 27 = barrierComplex (-2910243016633432819633901892202039429370459451708561261988149853 / 55511151231257827021181583404541015625000000000000000000000000000) (601637865962390842778538822657792114529860108448001225069308369 / 5551115123125782702118158340454101562500000000000000000000000000) := by
  change barrierP2MainBase ^ (26 + 1) = _
  rw [pow_succ, barrierP2_exact_power_26]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_27 :
    barrierP2 27 ^ 2 / 27 < (1122 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 27 (by norm_num), barrierP2_exact_power_27]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_28 :
    barrierP2MainBase ^ 28 = barrierComplex (-1450702681096067893242219035633568770294198816819699726685136695319 / 13877787807814456755295395851135253906250000000000000000000000000000) (-13274479616358491366918337649879422060333446223748220212283338533 / 346944695195361418882384896278381347656250000000000000000000000000) := by
  change barrierP2MainBase ^ (27 + 1) = _
  rw [pow_succ, barrierP2_exact_power_27]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_28 :
    barrierP2 28 ^ 2 / 28 < (1398 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 28 (by norm_num), barrierP2_exact_power_28]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_29 :
    barrierP2MainBase ^ 29 = barrierComplex (88759050805288559031077668559318601238301132471630532239248570511263 / 3469446951953614188823848962783813476562500000000000000000000000000000) (-34587413789914542750327524883360988546317249839437929973288211137373 / 346944695195361418882384896278381347656250000000000000000000000000000) := by
  change barrierP2MainBase ^ (28 + 1) = _
  rw [pow_succ, barrierP2_exact_power_28]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_29 :
    barrierP2 29 ^ 2 / 29 < (550 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 29 (by norm_num), barrierP2_exact_power_29]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_30 :
    barrierP2MainBase ^ 30 = barrierComplex (81592509885325085183468093608594601485010600677554741180065602737716949 / 867361737988403547205962240695953369140625000000000000000000000000000000) (124594765135360237445725330454702509191562930054042985211708826559947 / 8673617379884035472059622406959533691406250000000000000000000000000000) := by
  change barrierP2MainBase ^ (29 + 1) = _
  rw [pow_succ, barrierP2_exact_power_29]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_30 :
    barrierP2 30 ^ 2 / 30 < (1356 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 30 (by norm_num), barrierP2_exact_power_30]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_31 :
    barrierP2MainBase ^ 31 = barrierComplex (-989051870750808502031916447460481877250703575659229612727794147911291173 / 216840434497100886801490560173988342285156250000000000000000000000000000000) (1905284523343609813832282979002257411269303289496188933740201893076277637 / 21684043449710088680149056017398834228515625000000000000000000000000000000) := by
  change barrierP2MainBase ^ (30 + 1) = _
  rw [pow_succ, barrierP2_exact_power_30]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_31 :
    barrierP2 31 ^ 2 / 31 < (577 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 31 (by norm_num), barrierP2_exact_power_31]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_32 :
    barrierP2MainBase ^ 32 = barrierComplex (-4404902596717571167360984929996783129096163748081396828695203619477398262079 / 54210108624275221700372640043497085571289062500000000000000000000000000000000) (658542219051075942856513444545651165075868544320314511977668066837334021 / 169406589450860067813664500135928392410278320312500000000000000000000000000) := by
  change barrierP2MainBase ^ (31 + 1) = _
  rw [pow_succ, barrierP2_exact_power_31]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_32 :
    barrierP2 32 ^ 2 / 32 < (69 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 32 (by norm_num), barrierP2_exact_power_32]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_norm_block_32 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (24 + k + 1) ^ 2 / ((24 + k + 1 : ℕ) : ℝ)) ≤
      (6523 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_25.le) barrierP2_norm_term_26.le) barrierP2_norm_term_27.le) barrierP2_norm_term_28.le) barrierP2_norm_term_29.le) barrierP2_norm_term_30.le) barrierP2_norm_term_31.le) barrierP2_norm_term_32.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_32 :
    (∑ k ∈ Finset.range 32,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (66284386 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (24 + 8),
    barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierP2_norm_prefix_24 barrierP2_norm_block_32
  have hc : (66277863 / 1000000000 : ℝ) + 6523 / 1000000000 =
      66284386 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierP2_exact_power_33 :
    barrierP2MainBase ^ 33 = barrierComplex (-149781467046663326243542042908485937718795691067847275141546052967207943973417 / 13552527156068805425093160010874271392822265625000000000000000000000000000000000) (-100828072651282544955360259494740412711715926957252375579174119550787882188361 / 1355252715606880542509316001087427139282226562500000000000000000000000000000000) := by
  change barrierP2MainBase ^ (32 + 1) = _
  rw [pow_succ, barrierP2_exact_power_32]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_33 :
    barrierP2 33 ^ 2 / 33 < (220 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 33 (by norm_num), barrierP2_exact_power_33]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_34 :
    barrierP2MainBase ^ 34 = barrierComplex (228459593355876596893727129851007772669414331107119976503844915748566346321841709 / 3388131789017201356273290002718567848205566406250000000000000000000000000000000000) (-2882009706526377518787376477637103029950883607288645983288281983956952000860447 / 169406589450860067813664500135928392410278320312500000000000000000000000000000000) := by
  change barrierP2MainBase ^ (33 + 1) = _
  rw [pow_succ, barrierP2_exact_power_33]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_34 :
    barrierP2 34 ^ 2 / 34 < (2707 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 34 (by norm_num), barrierP2_exact_power_34]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_35 :
    barrierP2MainBase ^ 35 = barrierComplex (18511815297206498314977655783703852709170594208991530982714530188419005169360415507 / 847032947254300339068322500679641962051391601562500000000000000000000000000000000000) (1024399640136989672538300933720374406403757793905696348871434418191001234672555749 / 16940658945086006781366450013592839241027832031250000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (34 + 1) = _
  rw [pow_succ, barrierP2_exact_power_34]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_35 :
    barrierP2 35 ^ 2 / 35 < (315 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 35 (by norm_num), barrierP2_exact_power_35]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_36 :
    barrierP2MainBase ^ 36 = barrierComplex (-11354824109739631772945974654759117061332290963108702799419061614862877079839101556839 / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000) (135894427612875818396597672600757917261838953276490073180662288106400565220658366949 / 5293955920339377119177015629247762262821197509765625000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (35 + 1) = _
  rw [pow_succ, barrierP2_exact_power_35]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_36 :
    barrierP2 36 ^ 2 / 36 < (659 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 36 (by norm_num), barrierP2_exact_power_36]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_37 :
    barrierP2MainBase ^ 37 = barrierComplex (-1511389688562469060026456004986432531219561062295208837648731467720731372866356311738097 / 52939559203393771191770156292477622628211975097656250000000000000000000000000000000000000) (-248658667183626955485270431180189964022553508450063077654017486636057320835998766047989 / 5293955920339377119177015629247762262821197509765625000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (36 + 1) = _
  rw [pow_succ, barrierP2_exact_power_36]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_37 :
    barrierP2 37 ^ 2 / 37 < (94 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 37 (by norm_num), barrierP2_exact_power_37]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_38 :
    barrierP2MainBase ^ 38 = barrierComplex (537152971685405209235513503599748969033823165002355275338319395505355016346870966740398469 / 13234889800848442797942539073119405657052993774414062500000000000000000000000000000000000000) (-20240556091080104178384854015916158695284317563570627025981612975103069977577083394539989 / 661744490042422139897126953655970282852649688720703125000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (37 + 1) = _
  rw [pow_succ, barrierP2_exact_power_37]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_38 :
    barrierP2 38 ^ 2 / 38 < (2571 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 38 (by norm_num), barrierP2_exact_power_38]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_39 :
    barrierP2MainBase ^ 39 = barrierComplex (105461076367732799032987139056008556286085793587479055652296765782097287272832615849913114187 / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000) (11423452768574635020211107298062082987794854187129922489586191899768424157009486398880325293 / 330872245021211069948563476827985141426324844360351562500000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (38 + 1) = _
  rw [pow_succ, barrierP2_exact_power_38]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_39 :
    barrierP2 39 ^ 2 / 39 < (174 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 39 (by norm_num), barrierP2_exact_power_39]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_40 :
    barrierP2MainBase ^ 40 = barrierComplex (-23848336611263806168726842587254594077348191377886803446045415756479137953846668552876746547599 / 827180612553027674871408692069962853565812110900878906250000000000000000000000000000000000000000) (67208604253376774580588991653590617582481372470400162431582700667072784072159208793056227701 / 2067951531382569187178521730174907133914530277252197265625000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (39 + 1) = _
  rw [pow_succ, barrierP2_exact_power_39]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_40 :
    barrierP2 40 ^ 2 / 40 < (738 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 40 (by norm_num), barrierP2_exact_power_40]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_norm_block_40 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (32 + k + 1) ^ 2 / ((32 + k + 1 : ℕ) : ℝ)) ≤
      (7478 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_33.le) barrierP2_norm_term_34.le) barrierP2_norm_term_35.le) barrierP2_norm_term_36.le) barrierP2_norm_term_37.le) barrierP2_norm_term_38.le) barrierP2_norm_term_39.le) barrierP2_norm_term_40.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_40 :
    (∑ k ∈ Finset.range 40,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (66291864 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (32 + 8),
    barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierP2_norm_prefix_32 barrierP2_norm_block_40
  have hc : (66284386 / 1000000000 : ℝ) + 7478 / 1000000000 =
      66291864 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierP2_exact_power_41 :
    barrierP2MainBase ^ 41 = barrierComplex (-6731703333369730803294904611637192481367294668968211422964653023769716307577120585677338119086777 / 206795153138256918717852173017490713391453027725219726562500000000000000000000000000000000000000000) (-486679826145960909266575507185552295603125539018628329821988477785313211592086904626553441109857 / 20679515313825691871785217301749071339145302772521972656250000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (40 + 1) = _
  rw [pow_succ, barrierP2_exact_power_40]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_41 :
    barrierP2 41 ^ 2 / 41 < (44 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 41 (by norm_num), barrierP2_exact_power_41]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_42 :
    barrierP2MainBase ^ 42 = barrierComplex (964534423468206282837340860459114852815740962356576295862386479359516911587526107170494137813675229 / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000) (-83011406334430454694457021366461564935159832391848657157046377267882839470445886138494752942261291 / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (41 + 1) = _
  rw [pow_succ, barrierP2_exact_power_41]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_42 :
    barrierP2 42 ^ 2 / 42 < (1705 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 42 (by norm_num), barrierP2_exact_power_42]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_43 :
    barrierP2MainBase ^ 43 = barrierComplex (404036760878148836099761138076282840316497271136705077727248224457529950530564176701997228704116468867 / 12924697071141057419865760813593169586965814232826232910156250000000000000000000000000000000000000000000) (18365767048384943589313816807702409627744689844176216575610755670946278350872589702550606534370510881 / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (42 + 1) = _
  rw [pow_succ, barrierP2_exact_power_42]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_43 :
    barrierP2 43 ^ 2 / 43 < (95 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 43 (by norm_num), barrierP2_exact_power_43]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_44 :
    barrierP2MainBase ^ 44 = barrierComplex (-32948418711087947025127272481961036816533349405461081336178028880653251344803980251720458768857496242359 / 3231174267785264354966440203398292396741453558206558227539062500000000000000000000000000000000000000000000) (2428814535577569233212180990582915187179391275640067442241439135738738316068261406826150052621300133551 / 80779356694631608874161005084957309918536338955163955688476562500000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (43 + 1) = _
  rw [pow_succ, barrierP2_exact_power_43]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_44 :
    barrierP2 44 ^ 2 / 44 < (455 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 44 (by norm_num), barrierP2_exact_power_44]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_45 :
    barrierP2MainBase ^ 45 = barrierComplex (-23102907357668659727129992380447923568830666772214225339353334713051417288758496488590151035799683642243457 / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000) (-106872538616377282424481323190295129911952607793343733209176452753412171170442299272312949368512560257513 / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (44 + 1) = _
  rw [pow_succ, barrierP2_exact_power_44]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_45 :
    barrierP2 45 ^ 2 / 45 < (23 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 45 (by norm_num), barrierP2_exact_power_45]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_46 :
    barrierP2MainBase ^ 46 = barrierComplex (697667324861959574157545391938091751904349653862525749100402508264057370818641022394025443914501719189799989 / 201948391736579022185402512712393274796340847387909889221191406250000000000000000000000000000000000000000000000) (-271828605583631280601402588458593091011489942828580856062090995233412498663023141826944731500385834100606753 / 10097419586828951109270125635619663739817042369395494461059570312500000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (45 + 1) = _
  rw [pow_succ, barrierP2_exact_power_45]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_46 :
    barrierP2 46 ^ 2 / 46 < (870 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 46 (by norm_num), barrierP2_exact_power_46]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_47 :
    barrierP2MainBase ^ 47 = barrierComplex (1266457934156528960972075450924104328946653779050310030114927835763770813378735195919008350111808376404156463547 / 50487097934144755546350628178098318699085211846977472305297851562500000000000000000000000000000000000000000000000) (3542232614978031297959024945480828107271504668723372850453071909336344590329678991023127561015791172737489109 / 5048709793414475554635062817809831869908521184697747230529785156250000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (46 + 1) = _
  rw [pow_succ, barrierP2_exact_power_46]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_47 :
    barrierP2 47 ^ 2 / 47 < (50 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 47 (by norm_num), barrierP2_exact_power_47]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_48 :
    barrierP2MainBase ^ 48 = barrierComplex (20981397471150694117051977996648494919048576180093373136601274831093136149952647826783998662235272959999373710881 / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000) (1825625239734041301388174559062528663265017595346110516762735054780091539580530757683170249154684740891785056943 / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (47 + 1) = _
  rw [pow_succ, barrierP2_exact_power_47]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_48 :
    barrierP2 48 ^ 2 / 48 < (181 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 48 (by norm_num), barrierP2_exact_power_48]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_norm_block_48 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (40 + k + 1) ^ 2 / ((40 + k + 1 : ℕ) : ℝ)) ≤
      (3423 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_41.le) barrierP2_norm_term_42.le) barrierP2_norm_term_43.le) barrierP2_norm_term_44.le) barrierP2_norm_term_45.le) barrierP2_norm_term_46.le) barrierP2_norm_term_47.le) barrierP2_norm_term_48.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_48 :
    (∑ k ∈ Finset.range 48,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (66295287 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (40 + 8),
    barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierP2_norm_prefix_40 barrierP2_norm_block_48
  have hc : (66291864 / 1000000000 : ℝ) + 3423 / 1000000000 =
      66295287 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierP2_exact_power_49 :
    barrierP2MainBase ^ 49 = barrierComplex (-66700436680376253926392628279578139425014530256594719434726820694792226525114620982724633199660987186737704500152137 / 3155443620884047221646914261131144918692825740436092019081115722656250000000000000000000000000000000000000000000000000) (1154402230058593163603043731657925931219643727229516252310515821274215818014546218843438620920335262728162496305287 / 315544362088404722164691426113114491869282574043609201908111572265625000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (48 + 1) = _
  rw [pow_succ, barrierP2_exact_power_48]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_49 :
    barrierP2 49 ^ 2 / 49 < (14 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 49 (by norm_num), barrierP2_exact_power_49]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_50 :
    barrierP2MainBase ^ 50 = barrierComplex (-4189235172783418116594031033243526848580514768529565927312903264910917591511092585942575391708973809569740945005659251 / 788860905221011805411728565282786229673206435109023004770278930664062500000000000000000000000000000000000000000000000000) (-30151175847146123950883208892043298207145647803507993463911500241818284925266034391385349506220699885044389321769551 / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (49 + 1) = _
  rw [pow_succ, barrierP2_exact_power_49]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_50 :
    barrierP2 50 ^ 2 / 50 < (346 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 50 (by norm_num), barrierP2_exact_power_50]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_51 :
    barrierP2MainBase ^ 51 = barrierComplex (3371032813447785637669906308820378176304397657727239232021625752716151661800838825532635959206074089160000730268368202227 / 197215226305252951352932141320696557418301608777255751192569732666015625000000000000000000000000000000000000000000000000000) (-131026261198236659225178403990450910455569334650214208811695000371042132268811069026772385941460202487905089455165146423 / 19721522630525295135293214132069655741830160877725575119256973266601562500000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (50 + 1) = _
  rw [pow_succ, barrierP2_exact_power_50]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_51 :
    barrierP2 51 ^ 2 / 51 < (26 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 51 (by norm_num), barrierP2_exact_power_51]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_52 :
    barrierP2MainBase ^ 52 = barrierComplex (378894155465243385884318174280905792102810615823219182603395893165868392439684751748827114727098169772861722543052305424121 / 49303806576313237838233035330174139354575402194313937798142433166503906250000000000000000000000000000000000000000000000000000) (18630037675434906626057185452772081778630762857692893883457101825984379794809159599908715546271529848364549934675917570873 / 1232595164407830945955825883254353483864385054857848444953560829162597656250000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (51 + 1) = _
  rw [pow_succ, barrierP2_exact_power_51]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_52 :
    barrierP2 52 ^ 2 / 52 < (40 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 52 (by norm_num), barrierP2_exact_power_52]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_53 :
    barrierP2MainBase ^ 53 = barrierComplex (-162681781038300543084386788157042319145038374126840582527927231256241321086131519028937159386974816700178039780528238627276817 / 12325951644078309459558258832543534838643850548578484449535608291625976562500000000000000000000000000000000000000000000000000000) (10428529041840609284936579070115864741998674346841787437156158910805535967235191973414625468980238650825358212480387441275099 / 1232595164407830945955825883254353483864385054857848444953560829162597656250000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (52 + 1) = _
  rw [pow_succ, barrierP2_exact_power_52]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_53 :
    barrierP2 53 ^ 2 / 53 < (9 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 53 (by norm_num), barrierP2_exact_power_53]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_54 :
    barrierP2MainBase ^ 54 = barrierComplex (-27727297760114313846295027988878462246932833602653444503601491813746283109621966476519193244554969681002418803657040603360094491 / 3081487911019577364889564708135883709660962637144621112383902072906494140625000000000000000000000000000000000000000000000000000000) (-1750912397959289238693677404499654225634956547469986143543867331972511528867307761138509140056937647567555838032550288639019757 / 154074395550978868244478235406794185483048131857231055619195103645324707031250000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (53 + 1) = _
  rw [pow_succ, barrierP2_exact_power_53]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_54 :
    barrierP2 54 ^ 2 / 54 < (102 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 54 (by norm_num), barrierP2_exact_power_54]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_55 :
    barrierP2MainBase ^ 55 = barrierComplex (7416469182130101279526130416954204806241344945500907036718955415357388521268310472277200599637148876147701222465619393862208708907 / 770371977754894341222391177033970927415240659286155278095975518226623535156250000000000000000000000000000000000000000000000000000000) (-143653963757751304688938960870237745211732634808929717237170441797380008369840277194462573013476686890232640206721849430935416423 / 15407439555097886824447823540679418548304813185723105561919510364532470703125000000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (54 + 1) = _
  rw [pow_succ, barrierP2_exact_power_54]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_55 :
    barrierP2 55 ^ 2 / 55 < (13 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 55 (by norm_num), barrierP2_exact_power_55]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_56 :
    barrierP2MainBase ^ 56 = barrierComplex (1822599374403132333351899049597680780478476234049212610071996055223090032242334328598695203446636323389072490494010514514588089169361 / 192592994438723585305597794258492731853810164821538819523993879556655883789062500000000000000000000000000000000000000000000000000000000) (19257323169606366173734127386233671230525210092936743045282671718315154378329938623126552236888075644877546811617029171784153427027 / 2407412430484044816319972428231159148172627060269235244049923494458198547363281250000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (55 + 1) = _
  rw [pow_succ, barrierP2_exact_power_55]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_56 :
    barrierP2 56 ^ 2 / 56 < (2 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 56 (by norm_num), barrierP2_exact_power_56]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_norm_block_56 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (48 + k + 1) ^ 2 / ((48 + k + 1 : ℕ) : ℝ)) ≤
      (552 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_49.le) barrierP2_norm_term_50.le) barrierP2_norm_term_51.le) barrierP2_norm_term_52.le) barrierP2_norm_term_53.le) barrierP2_norm_term_54.le) barrierP2_norm_term_55.le) barrierP2_norm_term_56.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_56 :
    (∑ k ∈ Finset.range 56,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (66295839 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (48 + 8),
    barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierP2_norm_prefix_48 barrierP2_norm_block_56
  have hc : (66295287 / 1000000000 : ℝ) + 552 / 1000000000 =
      66295839 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierP2_exact_power_57 :
    barrierP2MainBase ^ 57 = barrierComplex (-312414960709485093929614265765952892690658912326904182001545250346867769819697181107758571479467956427798194052391094926992897006401497 / 48148248609680896326399448564623182963452541205384704880998469889163970947265625000000000000000000000000000000000000000000000000000000000) (45463133074479615043060757579813653457421592040232250751987920866301059147186398264425275290860041356606135894699775201443810281468271 / 4814824860968089632639944856462318296345254120538470488099846988916397094726562500000000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (56 + 1) = _
  rw [pow_succ, barrierP2_exact_power_56]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_57 :
    barrierP2 57 ^ 2 / 57 < (6 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 57 (by norm_num), barrierP2_exact_power_57]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_58 :
    barrierP2MainBase ^ 58 = barrierComplex (-111750750167621271759420870546188319483954816676052972915607758750470394744381751173656580313005858118033471021014478146641600278524257731 / 12037062152420224081599862141155795740863135301346176220249617472290992736816406250000000000000000000000000000000000000000000000000000000000) (-3069946017802563007195365344140601251182229183296727209369909289026517172733874002698332906168991023318708668813450176843814497336732099 / 601853107621011204079993107057789787043156765067308811012480873614549636840820312500000000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (57 + 1) = _
  rw [pow_succ, barrierP2_exact_power_57]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_58 :
    barrierP2 58 ^ 2 / 58 < (19 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 58 (by norm_num), barrierP2_exact_power_58]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_59 :
    barrierP2MainBase ^ 59 = barrierComplex (11551484428036500582632000560484434407307293459615726786042604278261159915455040135418230021178223970551290043058537816108789881342909727587 / 3009265538105056020399965535288948935215783825336544055062404368072748184204101562500000000000000000000000000000000000000000000000000000000000) (-2711484770674207148797666828392799005685343325980867828689994278556038869066538481118224660882908323787430432248751705507572273283547604367 / 300926553810505602039996553528894893521578382533654405506240436807274818420410156250000000000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (58 + 1) = _
  rw [pow_succ, barrierP2_exact_power_58]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_59 :
    barrierP2 59 ^ 2 / 59 < (7 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 59 (by norm_num), barrierP2_exact_power_59]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_exact_power_60 :
    barrierP2MainBase ^ 60 = barrierComplex (6502099114395515955635169718194579704444357399327157722065966739078896076908504429686536010517788296033769665162475292437918395823046413778601 / 752316384526264005099991383822237233803945956334136013765601092018187046051025390625000000000000000000000000000000000000000000000000000000000000) (10165999605966637448909483791905380711865242653680087800955501499660889203346776902445006164339612993778438552431254027191400249268266441703 / 3761581922631320025499956919111186169019729781670680068828005460090935230255126953125000000000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (59 + 1) = _
  rw [pow_succ, barrierP2_exact_power_59]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_60 :
    barrierP2 60 ^ 2 / 60 < (5 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 60 (by norm_num), barrierP2_exact_power_60]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex]

theorem barrierP2_norm_block_60 :
    (∑ k ∈ Finset.range 4,
      barrierP2 (56 + k + 1) ^ 2 / ((56 + k + 1 : ℕ) : ℝ)) ≤
      (37 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_57.le) barrierP2_norm_term_58.le) barrierP2_norm_term_59.le) barrierP2_norm_term_60.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_60 :
    (∑ k ∈ Finset.range 60,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (66295876 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (56 + 4),
    barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierP2_norm_prefix_56 barrierP2_norm_block_60
  have hc : (66295839 / 1000000000 : ℝ) + 37 / 1000000000 =
      66295876 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end

end OAI
