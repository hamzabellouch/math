import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Energy.BarrierTailPairRational

namespace OAI

section

noncomputable section

namespace InternalCatalan.ManuscriptPrecision

def logCoefficientMass (cs : List ℂ) : ℝ :=
  (cs.map fun c => ‖c‖).sum

def tailCoefficientMass (tail : List (ℂ × ℂ)) : ℝ :=
  logCoefficientMass (tail.map fun zr => zr.2)

def pairLogCoefficients (c : ℂ) (tail : List (ℂ × ℂ)) : List ℂ :=
  tail.flatMap (fun zr => tail.map (fun ws => c * zr.2 * ws.2))

def normLogCoefficients (κ : ℝ) (p v : List (ℂ × ℂ)) : List ℂ :=
  pairLogCoefficients (-(κ : ℂ)) p ++
    pairLogCoefficients (-((1 / 2 : ℝ) : ℂ)) v

def xLogCoefficients (κ : ℝ) (p v : List (ℂ × ℂ)) : List ℂ :=
  ([((19 / 48 : ℝ) : ℂ), ((1 / 12 : ℝ) : ℂ),
      -((κ / 2 + 17 / 48 : ℝ) : ℂ)] ++
    p.map (fun zr => (κ : ℂ) * zr.2)) ++ v.map (fun zr => zr.2)

def yLogCoefficients (v : List (ℂ × ℂ)) : List ℂ :=
  [((7 / 48 : ℝ) : ℂ), ((1 / 12 : ℝ) : ℂ)] ++
    v.map (fun zr => -zr.2)

@[simp] theorem logCoefficientMass_nil : logCoefficientMass [] = 0 := rfl

@[simp] theorem logCoefficientMass_cons (c : ℂ) (cs : List ℂ) :
    logCoefficientMass (c :: cs) = ‖c‖ + logCoefficientMass cs := rfl

theorem logCoefficientMass_append (xs ys : List ℂ) :
    logCoefficientMass (xs ++ ys) = logCoefficientMass xs + logCoefficientMass ys := by
  simp only [logCoefficientMass, List.map_append, List.sum_append]

theorem logCoefficientMass_nonneg (cs : List ℂ) : 0 ≤ logCoefficientMass cs := by
  induction cs with
  | nil => exact le_rfl
  | cons c cs ih =>
    rw [logCoefficientMass_cons]
    exact add_nonneg (norm_nonneg c) ih

@[simp] theorem tailCoefficientMass_nil : tailCoefficientMass [] = 0 := rfl

@[simp] theorem tailCoefficientMass_cons (zr : ℂ × ℂ) (tail : List (ℂ × ℂ)) :
    tailCoefficientMass (zr :: tail) = ‖zr.2‖ + tailCoefficientMass tail := rfl

theorem tailCoefficientMass_nonneg (tail : List (ℂ × ℂ)) :
    0 ≤ tailCoefficientMass tail := logCoefficientMass_nonneg _

theorem tailCoefficientMass_le_length (tail : List (ℂ × ℂ))
    (h : ∀ zr ∈ tail, ‖zr.2‖ ≤ 1) :
    tailCoefficientMass tail ≤ (tail.length : ℝ) := by
  induction tail with
  | nil => simp
  | cons zr tail ih =>
    have hz := h zr List.mem_cons_self
    have ht := ih (fun ws hws => h ws (List.mem_cons_of_mem _ hws))
    simp only [tailCoefficientMass_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem logCoefficientMass_scaled_tail (c : ℂ) (tail : List (ℂ × ℂ)) :
    logCoefficientMass (tail.map (fun zr => c * zr.2)) =
      ‖c‖ * tailCoefficientMass tail := by
  induction tail with
  | nil => simp
  | cons zr tail ih =>
    simp only [List.map_cons, logCoefficientMass_cons, tailCoefficientMass_cons,
      norm_mul, ih]
    ring

theorem logCoefficientMass_neg_tail (tail : List (ℂ × ℂ)) :
    logCoefficientMass (tail.map (fun zr => -zr.2)) = tailCoefficientMass tail := by
  induction tail with
  | nil => rfl
  | cons zr tail ih =>
    simp only [List.map_cons, logCoefficientMass_cons, tailCoefficientMass_cons,
      norm_neg, ih]

theorem logCoefficientMass_pair_lists (c : ℂ) (xs ys : List (ℂ × ℂ)) :
    logCoefficientMass (xs.flatMap (fun zr => ys.map (fun ws => c * zr.2 * ws.2))) =
      ‖c‖ * tailCoefficientMass xs * tailCoefficientMass ys := by
  induction xs with
  | nil => simp
  | cons zr xs ih =>
    rw [List.flatMap_cons, logCoefficientMass_append,
      logCoefficientMass_scaled_tail, ih, tailCoefficientMass_cons, norm_mul]
    ring

theorem logCoefficientMass_pair (c : ℂ) (tail : List (ℂ × ℂ)) :
    logCoefficientMass (pairLogCoefficients c tail) =
      ‖c‖ * (tailCoefficientMass tail) ^ 2 := by
  rw [pairLogCoefficients, logCoefficientMass_pair_lists]
  ring

theorem normLogCoefficients_mass (κ : ℝ) (p v : List (ℂ × ℂ)) :
    logCoefficientMass (normLogCoefficients κ p v) =
      |κ| * (tailCoefficientMass p) ^ 2 + (1 / 2 : ℝ) * (tailCoefficientMass v) ^ 2 := by
  rw [normLogCoefficients, logCoefficientMass_append,
    logCoefficientMass_pair, logCoefficientMass_pair]
  norm_num [norm_neg, Complex.norm_real, Real.norm_eq_abs]

theorem xLogCoefficients_mass (κ : ℝ) (p v : List (ℂ × ℂ)) :
    logCoefficientMass (xLogCoefficients κ p v) =
      23 / 48 + |κ / 2 + 17 / 48| + |κ| * tailCoefficientMass p +
        tailCoefficientMass v := by
  simp only [xLogCoefficients, logCoefficientMass_append,
    logCoefficientMass_cons, logCoefficientMass_nil, logCoefficientMass_scaled_tail,
    norm_neg, Complex.norm_real, Real.norm_eq_abs]
  change |(19 / 48 : ℝ)| + (|(1 / 12 : ℝ)| + (|κ / 2 + 17 / 48| + 0)) +
      |κ| * tailCoefficientMass p + tailCoefficientMass v = _
  norm_num
  ring

theorem yLogCoefficients_mass (v : List (ℂ × ℂ)) :
    logCoefficientMass (yLogCoefficients v) = 11 / 48 + tailCoefficientMass v := by
  simp only [yLogCoefficients, logCoefficientMass_append,
    logCoefficientMass_cons, logCoefficientMass_nil, logCoefficientMass_neg_tail,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num

theorem case2_tail_masses :
    tailCoefficientMass barrierP2Tail ≤ 10 ∧ tailCoefficientMass barrierV2Tail ≤ 13 := by
  constructor
  · have h := tailCoefficientMass_le_length barrierP2Tail
      (fun zr hzr => (barrierP2_tail_norm_bounds zr hzr).2.le)
    simpa only [barrier_tail_lengths.1, Nat.cast_ofNat] using h
  · have h := tailCoefficientMass_le_length barrierV2Tail
      (fun zr hzr => (barrierV2_tail_norm_bounds zr hzr).2.le)
    simpa only [barrier_tail_lengths.2, Nat.cast_ofNat] using h

theorem case2_norm_mass_le :
    logCoefficientMass (normLogCoefficients 2 barrierP2Tail barrierV2Tail) ≤
      (569 / 2 : ℝ) := by
  rw [normLogCoefficients_mass]
  norm_num
  have hp0 := tailCoefficientMass_nonneg barrierP2Tail
  have hv0 := tailCoefficientMass_nonneg barrierV2Tail
  have hp := case2_tail_masses.1
  have hv := case2_tail_masses.2
  have hp2 : (tailCoefficientMass barrierP2Tail) ^ 2 ≤ 100 := by
    have h := mul_le_mul hp hp hp0 (by norm_num : (0 : ℝ) ≤ 10)
    nlinarith only [h]
  have hv2 : (tailCoefficientMass barrierV2Tail) ^ 2 ≤ 169 := by
    have h := mul_le_mul hv hv hv0 (by norm_num : (0 : ℝ) ≤ 13)
    nlinarith only [h]
  linarith

theorem case2_X_mass_lt :
    logCoefficientMass (xLogCoefficients 2 barrierP2Tail barrierV2Tail) < 35 := by
  rw [xLogCoefficients_mass]
  norm_num
  have hp := case2_tail_masses.1
  have hv := case2_tail_masses.2
  linarith

theorem case2_Y_mass_lt :
    logCoefficientMass (yLogCoefficients barrierV2Tail) < 14 := by
  rw [yLogCoefficients_mass]
  have hv := case2_tail_masses.2
  linarith

theorem case1_norm_mass_eq :
    logCoefficientMass (normLogCoefficients 1 [] []) = 0 := by
  norm_num [normLogCoefficients_mass]

theorem case1_X_mass_eq :
    logCoefficientMass (xLogCoefficients 1 [] []) = (4 / 3 : ℝ) := by
  norm_num [xLogCoefficients_mass]

theorem case1_X_mass_lt : logCoefficientMass (xLogCoefficients 1 [] []) < 35 := by
  rw [case1_X_mass_eq]
  norm_num

theorem case1_Y_mass_eq :
    logCoefficientMass (yLogCoefficients []) = (11 / 48 : ℝ) := by
  norm_num [yLogCoefficients_mass]

theorem case1_Y_mass_lt : logCoefficientMass (yLogCoefficients []) < 14 := by
  rw [case1_Y_mass_eq]
  norm_num

end InternalCatalan.ManuscriptPrecision

end

end

end OAI
