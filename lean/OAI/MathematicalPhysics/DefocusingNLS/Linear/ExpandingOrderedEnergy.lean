import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingEnergyComponents
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCommutatorSymbol

namespace OAI

/-! # Ordered derivative components of the exact torus high energy -/

open scoped ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousOrderedSymbol_sq_sum (N : ℕ) (ξ : E) :
    (∑ j : Fin N → Fin 12, ‖homogeneousOrderedSymbol N j ξ‖ ^ 2) = ‖ξ‖ ^ (2 * N) := by
  have he (j : Fin N → Fin 12) : ‖homogeneousOrderedSymbol N j ξ‖ ^ 2 =
      ∏ i, (ξ (j i)) ^ 2 := by
    rw [homogeneousOrderedSymbol, norm_prod, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, sq_abs]
  simp_rw [he]
  rw [← Fintype.sum_pow (fun i : Fin 12 => (ξ i) ^ 2) N,
    ← EuclideanSpace.real_norm_sq_eq, pow_mul]

noncomputable def expandingOrderedMultiplier (a L : ℝ) (N : ℕ)
    (j : Fin N → Fin 12) (n : frequencyLattice) : ℂ :=
  (((2 * Real.pi) ^ 6 * L ^ (6 - (N : ℝ)) /
    expandingSobolevWeight a N L n : ℝ) : ℂ) * homogeneousOrderedSymbol N j n

theorem expandingOrderedMultiplier_sq_sum (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (n : frequencyLattice) :
    (∑ j : Fin N → Fin 12, ‖expandingOrderedMultiplier a L N j n‖ ^ 2) =
      1 - expandingLowFraction a N L n := by
  have hc : ((2 * Real.pi) ^ 6 * L ^ (6 - (N : ℝ)) /
      expandingSobolevWeight a N L n) ^ 2 =
      L ^ (12 - 2 * (N : ℝ)) / expandingSobolevWeightSq a N L n := by
    rw [div_pow, mul_pow, ← pow_mul, expandingSobolevWeight_sq a N L hL]
    have hpow : (L ^ (6 - (N : ℝ))) ^ 2 = L ^ (12 - 2 * (N : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ L)]
      congr 1
      ring
    rw [hpow]
    norm_num only [Nat.reduceMul]
    have hP : (2 * Real.pi) ^ 12 ≠ 0 := by positivity
    field_simp
  simp only [expandingOrderedMultiplier, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  simp only [mul_pow] at hc
  rw [← Finset.mul_sum, homogeneousOrderedSymbol_sq_sum, hc,
    expandingHighFraction_eq a N L hL]
  have hpow : ‖n‖ ^ (2 * (N : ℝ)) = ‖n‖ ^ (2 * N) := by
    rw [show (2 : ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]
  rw [hpow]
  rw [Submodule.norm_coe]
  ring

theorem expandingOrderedMultiplier_norm_le (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (n : frequencyLattice) :
    ‖expandingOrderedMultiplier a L N j n‖ ≤ 1 := by
  have hi : ‖expandingOrderedMultiplier a L N j n‖ ^ 2 ≤
      ∑ i : Fin N → Fin 12, ‖expandingOrderedMultiplier a L N i n‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖expandingOrderedMultiplier a L N i n‖ ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  rw [expandingOrderedMultiplier_sq_sum a L N hL n] at hi
  have hf := (expandingLowFraction_bounds a N L hL n).1
  nlinarith [norm_nonneg (expandingOrderedMultiplier a L N j n)]

noncomputable def expandingOrderedFourierEnergy (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) : FourierL2 →L[ℂ] FourierL2 :=
  let F : FourierL2 → FourierL2 := fun f =>
    ⟨fun n => expandingOrderedMultiplier a L N j n * f n, by
      apply (lp.memℓp f).mono'
      intro n
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (expandingOrderedMultiplier_norm_le a L N hL j n)⟩
  LinearMap.mkContinuous
    { toFun := F
      map_add' := by intro f g; ext n; exact mul_add _ _ _
      map_smul' := by intro c f; ext n; change _ * (c * _) = c * (_ * _); ring }
    1 (by
      intro f
      rw [one_mul]
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖expandingOrderedMultiplier a L N j n * f n‖ ≤ ‖f n‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (expandingOrderedMultiplier_norm_le a L N hL j n))

@[simp] theorem expandingOrderedFourierEnergy_apply (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (f : FourierL2) (n : frequencyLattice) :
    expandingOrderedFourierEnergy a L N hL j f n = expandingOrderedMultiplier a L N j n * f n := rfl

theorem expandingOrderedFourierEnergy_norm_sq (a L : ℝ) (N : ℕ) (hL : 1 ≤ L) (f : FourierL2) :
    (∑ j : Fin N → Fin 12, ‖expandingOrderedFourierEnergy a L N hL j f‖ ^ 2) =
      ‖expandingHighEnergy a N L hL f‖ ^ 2 := by
  have hs (j : Fin N → Fin 12) : HasSum
      (fun n => ‖expandingOrderedFourierEnergy a L N hL j f n‖ ^ 2)
      (‖expandingOrderedFourierEnergy a L N hL j f‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (p := 2) (by norm_num) (expandingOrderedFourierEnergy a L N hL j f)
  have hsum := hasSum_sum (s := Finset.univ) (fun j _ => hs j)
  rw [← hsum.tsum_eq, expandingHighEnergy, fourierEnergyComponent_norm_sq]
  apply tsum_congr
  intro n
  simp only [expandingOrderedFourierEnergy_apply, norm_mul, mul_pow]
  rw [← Finset.sum_mul, expandingOrderedMultiplier_sq_sum a L N hL n]

end DefocusingNLS

end OAI
