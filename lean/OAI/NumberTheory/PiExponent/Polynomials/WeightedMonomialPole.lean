import OAI.NumberTheory.PiExponent.Polynomials.WeightedPolynomialPole

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.WeightedMonomialPole

open WeightedCurveDegree WeightedPolynomialPole PolynomialPoleBound

variable {K ι : Type*} [Field K] [Fintype ι]

theorem coordinateOrder_le_realValuation (v : AddValuation K (WithTop ℤ)) (x : K) :
    ((coordinateOrder v x : ℝ) : WithTop ℝ) ≤ realValuation v x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [realValuation_of_ne_zero v x hx]

theorem realValuation_le_iff (v : AddValuation K (WithTop ℤ)) (x y : K) :
    realValuation v x ≤ realValuation v y ↔ v x ≤ v y :=
  (Int.cast_strictMono (R := ℝ)).withTop_map.le_iff_le

theorem monomial_order_lower (v : AddValuation K (WithTop ℤ)) (x : ι → K)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) (a : ι → ℕ) {R : ℚ}
    (ha : (∑ i, w i * (a i : ℚ)) ≤ R) :
    ((-(R : ℝ) * (coordinatePole v x w : ℝ) : ℝ) : WithTop ℝ) ≤
      realValuation v (∏ i, x i ^ a i) := by
  have hq : -R * coordinatePole v x w ≤
      ∑ i, (a i : ℚ) * (coordinateOrder v (x i) : ℚ) := by
    have h := monomial_pole_le w (fun i => (coordinateOrder v (x i) : ℚ)) hw a ha
    change -(∑ i, (a i : ℚ) * (coordinateOrder v (x i) : ℚ)) ≤ R * coordinatePole v x w at h
    linarith
  have hr : -(R : ℝ) * (coordinatePole v x w : ℝ) ≤
      ∑ i, (a i : ℝ) * (coordinateOrder v (x i) : ℝ) := by exact_mod_cast hq
  apply (WithTop.coe_le_coe.mpr hr).trans
  rw [WithTop.coe_sum, valuation_prod]
  apply Finset.sum_le_sum
  intro i hi
  rw [(realValuation v).map_pow]
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using
    nsmul_le_nsmul_right (coordinateOrder_le_realValuation v (x i)) (a i)

theorem coordinateOrder_pow (v : AddValuation K (WithTop ℤ))
    (x : K) (hx : x ≠ 0) (n : ℕ) :
    coordinateOrder v (x ^ n) = (n : ℤ) * coordinateOrder v x := by
  rw [coordinateOrder, dite_eq_right (pow_ne_zero n hx), coordinateOrder, dite_eq_right hx]
  have hu : Units.mk0 (x ^ n) (pow_ne_zero n hx) = (Units.mk0 x hx) ^ n := by
    apply Units.ext
    rfl
  rw [hu, integerOrder_pow]

theorem exists_attaining_monomial [DecidableEq ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → K)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (_hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (M : Finset (ι → ℕ)) (hzero : 0 ∈ M)
    (hpure : ∀ i, Pi.single i (powers i) ∈ M) :
    ∃ a ∈ M, (∏ i, x i ^ a i) ≠ 0 ∧
      (coordinateOrder v (∏ i, x i ^ a i) : ℚ) = -R * coordinatePole v x w := by
  by_cases hD : coordinatePole v x w = 0
  · refine ⟨0, hzero, by simp, ?_⟩
    simp [hD, coordinateOrder, integerOrder_one]
  have hDpos : 0 < coordinatePole v x w :=
    lt_of_le_of_ne (weightedPole_nonneg w _) (Ne.symm hD)
  obtain ⟨o, _, ho⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Option ι))) Finset.univ_nonempty
    (fun i => i.elim 0 (fun j => -(coordinateOrder v (x j) : ℚ) / w j))
  change coordinatePole v x w = _ at ho
  cases o with
  | none => exact False.elim (hD ho)
  | some i =>
    change coordinatePole v x w = -(coordinateOrder v (x i) : ℚ) / w i at ho
    have hx : x i ≠ 0 := by
      intro hx
      have hh : coordinatePole v x w = 0 := by simpa [hx, coordinateOrder] using ho
      exact hD hh
    have heval : (∏ j, x j ^ (Pi.single i (powers i) : ι → ℕ) j) = x i ^ powers i := by
      simp [Pi.single_apply]
    refine ⟨Pi.single i (powers i), hpure i, ?_, ?_⟩
    · rw [heval]
      exact pow_ne_zero _ hx
    · rw [heval, coordinateOrder_pow v (x i) hx]
      push_cast
      change (powers i : ℚ) * (coordinateOrder v (x i) : ℚ) = -R * coordinatePole v x w
      rw [ho, ← hpowers i]
      field_simp [ne_of_gt (hw i)]

theorem exists_minimizing_monomial [DecidableEq ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → K)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (M : Finset (ι → ℕ)) (hzero : 0 ∈ M)
    (hpure : ∀ i, Pi.single i (powers i) ∈ M)
    (hbudget : ∀ a ∈ M, (∑ i, w i * (a i : ℚ)) ≤ R) :
    ∃ a ∈ M, (∏ i, x i ^ a i) ≠ 0 ∧
      (coordinateOrder v (∏ i, x i ^ a i) : ℚ) = -R * coordinatePole v x w ∧
      ∀ b ∈ M, v (∏ i, x i ^ a i) ≤ v (∏ i, x i ^ b i) := by
  obtain ⟨a,ha,han,hao⟩ := exists_attaining_monomial v x w hw hR powers hpowers M hzero hpure
  refine ⟨a,ha,han,hao,?_⟩
  intro b hb
  apply (realValuation_le_iff v _ _).mp
  rw [realValuation_of_ne_zero v _ han]
  have he : (coordinateOrder v (∏ i, x i ^ a i) : ℝ) =
      -(R : ℝ) * (coordinatePole v x w : ℝ) := by exact_mod_cast hao
  rw [he]
  exact monomial_order_lower v x w hw b (hbudget b hb)

end PiExponent.WeightedMonomialPole

end

end OAI
