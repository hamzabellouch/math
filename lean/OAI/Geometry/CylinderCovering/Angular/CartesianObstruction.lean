import OAI.Geometry.CylinderCovering.Cartesian.CapsDefinitions

namespace OAI

namespace CylinderCovering.CartesianCaps

theorem discriminant_failures_location {τ η x y s : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hη : 0 ≤ η)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hfirst : 1 / 4 + τ * x * y + τ ^ 2 * (D y + η / 2 - x ^ 2 / 4) < s ^ 2)
    (hsecond : 1 / 4 - τ * x * y + τ ^ 2 * (D x + η / 2 - y ^ 2 / 4) <
      (1 - s) ^ 2) :
    |s - 1 / 2| ≤ 3 * τ ∧ |s - 1 / 2 - τ * x * y| ≤ 10 * τ ^ 2 := by
  have hx2 : x ^ 2 ≤ 1 := by
    nlinarith only [(abs_le.mp hx).1, (abs_le.mp hx).2]
  have hy2 : y ^ 2 ≤ 1 := by
    nlinarith only [(abs_le.mp hy).1, (abs_le.mp hy).2]
  have hDy : 0 ≤ D y := by unfold D; positivity
  have hDx : 0 ≤ D x := by unfold D; positivity
  have hB : -(1 / 4 : ℝ) ≤ D y + η / 2 - x ^ 2 / 4 := by linarith
  have hC : -(1 / 4 : ℝ) ≤ D x + η / 2 - y ^ 2 / 4 := by linarith
  have hBmul := mul_le_mul_of_nonneg_left hB (sq_nonneg τ)
  have hCmul := mul_le_mul_of_nonneg_left hC (sq_nonneg τ)
  have hxy : |τ * x * y| ≤ τ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hτ0]
    calc
      τ * |x| * |y| ≤ τ * 1 * 1 := by gcongr
      _ = τ := by ring
  have hτ2 : τ ^ 2 ≤ τ := by nlinarith
  have hcoarse : |s - 1 / 2| ≤ 3 * τ := by
    rw [abs_le]
    constructor
    · by_cases hs : s ≤ 1 / 2
      · have hprod := mul_nonneg hs0 (sub_nonneg.mpr hs)
        nlinarith only [hfirst, hBmul, (abs_le.mp hxy).1, hτ2, hprod, hτ0]
      · linarith
    · by_cases hs : 1 / 2 ≤ s
      · have hprod := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hs1)
        nlinarith only [hsecond, hCmul, (abs_le.mp hxy).2, hτ2, hprod, hτ0]
      · linarith
  have hu2 : (s - 1 / 2) ^ 2 ≤ 9 * τ ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (s - 1 / 2)) (by positivity : 0 ≤ 3 * τ)).2 hcoarse
    nlinarith only [hh, sq_abs (s - 1 / 2)]
  refine ⟨hcoarse, ?_⟩
  rw [abs_le]
  constructor <;> nlinarith only [hfirst, hsecond, hBmul, hCmul, hu2, sq_nonneg τ]

theorem discriminant_failures_impossible {τ η x y s : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hsmall : τ ≤ η / 240)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hfirst : 1 / 4 + τ * x * y + τ ^ 2 * (D y + η / 2 - x ^ 2 / 4) < s ^ 2)
    (hsecond : 1 / 4 - τ * x * y + τ ^ 2 * (D x + η / 2 - y ^ 2 / 4) <
      (1 - s) ^ 2) : False := by
  have hη : 0 ≤ η := by linarith
  obtain ⟨hcoarse, hfine⟩ := discriminant_failures_location hτ.le hτ1 hη hx hy hs0 hs1 hfirst hsecond
  have hxy : |τ * x * y| ≤ τ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hτ.le]
    calc
      τ * |x| * |y| ≤ τ * 1 * 1 := by gcongr
      _ = τ := by ring
  have hsum : |s - 1 / 2 + τ * x * y| ≤ 4 * τ :=
    (abs_add_le _ _).trans (by linarith)
  have herror : |(s - 1 / 2) ^ 2 - (τ * x * y) ^ 2| ≤ 40 * τ ^ 3 := by
    calc
      _ = |s - 1 / 2 - τ * x * y| * |s - 1 / 2 + τ * x * y| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ (10 * τ ^ 2) * (4 * τ) := mul_le_mul hfine hsum (abs_nonneg _) (by positivity)
      _ = 40 * τ ^ 3 := by ring
  have hquartic := mul_nonneg (sq_nonneg τ) (sq_nonneg (x ^ 2 - y ^ 2))
  have hmargin := mul_le_mul_of_nonneg_left hsmall (sq_nonneg τ)
  have hτ3 : 0 < τ ^ 3 := pow_pos hτ 3
  unfold D at hfirst hsecond
  nlinarith only [hfirst, hsecond, (abs_le.mp herror).2, hquartic, hmargin, hτ3]

theorem discriminant_alternative {τ η x y s : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hsmall : τ ≤ η / 240)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.sqrt (s ^ 2 - τ * x * y + τ ^ 2 * x ^ 2 / 4) ≤
        1 / 2 + τ ^ 2 * (D y + η / 2) ∨
      Real.sqrt ((1 - s) ^ 2 + τ * x * y + τ ^ 2 * y ^ 2 / 4) ≤
        1 / 2 + τ ^ 2 * (D x + η / 2) := by
  by_contra! hfail
  have hη : 0 ≤ η := by linarith
  have hDx : 0 ≤ D x := by unfold D; positivity
  have hDy : 0 ≤ D y := by unfold D; positivity
  have hBy : 0 ≤ 1 / 2 + τ ^ 2 * (D y + η / 2) := by positivity
  have hBx : 0 ≤ 1 / 2 + τ ^ 2 * (D x + η / 2) := by positivity
  have hQy : 0 ≤ s ^ 2 - τ * x * y + τ ^ 2 * x ^ 2 / 4 :=
    (Real.sqrt_pos.mp (hBy.trans_lt hfail.1)).le
  have hQx : 0 ≤ (1 - s) ^ 2 + τ * x * y + τ ^ 2 * y ^ 2 / 4 :=
    (Real.sqrt_pos.mp (hBx.trans_lt hfail.2)).le
  have hy2 := (sq_lt_sq₀ hBy (Real.sqrt_nonneg _)).2 hfail.1
  have hx2 := (sq_lt_sq₀ hBx (Real.sqrt_nonneg _)).2 hfail.2
  rw [Real.sq_sqrt hQy] at hy2
  rw [Real.sq_sqrt hQx] at hx2
  apply discriminant_failures_impossible hτ hτ1 hsmall hx hy hs0 hs1
  · nlinarith only [hy2, sq_nonneg (τ ^ 2 * (D y + η / 2))]
  · nlinarith only [hx2, sq_nonneg (τ ^ 2 * (D x + η / 2))]

theorem eventually_discriminant_alternative {η : ℝ} (hη : 0 < η) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      ∀ x y s : ℝ, |x| ≤ 1 → |y| ≤ 1 → 0 ≤ s → s ≤ 1 →
        Real.sqrt (s ^ 2 - τ * x * y + τ ^ 2 * x ^ 2 / 4) ≤
            1 / 2 + τ ^ 2 * (D y + η / 2) ∨
          Real.sqrt ((1 - s) ^ 2 + τ * x * y + τ ^ 2 * y ^ 2 / 4) ≤
            1 / 2 + τ ^ 2 * (D x + η / 2) := by
  refine ⟨min 1 (η / 240), lt_min (by norm_num) (by positivity), ?_⟩
  intro τ hτ hsmall x y s hx hy hs0 hs1
  exact discriminant_alternative hτ (hsmall.trans (min_le_left _ _))
    (hsmall.trans (min_le_right _ _)) hx hy hs0 hs1

end CylinderCovering.CartesianCaps

end OAI
