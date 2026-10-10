import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantVariation
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterJointComparison

namespace OAI

/-! # The moving-window budget for the original outer-prior kernel -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- The two original outer factors and the diagonal reciprocal ratio cost
only a fixed constant, uniformly in the giant cell centers. -/
theorem movingOuterVariationBudget_bound (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ)
    (n : ℕ) (B D : ℝ) (diagonal : Bool) :
    2 * giantOuterScalar diagonal * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
      (2 * Real.exp 1 * (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (3 + Real.exp 2)) *
        (movingFourierVariationBudget ψ V lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := by
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hcoef : 2 * giantOuterScalar diagonal * (if diagonal then 1 + Real.exp 2 else 2) ≤
      2 * Real.exp 1 * (3 + Real.exp 2) := by
    have hp := mul_nonneg (Real.exp_nonneg (1 : ℝ)) (Real.exp_nonneg (2 : ℝ))
    cases diagonal <;> simp only [giantOuterScalar, Bool.false_eq_true, ite_false, ite_true] <;>
      nlinarith only [he, hp, Real.exp_pos (1 : ℝ)]
  have hh := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (sq_nonneg (2 * B + D * (Real.exp 2 - 1)))
      (sq_nonneg (movingFourierVariationBudget ψ V lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1))))
  convert hh using 1 <;> (try unfold movingOuterVariationBudget) <;> ring

/-- Actual spectator growth, bounded harmonic normalizers and every moving
bottom window fit the common giant comparison budget. -/
theorem moving_outer_variation_scale (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin B D H : ℝ) (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hH : 0 ≤ H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      let m := spectatorBulkCount k L
      ∀ (p : Fin m → ℕ) (V lo hi amp : ℝ) (diagonal : Bool),
      0 ≤ V → V ≤ Real.exp (A * m) → lo ≤ hi → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      0 ≤ amp → amp ≤ 4 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 * Real.exp (H * L + H * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      2 * (amp * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ 2 + C * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
  obtain ⟨C₀, hC₀, hbase⟩ := movingPattern_pointwise_cost_budget ψ n r₀ k A Wwin B D hA hWwin
  let F := 2 * Real.exp 1 * (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (3 + Real.exp 2)
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  let C := C₀ + H + F
  have hC : C₀ ≤ C := by dsimp only [C]; linarith only [hH, hF]
  refine ⟨C, hC₀.trans hC, ?_⟩
  intro L hL
  dsimp only
  intro p V lo hi amp diagonal hV hVA hhi hwidth hp hamp hampup
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have houter := movingOuterVariationBudget_bound ψ V lo hi n B D diagonal
  have hbase' := hbase L hL p V lo hi hV hVA hhi hwidth hp
  let W := (movingFourierVariationBudget ψ V lo hi n *
    (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hFE : F ≤ Real.exp (F * L) := by
    have hh := mul_le_mul_of_nonneg_left hL hF
    linarith only [hh, Real.add_one_le_exp (F * L)]
  have hbound :
      2 * (amp * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C₀ * L ^ 2 + C₀ * L * Real.exp ((1 / 1000 : ℝ) * L)) *
          Real.exp ((H + F) * L + H * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
    calc
      _ = amp * (2 * giantOuterScalar diagonal * movingOuterVariationBudget ψ V lo hi n B D diagonal) := by ring
      _ ≤ amp * (F * W) := mul_le_mul_of_nonneg_left houter hamp
      _ ≤ (4 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 * Real.exp (H * L + H * L * Real.exp ((12 / 1000 : ℝ) * L))) * (F * W) :=
        mul_le_mul_of_nonneg_right hampup (mul_nonneg hF (sq_nonneg _))
      _ = (4 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 * W) * (F * Real.exp (H * L + H * L * Real.exp ((12 / 1000 : ℝ) * L))) := by ring
      _ ≤ Real.exp (C₀ * L ^ 2 + C₀ * L * Real.exp ((1 / 1000 : ℝ) * L)) *
          (Real.exp (F * L) * Real.exp (H * L + H * L * Real.exp ((12 / 1000 : ℝ) * L))) :=
        mul_le_mul hbase' (mul_le_mul_of_nonneg_right hFE (Real.exp_nonneg _))
          (mul_nonneg hF (Real.exp_nonneg _)) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  apply hbound.trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hLsq : L ≤ L ^ 2 := by nlinarith only [hL]
  have hpoly := mul_le_mul_of_nonneg_left hLsq (add_nonneg hH hF)
  have hscale : Real.exp ((1 / 1000 : ℝ) * L) ≤ Real.exp ((12 / 1000 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by linarith only [hL0])
  have hterm := mul_le_mul_of_nonneg_left hscale
    (mul_nonneg (le_trans (by norm_num) hC₀) hL0)
  have hextra := mul_nonneg (mul_nonneg hF hL0)
    (Real.exp_nonneg ((12 / 1000 : ℝ) * L))
  dsimp only [C] at ⊢
  nlinarith only [hpoly, hterm, hextra]

end Ostmann

end OAI
