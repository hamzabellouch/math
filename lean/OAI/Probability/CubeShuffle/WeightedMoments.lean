import OAI.Probability.CubeShuffle.UniformDecay

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace CubeShuffle.WeightedSweep
open Specht UnitaryFinite

lemma weighted_power_collapse {D b : ℝ} (hD : 0 < D) (hb : 0 < b) :
    D * (D * (D ^ (-b)) ^ (2 / b)) = 1 := by
  rw [← Real.rpow_mul hD.le]
  have he : -b * (2 / b) = (-2 : ℝ) := by
    rw [neg_mul, mul_div_cancel₀ _ hb.ne']
  rw [he, Real.rpow_neg hD.le, Real.rpow_two]
  field_simp

theorem weighted_sweep_moments :
    ∃ (W : YoungDiagram → ℝ) (pStar : ℝ) (p : ℕ → ℝ),
      (∀ μ : YoungDiagram, 0 < W μ) ∧
      2 ≤ pStar ∧
      (∀ d : ℕ, 1 ≤ d → 2 ≤ p d ∧ p d ≤ pStar) ∧
      ∀ d : ℕ, 1 ≤ d → ∀ μ : Shapes (2 ^ d),
        dimension μ.1 ^ (3 / 4 : ℝ) ≤ W μ.1 ∧
        W μ.1 ≤ dimension μ.1 ∧
        W μ.1 *
          schattenNorm (V := hilbertSpace μ.1) (fourierSweep d μ) (p d) ^ (p d) ≤ 1 ∧
        ‖fourierSweep d μ‖ ≤ dimension μ.1 ^ (-3 / (4 * pStar)) := by
  obtain ⟨b, hb, hb1, hdecay⟩ := uniform_sweep_dimension_decay
  let P : ℝ := 2 / b
  have hP : 2 ≤ P := (le_div_iff₀ hb).mpr (by linarith)
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hbP : b * P = 2 := mul_div_cancel₀ _ hb.ne'
  refine ⟨dimension, P, fun _ => P, dimension_pos, hP,
    (fun _ _ => ⟨hP, le_rfl⟩), ?_⟩
  intro d hd μ
  let : NormedAddCommGroup (hilbertSpace μ.1) := inferInstance
  let : InnerProductSpace ℂ (hilbertSpace μ.1) := inferInstance
  let : FiniteDimensional ℂ (hilbertSpace μ.1) := inferInstance
  refine ⟨?_, le_rfl, ?_, ?_⟩
  · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (dimension_one_le μ.1) (show (3 / 4 : ℝ) ≤ 1 by norm_num)
  · rw [schattenNorm_rpow (V := hilbertSpace μ.1) _ hPpos.ne']
    have hm := schattenMoment_le (V := hilbertSpace μ.1) (fourierSweep d μ) hPpos.le
    have hrank : (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) = dimension μ.1 := by
      rw [finrank_hilbertSpace]
      rfl
    rw [hrank] at hm
    calc
      dimension μ.1 * schattenMoment (V := hilbertSpace μ.1) (fourierSweep d μ) P
          ≤ dimension μ.1 * (dimension μ.1 * ‖fourierSweep d μ‖ ^ P) :=
        mul_le_mul_of_nonneg_left hm (dimension_pos μ.1).le
      _ ≤ dimension μ.1 * (dimension μ.1 * (dimension μ.1 ^ (-b)) ^ P) := by
        apply mul_le_mul_of_nonneg_left ?_ (dimension_pos μ.1).le
        apply mul_le_mul_of_nonneg_left ?_ (dimension_pos μ.1).le
        exact Real.rpow_le_rpow (norm_nonneg _) (hdecay d hd μ) hPpos.le
      _ = 1 := weighted_power_collapse (dimension_pos μ.1) hb
  · apply (hdecay d hd μ).trans
    apply Real.rpow_le_rpow_of_exponent_le (dimension_one_le μ.1)
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hPpos)).mpr
    nlinarith [hbP]

end CubeShuffle.WeightedSweep

end

end OAI
