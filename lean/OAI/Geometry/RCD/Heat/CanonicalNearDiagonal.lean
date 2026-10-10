import OAI.Geometry.RCD.Heat.CanonicalDiagonalLower
import OAI.Geometry.RCD.Heat.CanonicalGaussianDifference

namespace OAI

/-! # Uniform near-diagonal lower bounds at small times

The diagonal mass bound and the proved Gaussian finite difference estimate
give a dimensional neighborhood of strict positivity. No lower heat-kernel
estimate is assumed.
-/

open Set Metric MeasureTheory TopologicalSpace
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_near_diagonal :
    ∃ c δ τ : ℝ, 0 < c ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < τ ∧ τ ≤ 1 ∧
      ∀ (t : ℝ), 0 < t → t ≤ τ → ∀ x y : X, dist x y ≤ δ*Real.sqrt t →
        c/(hausdorff n X).real (ball y (Real.sqrt t)) ≤
          hX.canonicalHeatKernel hn p t x y := by
  obtain ⟨c,τ,hc,hτ,hdiag⟩ := hX.canonicalHeatKernel_diagonal_lower hn p
  obtain ⟨C,D,B,hC,_hD,hB,hdiff⟩ := hX.canonicalHeatKernel_gaussian_difference hn p
  let δ := min 1 (c/(2*C*Real.exp B))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδc : C*δ*Real.exp B ≤ c/2 := by
    have hh := min_le_right 1 (c/(2*C*Real.exp B))
    have hle := (le_div_iff₀ (by positivity : 0 < 2*C*Real.exp B)).mp hh
    nlinarith only [hle]
  refine ⟨c/2,δ,min τ 1,by positivity,hδ,hδ1,lt_min hτ (by norm_num),min_le_right _ _,?_⟩
  intro t ht htτ x y hxy
  have ht1 : t ≤ 1 := htτ.trans (min_le_right _ _)
  have htold : t ≤ τ := htτ.trans (min_le_left _ _)
  let V := (hausdorff n X).real (ball y (Real.sqrt t))
  have hV : 0 < V := ENNReal.toReal_pos
    (hX.fullSupport y _ (Real.sqrt_pos.mpr ht)).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hxy' : dist y x ≤ Real.sqrt t := by
    rw [dist_comm]
    exact hxy.trans (by nlinarith only [mul_le_mul_of_nonneg_right hδ1 (Real.sqrt_nonneg t)])
  have hh := hdiff t ht ht1 y x y hxy'
  simp only [dist_self,zero_pow (by norm_num : 2 ≠ 0),neg_zero,zero_div,zero_add,dist_comm y x] at hh
  have hsmall : |hX.canonicalHeatKernel hn p t y y-hX.canonicalHeatKernel hn p t x y| ≤ (c/2)/V := by
    apply hh.trans
    calc
      _ ≤ C/(Real.sqrt t*V)*(δ*Real.sqrt t)*Real.exp B := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hxy (by positivity)
        · exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left ht1 hB])
        · positivity
        · positivity
      _ = (C*δ*Real.exp B)/V := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hδc hV.le
  have hdiag' := hdiag t ht htold y
  have hpoint := (abs_le.mp hsmall).2
  change (c/2)/V ≤ _
  change c/V ≤ _ at hdiag'
  have he : c/V = (c/2)/V+(c/2)/V := by ring
  linarith only [hdiag',hpoint,he]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
