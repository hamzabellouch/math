import OAI.Geometry.IsometricImmersion.Immersions.HeightCoefficientClosedBounds
import OAI.Geometry.IsometricImmersion.Caps.CapReciprocalBounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem capPullback_bound_one {u : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {A F : ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U)
    (hmapS : MapsTo (capChart Y) capChartDomain modelSquare)
    (hA : 0 ≤ A) (hF : 0 ≤ F)
    (huB : CoordinateBound u modelSquare 1 A)
    (hFB : CoordinateBound (capFlowHeight Y) capChartDomain 3 F) :
    CoordinateBound (capPullback Y u) capChartDomain 1 (A * (1 + F)) := by
  intro ds hds p hp
  have hv : |u (capChart Y p)| ≤ A := huB [] (by norm_num) _ (hmapS hp)
  have hdu (i : Fin 2) : |coordPartial i u (capChart Y p)| ≤ A := huB [i] (by norm_num) _ (hmapS hp)
  have hdf (i : Fin 2) : |coordPartial i (capFlowHeight Y) p| ≤ F := hFB [i] (by norm_num) p hp
  cases ds with
  | nil => exact hv.trans (by nlinarith [mul_nonneg hA hF])
  | cons i ds =>
    cases ds with
    | nil =>
      change |coordPartial i (capPullback Y u) p| ≤ A * (1 + F)
      rw [capPullback_partial hY hp ((hu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp)) i]
      have h0 : |if i = 0 then coordPartial 0 u (capChart Y p) else 0| ≤ A := by
        split_ifs
        · exact hdu 0
        · simpa only [abs_zero] using hA
      have h1 : |coordPartial 1 u (capChart Y p) * coordPartial i (capFlowHeight Y) p| ≤ A * F := by
        rw [abs_mul]
        exact mul_le_mul (hdu 1) (hdf i) (abs_nonneg _) hA
      exact ((abs_add_le _ _).trans (add_le_add h0 h1)).trans (le_of_eq (by ring))
    | cons _ ds => simp only [List.length_cons] at hds; omega

theorem heightOriginalB_bound_one {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {P Q : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hne : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hPB : CoordinateBound (heightPFirst g z 0) modelSquare 1 P)
    (hqB : CoordinateBound (hessianQuotient g z) modelSquare 3 Q) (ell : ℕ) :
    CoordinateBound (heightOriginalB g z ell) modelSquare 1 (P + 2 * (ell : ℝ) * Q) := by
  have hI : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hP := heightPFirst_contDiffOn hg hU hz hne 0
  have hq := hessianQuotient_contDiffOn hg hU hz hne
  have hqy := partial_contDiffOn hq hU 1
  have hqyB : CoordinateBound (coordPartial 1 (hessianQuotient g z)) modelSquare 1 Q :=
    (hqB.mono (by norm_num : 2 ≤ 3) le_rfl).partial_bound 1
  have ht := CoordinateBound.const_mul (hqy.mono hI) isOpen_interior
    (hqyB.restrict_domain interior_subset) (2 * (ell : ℝ))
  have hb := CoordinateBound.sub (hP.neg.mono hI) (contDiffOn_const.mul (hqy.mono hI)) isOpen_interior
    (CoordinateBound.neg (hP.mono hI) isOpen_interior (hPB.restrict_domain interior_subset)) ht
  have hc : |2 * (ell : ℝ)| = 2 * (ell : ℝ) := abs_of_nonneg (by positivity)
  rw [hc] at hb
  exact CoordinateBound.of_modelSquare_interior (heightOriginalB_contDiffOn hg hU hz hne ell) hU hSU hb

theorem capChartRho_lower_from_q
    {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hM : 0 ≤ M) (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    {p : Coord} (hp : p ∈ capChartDomain) : 1 / Real.exp (2 * M) ≤ capChartRho Y p := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hpos := cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hp.2 hp.1
  have hupper := (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hq1 hp.2 hp.1).2
  unfold capChartRho
  rw [capFlowHeight_partial_one_eq hs hp]
  apply (le_div_iff₀ hpos).mpr
  calc
    _ ≤ (1 / Real.exp (2 * M)) * Real.exp (2 * M) := mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = 1 := one_div_mul_cancel (Real.exp_ne_zero _)

theorem heightChartRemainder_bound_of_low_coefficients
    (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : Coord) (ell : ℕ)
    {DE DG SG lowerG RL : ℝ} (hDE : 0 ≤ DE) (hDG : 0 ≤ DG) (hSG : 0 ≤ SG)
    (hGL : 0 < lowerG) (hRL : 0 < RL)
    (herror : |curvatureDriftError g z (capChart Y p)| ≤ DE)
    (hGy : |coordPartial 1 (darbouxG g z) (capChart Y p)| ≤ DG)
    (hG : lowerG ≤ darbouxG g z (capChart Y p))
    (hrho : RL ≤ capChartRho Y p) (hsigma : |capChartSigma Y p| ≤ SG) :
    |heightChartRemainder g z Y ell p| ≤
      (DE + DG) / (lowerG * RL) + (2 * (ell : ℝ) + 1) * SG / RL^2 := by
  have hGpos : 0 < darbouxG g z (capChart Y p) := hGL.trans_le hG
  have hrhopos : 0 < capChartRho Y p := hRL.trans_le hrho
  have hden : lowerG * RL ≤ |darbouxG g z (capChart Y p) * capChartRho Y p| := by
    rw [abs_of_pos (mul_pos hGpos hrhopos)]
    exact mul_le_mul hG hrho hRL.le hGpos.le
  have hden2 : RL^2 ≤ |(capChartRho Y p)^2| := by
    rw [abs_pow, abs_of_pos hrhopos]
    exact pow_le_pow_left₀ hRL.le hrho 2
  have hnum := (abs_sub _ _).trans (add_le_add herror hGy)
  have hfirst := LowQuotient.abs_div_bound (add_nonneg hDE hDG) hnum (mul_pos hGL hRL) hden
  have hnum2 : |(2 * (ell : ℝ) + 1) * capChartSigma Y p| ≤ (2 * (ell : ℝ) + 1) * SG := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (ell : ℝ) + 1)]
    exact mul_le_mul_of_nonneg_left hsigma (by positivity)
  have hsecond := LowQuotient.abs_div_bound (by positivity) hnum2 (pow_pos hRL 2) hden2
  exact (abs_sub _ _).trans (add_le_add hfirst hsecond)

end SmoothLocal.Flow

end

end OAI
