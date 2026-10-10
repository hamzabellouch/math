import OAI.Geometry.RCD.Coordinates.PatchCover
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-!
# Localization of active coordinate patches

A cutoff support bounds the finely normalized displacement. Coarse harmonic
separation and sublinear growth of the normalizations then bound the original
metric distance. The squared growth hypothesis below is the exponent-one
bound for squared norms (equivalently, exponent one-half for norms).
-/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace RegularPointCoordinates

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Membership in the actual topological support of a normalized cutoff
bounds its normalized displacement, including boundary support points. -/
theorem normalized_cutoff_support_norm_le (T : E →L[ℝ] F) (c x : E)
    (psi : F → ℝ) {r L : ℝ} (hr : 0 < r)
    (hsupport : tsupport psi ⊆ Metric.closedBall 0 L)
    (hx : x ∈ tsupport (fun P => psi (r⁻¹ • T (P - c)))) :
    ‖T (x - c)‖ ≤ L * r := by
  have hcont : Continuous (fun P => r⁻¹ • T (P - c)) := by fun_prop
  have hm := tsupport_comp_subset_preimage psi hcont hx
  have hb := hsupport hm
  have hn : r⁻¹ * ‖T (x - c)‖ ≤ L := by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] using hb
  have hh := mul_le_mul_of_nonneg_left hn hr.le
  rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at hh
  simpa only [mul_comm] using hh

/-- A coarse lower bound and sublinear normalization growth localize a
fine-scale displacement. The estimate is uniform in the scale `r`. -/
theorem distance_le_of_normalization_growth {d r c M L A B : ℝ}
    (hd : 0 ≤ d) (hr : 0 < r) (hc : 0 < c) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsmall : A ≤ L * r) (hseparate : c * d ≤ B)
    (hgrowth : B ^ 2 ≤ M ^ 2 * (d / r) * A ^ 2) :
    d ≤ (M * L / c) ^ 2 * r := by
  by_cases hz : d = 0
  · rw [hz]
    positivity
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hz)
  have hsep2 := (sq_le_sq₀ (mul_nonneg hc.le hd) hB).mpr hseparate
  have hsmall2 := (sq_le_sq₀ hA (mul_nonneg hL hr.le)).mpr hsmall
  have hcoef : 0 ≤ M ^ 2 * (d / r) := mul_nonneg (sq_nonneg _) (div_nonneg hd hr.le)
  have hg := hgrowth.trans (mul_le_mul_of_nonneg_left hsmall2 hcoef)
  have hid : M ^ 2 * (d / r) * (L * r) ^ 2 = (M * L) ^ 2 * r * d := by
    field_simp [hr.ne']
  rw [hid] at hg
  have hcancel : c ^ 2 * d ≤ (M * L) ^ 2 * r := by
    apply (mul_le_mul_iff_left₀ hdpos).mp
    calc
      _ = (c * d) ^ 2 := by ring
      _ ≤ B ^ 2 := hsep2
      _ ≤ _ := hg
  have hquot : d ≤ ((M * L) ^ 2 * r) / c ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    simpa only [mul_comm] using hcancel
  convert hquot using 1
  ring

variable {X : Type*} [MetricSpace X]

/-- Any slow norm-growth exponent at most one-half gives the squared
growth bound used in localization, at all coarser scales. -/
theorem squared_growth_of_slow_norm_growth (T S : E →L[ℝ] F) (w : E)
    {d r M a : ℝ} (hr : 0 < r) (hdr : r ≤ d) (hM : 0 ≤ M) (ha : a ≤ 1 / 2)
    (hslow : ‖S w‖ ≤ M * (d / r) ^ a * ‖T w‖) :
    ‖S w‖ ^ 2 ≤ M ^ 2 * (d / r) * ‖T w‖ ^ 2 := by
  have hratio : 1 ≤ d / r := (le_div_iff₀ hr).mpr (by simpa using hdr)
  have hratio0 : 0 ≤ d / r := (by norm_num : (0 : ℝ) ≤ 1).trans hratio
  have hpower : ((d / r) ^ a) ^ (2 : ℕ) ≤ d / r := by
    rw [← Real.rpow_mul_natCast hratio0 a 2]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hratio (show a * (2 : ℕ) ≤ 1 by norm_num; linarith)
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg hM (Real.rpow_nonneg hratio0 _)) (norm_nonneg _))).mpr hslow
  calc
    _ ≤ (M * (d / r) ^ a * ‖T w‖) ^ 2 := hs
    _ = M ^ 2 * (((d / r) ^ a) ^ (2 : ℕ)) * ‖T w‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpower (sq_nonneg M)) (sq_nonneg _)

/-- Active support forces an original-metric distance bound. Separation
and comparison are only required when the distance exceeds the fine scale,
so nearby pairs need no coarse-scale selection. -/
theorem active_cutoff_distance_le (u : X → E) (T S : E →L[ℝ] F)
    (psi : F → ℝ) (x y : X) {r c M L : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hL : 0 ≤ L)
    (hsupport : tsupport psi ⊆ Metric.closedBall 0 L)
    (hactive : u x ∈ tsupport (fun P => psi (r⁻¹ • T (P - u y))))
    (hseparate : r < dist x y → c * dist x y ≤ ‖S (u x - u y)‖)
    (hgrowth : r < dist x y →
      ‖S (u x - u y)‖ ^ 2 ≤ M ^ 2 * (dist x y / r) * ‖T (u x - u y)‖ ^ 2) :
    dist x y ≤ max 1 ((M * L / c) ^ 2) * r := by
  by_cases hnear : dist x y ≤ r
  · exact hnear.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (le_max_left 1 ((M * L / c) ^ 2)) hr.le)
  have hfar : r < dist x y := lt_of_not_ge hnear
  have hloc := distance_le_of_normalization_growth dist_nonneg hr hc hL
    (norm_nonneg _) (norm_nonneg _)
    (normalized_cutoff_support_norm_le T (u y) (u x) psi hr hsupport hactive)
    (hseparate hfar) (hgrowth hfar)
  exact hloc.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le)

/-- The same localization, stated directly with the manuscript's slow
power growth instead of its squared consequence. -/
theorem active_cutoff_distance_le_of_slow_growth (u : X → E) (T S : E →L[ℝ] F)
    (psi : F → ℝ) (x y : X) {r c M L a : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hM : 0 ≤ M) (hL : 0 ≤ L) (ha : a ≤ 1 / 2)
    (hsupport : tsupport psi ⊆ Metric.closedBall 0 L)
    (hactive : u x ∈ tsupport (fun P => psi (r⁻¹ • T (P - u y))))
    (hseparate : r < dist x y → c * dist x y ≤ ‖S (u x - u y)‖)
    (hslow : r < dist x y →
      ‖S (u x - u y)‖ ≤ M * (dist x y / r) ^ a * ‖T (u x - u y)‖) :
    dist x y ≤ max 1 ((M * L / c) ^ 2) * r := by
  apply active_cutoff_distance_le u T S psi x y hr hc hL hsupport hactive hseparate
  intro hfar
  exact squared_growth_of_slow_norm_growth T S (u x - u y) hr hfar.le hM ha (hslow hfar)

/-- The cutoff equals one on the fine normalized core. -/
theorem normalized_cutoff_eq_one_of_norm_le (T : E →L[ℝ] F) (psi : F → ℝ)
    (c P : E) {r L : ℝ} (hr : 0 < r)
    (hcore : ∀ v, ‖v‖ ≤ L → psi v = 1)
    (hnorm : ‖T (P - c)‖ ≤ L * r) :
    psi (r⁻¹ • T (P - c)) = 1 := by
  apply hcore
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have h := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hr.le)
  calc
    _ ≤ r⁻¹ * (L * r) := h
    _ = L := by field_simp [hr.ne']

/-- Net covering produces an active weight-one patch. Its enlarged source
ball covers the testing ball, exactly as required for the lower cumulative
mass comparison. -/
theorem exists_weight_one_covering_patch (A : Set X) (hA : TotallyBounded A)
    (r : ℝ≥0) (hr : 0 < r) (u : X → E) (T : X → E →L[ℝ] F)
    (psi : F → ℝ) (hcore : ∀ v, ‖v‖ ≤ 2 → psi v = 1)
    (hnear : ∀ x ∈ A, ∀ y ∈ maximalPatchNet r A, dist x y ≤ r →
      ‖T y (u x - u y)‖ ≤ 2 * r)
    (x : X) (hx : x ∈ A) {L : ℝ} (hL : 2 ≤ L) :
    ∃ y ∈ maximalPatchNet r A,
      dist x y ≤ r ∧ psi ((r : ℝ)⁻¹ • T y (u x - u y)) = 1 ∧
      u x ∈ tsupport (fun P => psi ((r : ℝ)⁻¹ • T y (P - u y))) ∧
      Metric.ball x r ⊆ Metric.ball y (L * r) := by
  obtain ⟨y, hy, hxy⟩ := maximalPatchNet_covers (ne_of_gt hr) hA x hx
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hvalue := normalized_cutoff_eq_one_of_norm_le (T y) psi (u y) (u x)
    hr' hcore (hnear x hx y hy hxy)
  refine ⟨y, hy, hxy, hvalue, ?_, ?_⟩
  · apply subset_tsupport
    change psi ((r : ℝ)⁻¹ • T y (u x - u y)) ≠ 0
    rw [hvalue]
    norm_num
  · apply Metric.ball_subset_ball'
    have hm := mul_le_mul_of_nonneg_right hL hr'.le
    linarith

section Volume

variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The overlap bound for the actual normalized cutoffs: active-center
distance is derived from support, harmonic separation, and normalization
growth before the disjoint-ball volume count is applied. -/
theorem active_normalized_cutoff_card_le (μ : Measure X) (A : Set X)
    (r : ℝ≥0) (u : X → E) (T S : X → E →L[ℝ] F) (psi : F → ℝ)
    (x : X) (n : ℕ) (hr : 0 < r) {c M L a b : ℝ}
    (hc : 0 < c) (hL : 0 ≤ L) (ha : 0 < a)
    (hsupport : tsupport psi ⊆ Metric.closedBall 0 L)
    (hseparate : ∀ y ∈ maximalPatchNet r A, (r : ℝ) < dist x y →
      c * dist x y ≤ ‖S y (u x - u y)‖)
    (hgrowth : ∀ y ∈ maximalPatchNet r A, (r : ℝ) < dist x y →
      ‖S y (u x - u y)‖ ^ 2 ≤ M ^ 2 * (dist x y / r) * ‖T y (u x - u y)‖ ^ 2)
    (hlower : ∀ y ∈ maximalPatchNet r A,
      a * ((r : ℝ) / 2) ^ n ≤ μ.real (Metric.ball y (r / 2)))
    (hupper : μ.real (Metric.ball x (max 1 ((M * L / c) ^ 2) * r + r / 2)) ≤
      b * (max 1 ((M * L / c) ^ 2) * r + r / 2) ^ n)
    (hfinite : μ (Metric.ball x (max 1 ((M * L / c) ^ 2) * r + r / 2)) ≠ ∞) :
    ((maximalPatchNet r A).filter (fun y =>
      u x ∈ tsupport (fun P => psi ((r : ℝ)⁻¹ • T y (P - u y))))).card ≤
      ⌈b / a * (2 * max 1 ((M * L / c) ^ 2) + 1) ^ n⌉₊ := by
  classical
  apply active_maximalPatchNet_card_le μ A r x _ n hr ha
  · intro y hy hactive
    have hh := active_cutoff_distance_le u (T y) (S y) psi x y
      (show 0 < (r : ℝ) by exact_mod_cast hr) hc hL hsupport hactive
      (hseparate y hy) (hgrowth y hy)
    simpa only [dist_comm] using hh
  · intro y hy _
    exact hlower y hy
  · exact hupper
  · exact hfinite

end Volume

end RegularPointCoordinates

end

end OAI
