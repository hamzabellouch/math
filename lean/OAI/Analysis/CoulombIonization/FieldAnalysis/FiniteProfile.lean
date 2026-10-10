import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.SommerfeldCoefficient

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
namespace CoulombPDE

structure FiniteProfile (d Z : ℝ) (F : Space → ℝ) : Prop where
  regular : ∀ x, x ≠ 0 → ContDiffAt ℝ 2 F x
  equation : ∀ x, x ≠ 0 → Δ F x = reaction d (F x)
  decay : ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → |F x| < ε
  nucleus : ∃ C > 0, ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → |F x - Z / ‖x‖| ≤ C

lemma FiniteProfile.near_pos {d Z : ℝ} {F : Space → ℝ} (h : FiniteProfile d Z F)
    (hZ : 0 < Z) : ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → 0 ≤ F x := by
  obtain ⟨C, hC, a, ha, hn⟩ := h.nucleus
  refine ⟨min a (Z / (C + 1)), lt_min ha (div_pos hZ (by linarith)), ?_⟩
  intro x hx hxa
  have hh := (abs_le.mp (hn x hx (hxa.trans (min_le_left _ _)))).1
  have hxr := (le_div_iff₀ (show 0 < C + 1 by linarith)).mp (hxa.trans (min_le_right _ _))
  have hz : C ≤ Z / ‖x‖ := (le_div_iff₀ (norm_pos_iff.mpr hx)).mpr (by nlinarith [norm_nonneg x])
  linarith

lemma FiniteProfile.nonneg {d Z : ℝ} {F : Space → ℝ} (h : FiniteProfile d Z F)
    (hZ : 0 < Z) (x : Space) (hx : x ≠ 0) : 0 ≤ F x := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let u : Space → ℝ := fun y => -F y - δ
  have hreg (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 u y :=
    (h.regular y hy).neg.sub contDiffAt_const
  have hl (y : Space) (hy : y ≠ 0) (hp : 0 < u y) : 0 ≤ Δ u y := by
    have hf : F y ≤ 1 := by dsimp [u] at hp; linarith
    have he : reaction d (F y) = 0 := by simp [reaction, max_eq_right (sub_nonpos.mpr hf)]
    change 0 ≤ Δ ((-F) - (fun _ : Space => δ)) y
    have hn : ContDiffAt ℝ 2 (-F) y := (h.regular y hy).neg
    rw [hn.laplacian_sub (show ContDiffAt ℝ 2 (fun _ : Space => δ) y from contDiffAt_const),
      laplacian_neg, Pi.neg_apply, laplacian_const, Pi.zero_apply, h.equation y hy, he]
    norm_num
  have hnear : ∃ a > 0, ∀ y, y ≠ 0 → ‖y‖ ≤ a → u y ≤ 0 := by
    obtain ⟨a, ha, hb⟩ := h.near_pos hZ
    exact ⟨a, ha, fun y hy hr => by dsimp [u]; linarith [hb y hy hr]⟩
  have hfar : ∃ R > 0, ∀ y, R ≤ ‖y‖ → u y ≤ 0 := by
    obtain ⟨R, hR, hb⟩ := h.decay δ hδ
    exact ⟨R, hR, fun y hy => by dsimp [u]; linarith [(abs_lt.mp (hb y hy)).1]⟩
  have hh := global_punctured_maximum_principle hreg hl hnear hfar x hx
  dsimp [u] at hh
  linarith

lemma FiniteProfile.compare {d Z W : ℝ} {F G : Space → ℝ}
    (hF : FiniteProfile d Z F) (hG : FiniteProfile d W G) (hd : 0 ≤ d) (hZW : Z < W)
    (x : Space) (hx : x ≠ 0) : F x ≤ G x := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let u : Space → ℝ := fun y => F y - (G y + δ)
  have hgd (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 (G + fun _ : Space => δ) y :=
    (hG.regular y hy).add contDiffAt_const
  have hdif (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 u y := (hF.regular y hy).sub (hgd y hy)
  have hl (y : Space) (hy : y ≠ 0) (hp : 0 < u y) : 0 ≤ Δ u y := by
    have hfg : G y ≤ F y := by dsimp [u] at hp; linarith
    change 0 ≤ Δ (F - (G + fun _ : Space => δ)) y
    rw [(hF.regular y hy).laplacian_sub (hgd y hy),
      (hG.regular y hy).laplacian_add (show ContDiffAt ℝ 2 (fun _ : Space => δ) y from contDiffAt_const),
      laplacian_const, Pi.zero_apply, add_zero, hF.equation y hy, hG.equation y hy]
    exact sub_nonneg.mpr (reaction_monotone hd hfg)
  have hnear : ∃ a > 0, ∀ y, y ≠ 0 → ‖y‖ ≤ a → u y ≤ 0 := by
    obtain ⟨C, hC, a, ha, hnF⟩ := hF.nucleus
    obtain ⟨D, hD, b, hb, hnG⟩ := hG.nucleus
    refine ⟨min (min a b) ((W-Z)/(C+D+1)),
      lt_min (lt_min ha hb) (div_pos (sub_pos.mpr hZW) (by linarith)), ?_⟩
    intro y hy hr
    have hFa := (abs_le.mp (hnF y hy (hr.trans ((min_le_left _ _).trans (min_le_left _ _))))).2
    have hGa := (abs_le.mp (hnG y hy (hr.trans ((min_le_left _ _).trans (min_le_right _ _))))).1
    have hsmall := (le_div_iff₀ (show 0 < C+D+1 by linarith)).mp (hr.trans (min_le_right _ _))
    have hgap : C+D ≤ (W-Z)/‖y‖ := (le_div_iff₀ (norm_pos_iff.mpr hy)).mpr (by nlinarith [norm_nonneg y])
    rw [sub_div] at hgap
    dsimp [u]
    linarith
  have hfar : ∃ R > 0, ∀ y, R ≤ ‖y‖ → u y ≤ 0 := by
    obtain ⟨a, ha, hFa⟩ := hF.decay (δ/2) (by positivity)
    obtain ⟨b, hb, hGb⟩ := hG.decay (δ/2) (by positivity)
    refine ⟨max a b, ha.trans_le (le_max_left _ _), ?_⟩
    intro y hy
    have hf := abs_lt.mp (hFa y ((le_max_left _ _).trans hy))
    have hg := abs_lt.mp (hGb y ((le_max_right _ _).trans hy))
    dsimp [u]
    linarith
  have hh := global_punctured_maximum_principle hdif hl hnear hfar x hx
  dsimp [u] at hh
  linarith

lemma FiniteProfile.upper {d Z : ℝ} {F : Space → ℝ}
    (hF : FiniteProfile d Z F) (hd : 0 < d) (x : Space) (hx : x ≠ 0) :
    F x ≤ 1 + sommerfeldCoefficient d * radialPower (-2) x := by
  let A := sommerfeldCoefficient d
  have hA : 0 < A := sommerfeldCoefficient_pos hd
  let G := radialCombination A 0 0 1
  have hG (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 G y := radialCombination_contDiffAt _ _ _ _ hy
  have hGl (y : Space) (hy : y ≠ 0) : Δ G y ≤ reaction d (G y) := by
    apply upper_barrier_laplacian hd.le hA (by norm_num) le_rfl
      (le_of_eq (sommerfeldCoefficient_half hd).symm)
    · simpa using le_of_eq (sommerfeldCoefficient_half hd).symm
    · exact hy
  let u : Space → ℝ := fun y => F y - G y
  have hud (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 u y := (hF.regular y hy).sub (hG y hy)
  have hul (y : Space) (hy : y ≠ 0) (hp : 0 < u y) : 0 ≤ Δ u y := by
    change 0 ≤ Δ (F-G) y
    rw [(hF.regular y hy).laplacian_sub (hG y hy), hF.equation y hy]
    have hm := reaction_monotone hd.le (show G y ≤ F y by dsimp [u] at hp; linarith)
    linarith [hGl y hy]
  have hnear : ∃ a > 0, ∀ y, y ≠ 0 → ‖y‖ ≤ a → u y ≤ 0 := by
    obtain ⟨C, hC, a, ha, hn⟩ := hF.nucleus
    refine ⟨min (min a 1) (A/(|Z|+C+1)),
      lt_min (lt_min ha zero_lt_one) (div_pos hA (by positivity)), ?_⟩
    intro y hy hr
    have hrp := norm_pos_iff.mpr hy
    have hr1 : ‖y‖ ≤ 1 := hr.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hn' := (abs_le.mp (hn y hy (hr.trans ((min_le_left _ _).trans (min_le_left _ _))))).2
    have hs := (le_div_iff₀ (show 0 < |Z|+C+1 by positivity)).mp (hr.trans (min_le_right _ _))
    have hr3 : ‖y‖^3 ≤ ‖y‖ := by nlinarith [sq_nonneg ‖y‖, mul_nonneg (norm_nonneg y) (sub_nonneg.mpr hr1)]
    have hr4 : ‖y‖^4 ≤ ‖y‖ := by
      calc
        ‖y‖^4 = ‖y‖^3 * ‖y‖ := by ring
        _ ≤ ‖y‖ * ‖y‖ := mul_le_mul_of_nonneg_right hr3 (norm_nonneg _)
        _ ≤ ‖y‖ := by nlinarith
    have hf : ‖y‖^4 * F y ≤ Z * ‖y‖^3 + C * ‖y‖^4 := by
      have hh := mul_le_mul_of_nonneg_left hn' (pow_nonneg (norm_nonneg y) 4)
      have he : ‖y‖^4 * (F y - Z/‖y‖) = ‖y‖^4 * F y - Z * ‖y‖^3 := by field_simp
      rw [he] at hh
      linarith
    have hz : Z * ‖y‖^3 ≤ |Z| * ‖y‖ :=
      (mul_le_mul_of_nonneg_right (le_abs_self Z) (pow_nonneg (norm_nonneg y) 3)).trans
        (mul_le_mul_of_nonneg_left hr3 (abs_nonneg Z))
    have hb : ‖y‖^4 * F y ≤ A := by nlinarith [mul_le_mul_of_nonneg_left hr4 hC.le]
    have hg : ‖y‖^4 * (A * radialPower (-2) y) = A := by nlinarith [norm_four_mul_radialPower hy]
    have hh : F y ≤ A * radialPower (-2) y := (mul_le_mul_iff_right₀ (pow_pos hrp 4)).mp (by nlinarith)
    dsimp [u, G, radialCombination]
    linarith
  have hfar : ∃ R > 0, ∀ y, R ≤ ‖y‖ → u y ≤ 0 := by
    obtain ⟨R, hR, hb⟩ := hF.decay 1 zero_lt_one
    refine ⟨R, hR, ?_⟩
    intro y hy
    have hf := (abs_lt.mp (hb y hy)).2
    have hp := mul_nonneg hA.le (radialPower_nonneg (-2) y)
    dsimp [u, G, radialCombination]
    linarith
  have hh := global_punctured_maximum_principle hud hul hnear hfar x hx
  dsimp [u, G, radialCombination, A] at hh
  linarith

end CoulombPDE

end

end OAI
