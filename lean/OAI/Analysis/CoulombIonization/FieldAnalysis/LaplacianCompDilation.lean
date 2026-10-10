import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.FiniteProfile

namespace OAI

noncomputable section

namespace CoulombPDE

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
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma laplacian_comp_dilation {f : E → ℝ} (a : ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f (a • x)) : Δ (fun y => f (a • y)) x = a^2 * Δ f (a • x) := by
  have hc : ContDiffAt ℝ 2 (fun y => f (a • y)) x := hf.comp x (contDiffAt_id.const_smul a)
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← second_deriv_line hc]
  have he : (fun t : ℝ => f (a • (x + t • (stdOrthonormalBasis ℝ E) i))) =
      (fun t : ℝ => f (a • x + t • (a • (stdOrthonormalBasis ℝ E) i))) := by
    funext t
    simp only [smul_add, smul_smul, mul_comm]
  rw [he, second_deriv_line hf]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

end

open Filter Set Metric Topology InnerProductSpace Laplacian

lemma compare_subsolution_finite {d Z W : ℝ} {L G : Space → ℝ}
    (hd : 0 ≤ d) (hW : 0 < W) (hZW : Z < W) (hG : FiniteProfile d W G)
    (hreg : ∀ x, x ≠ 0 → ContDiffAt ℝ 2 L x)
    (hpde : ∀ x, x ≠ 0 → reaction d (L x) ≤ Δ L x)
    (hnear : ∃ C > 0, ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → L x ≤ Z/‖x‖ + C)
    (hfar : ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → L x ≤ ε)
    (x : Space) (hx : x ≠ 0) : L x ≤ G x := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let u : Space → ℝ := fun y => L y - (G y + δ)
  have hgd (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 (G + fun _ : Space => δ) y :=
    (hG.regular y hy).add contDiffAt_const
  have hud (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 u y := (hreg y hy).sub (hgd y hy)
  have hul (y : Space) (hy : y ≠ 0) (hp : 0 < u y) : 0 ≤ Δ u y := by
    have hlg : G y ≤ L y := by dsimp [u] at hp; linarith
    change 0 ≤ Δ (L - (G + fun _ : Space => δ)) y
    rw [(hreg y hy).laplacian_sub (hgd y hy),
      (hG.regular y hy).laplacian_add (show ContDiffAt ℝ 2 (fun _ : Space => δ) y from contDiffAt_const),
      laplacian_const, Pi.zero_apply, add_zero, hG.equation y hy]
    linarith [reaction_monotone hd hlg, hpde y hy]
  have hn : ∃ a > 0, ∀ y, y ≠ 0 → ‖y‖ ≤ a → u y ≤ 0 := by
    obtain ⟨C, hC, a, ha, hL⟩ := hnear
    obtain ⟨D, hD, b, hb, hG'⟩ := hG.nucleus
    refine ⟨min (min a b) ((W-Z)/(C+D+1)),
      lt_min (lt_min ha hb) (div_pos (sub_pos.mpr hZW) (by linarith)), ?_⟩
    intro y hy hr
    have hl := hL y hy (hr.trans ((min_le_left _ _).trans (min_le_left _ _)))
    have hg := (abs_le.mp (hG' y hy (hr.trans ((min_le_left _ _).trans (min_le_right _ _))))).1
    have hsmall := (le_div_iff₀ (show 0 < C+D+1 by linarith)).mp (hr.trans (min_le_right _ _))
    have hgap : C+D ≤ (W-Z)/‖y‖ := (le_div_iff₀ (norm_pos_iff.mpr hy)).mpr (by nlinarith [norm_nonneg y])
    rw [sub_div] at hgap
    dsimp [u]
    linarith
  have hf : ∃ R > 0, ∀ y, R ≤ ‖y‖ → u y ≤ 0 := by
    obtain ⟨R, hR, hb⟩ := hfar (δ/2) (by positivity)
    refine ⟨R, hR, fun y hy => ?_⟩
    have hz : y ≠ 0 := norm_pos_iff.mp (hR.trans_le hy)
    dsimp [u]
    linarith [hb y hy, hG.nonneg hW y hz]
  have hh := global_punctured_maximum_principle hud hul hn hf x hx
  dsimp [u] at hh
  linarith

def shiftedDilation (a : ℝ) (F : Space → ℝ) (x : Space) : ℝ := a^4*F (a • x) + (1-a^4)

lemma reaction_shiftedDilation {a : ℝ} (ha : 0 < a) (d v : ℝ) :
    reaction d (a^4*v + (1-a^4)) = a^6 * reaction d v := by
  unfold reaction
  rw [show a^4*v+(1-a^4)-1 = a^4*(v-1) by ring]
  rw [show max (a^4*(v-1)) 0 = a^4 * max (v-1) 0 by
    rw [mul_max_of_nonneg _ _ (pow_nonneg ha.le _), mul_zero]]
  rw [Real.mul_rpow (pow_nonneg ha.le _) (le_max_right _ _)]
  have hp : (a^4)^(3/2:ℝ) = a^6 := by
    rw [← Real.rpow_natCast a 4, ← Real.rpow_mul ha.le]
    norm_num
  rw [hp]
  ring

lemma FiniteProfile.shifted_dilation_regular {d Z : ℝ} {F : Space → ℝ}
    (hF : FiniteProfile d Z F) {a : ℝ} (ha : 0 < a) (x : Space) (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (shiftedDilation a F) x := by
  have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
  exact (((hF.regular _ hax).comp x (contDiffAt_id.const_smul a)).const_smul (a^4)).add contDiffAt_const

lemma FiniteProfile.shifted_dilation_equation {d Z : ℝ} {F : Space → ℝ}
    (hF : FiniteProfile d Z F) {a : ℝ} (ha : 0 < a) (x : Space) (hx : x ≠ 0) :
    Δ (shiftedDilation a F) x = reaction d (shiftedDilation a F x) := by
  have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
  have hc : ContDiffAt ℝ 2 (fun y : Space => F (a • y)) x :=
    (hF.regular _ hax).comp x (contDiffAt_id.const_smul a)
  have hs : Δ (fun y : Space => (a^4) • F (a • y)) x =
      (a^4) • Δ (fun y : Space => F (a • y)) x := laplacian_smul (a^4) hc
  change (Δ ((fun y : Space => (a^4) • F (a • y)) + (fun _ : Space => 1-a^4)) : Space → ℝ) x = _
  rw [(hc.const_smul (a^4)).laplacian_add
    (show ContDiffAt ℝ 2 (fun _ : Space => 1-a^4) x from contDiffAt_const),
    hs, laplacian_const, Pi.zero_apply, add_zero,
    laplacian_comp_dilation a x (hF.regular _ hax), hF.equation _ hax]
  rw [shiftedDilation, reaction_shiftedDilation ha]
  simp only [smul_eq_mul]
  ring

lemma FiniteProfile.shifted_dilation_near {d Z : ℝ} {F : Space → ℝ}
    (hF : FiniteProfile d Z F) {a : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∃ b > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ b → shiftedDilation a F x ≤ a^3*Z/‖x‖ + C := by
  obtain ⟨C, hC, b, hb, hn⟩ := hF.nucleus
  refine ⟨a^4*C+2, by positivity, b/a, div_pos hb ha, ?_⟩
  intro x hx hxb
  have hnorm : ‖a • x‖ = a*‖x‖ := by rw [norm_smul, Real.norm_of_nonneg ha.le]
  have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
  have htt : ‖a • x‖ ≤ b := by rw [hnorm]; nlinarith [(le_div_iff₀ ha).mp hxb]
  have hh := (abs_le.mp (hn _ hax htt)).2
  rw [hnorm] at hh
  have hi := mul_le_mul_of_nonneg_left hh (pow_nonneg ha.le 4)
  have he : a^4 * (Z/(a*‖x‖)) = a^3*Z/‖x‖ := by field_simp
  unfold shiftedDilation
  rw [mul_sub, he] at hi
  nlinarith [pow_nonneg ha.le 4]

lemma FiniteProfile.shifted_dilation_far {d Z : ℝ} {F : Space → ℝ}
    (hF : FiniteProfile d Z F) {a : ℝ} (ha : 1 ≤ a) :
    ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → shiftedDilation a F x ≤ ε := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  intro ε hε
  obtain ⟨R, hR, hb⟩ := hF.decay (ε/a^4) (by positivity)
  refine ⟨R/a, div_pos hR ha0, ?_⟩
  intro x hx
  have hh : R ≤ ‖a • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg ha0.le]
    nlinarith [(div_le_iff₀ ha0).mp hx]
  have hf := (abs_lt.mp (hb _ hh)).2
  have hg := (lt_div_iff₀ (pow_pos ha0 4)).mp hf
  have hp : 1 ≤ a^4 := one_le_pow₀ ha
  unfold shiftedDilation
  nlinarith

end CoulombPDE

end

end OAI
