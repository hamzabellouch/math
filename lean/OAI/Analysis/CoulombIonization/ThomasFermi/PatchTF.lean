import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.Pairing

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

abbrev TFField (R : ℝ) := Lp ℝ (5 / 2) (ballMeasure R)

def tfPatchPair (R : ℝ) : TFField R →L[ℝ] TFLp (ballMeasure R) →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing (ballMeasure R) (5 / 2) (5 / 3)

lemma tfPatchPair_apply (R : ℝ) (Φ : TFField R) (f : TFLp (ballMeasure R)) :
    tfPatchPair R Φ f = ∫ x, Φ x * f x ∂ballMeasure R := by
  exact ContinuousLinearMap.lpPairing_eq_integral ..

def tfPatchLinear (R : ℝ) (Φ : TFField R) : TFLp (ballMeasure R) →L[ℝ] ℝ :=
  -tfPatchPair R Φ

@[simp] lemma tfPatchLinear_apply (R : ℝ) (Φ : TFField R) (f : TFLp (ballMeasure R)) :
    tfPatchLinear R Φ f = -(∫ x, Φ x * f x ∂ballMeasure R) := by
  simp only [tfPatchLinear, neg_apply, tfPatchPair_apply]

def tfPatchFunctional (R T : ℝ) (Φ : TFField R) (f : TFLp (ballMeasure R)) : ℝ :=
  T * ‖f‖ ^ (5 / 3 : ℝ) + tfPatchLinear R Φ f + (1 / 2 : ℝ) * tfCoulombL R f f

lemma tfPatchFunctional_continuous (R T : ℝ) (Φ : TFField R) : Continuous (tfPatchFunctional R T Φ) := by
  apply Continuous.add
  · exact ((continuous_norm.rpow_const (fun _ => Or.inr (by norm_num))).const_mul T).add
      (tfPatchLinear R Φ).continuous
  · exact ((tfCoulombL R).continuous₂.comp (continuous_id.prodMk continuous_id)).const_mul _

lemma tfPatchFunctional_lower (R T : ℝ) (Φ : TFField R) (f : TFLp (ballMeasure R)) :
    T * ‖f‖ ^ (5 / 3 : ℝ) - ‖tfPatchLinear R Φ‖ * ‖f‖ ≤ tfPatchFunctional R T Φ f := by
  have hL := (tfPatchLinear R Φ).le_opNorm f
  have hn := neg_abs_le (tfPatchLinear R Φ f)
  have hD := tfCoulombL_nonneg R f
  change |tfPatchLinear R Φ f| ≤ _ at hL
  unfold tfPatchFunctional
  linarith

lemma tfPatchFunctional_bddBelow (R : ℝ) (Φ : TFField R) {T : ℝ} (hT : 0 < T) :
    BddBelow (Set.range (tfPatchFunctional R T Φ)) := by
  obtain ⟨B, hB0, hB⟩ := tf_power_dominates_linear hT ‖tfPatchLinear R Φ‖
  refine ⟨-‖tfPatchLinear R Φ‖ * B, ?_⟩
  rintro _ ⟨f, rfl⟩
  apply le_trans _ (tfPatchFunctional_lower R T Φ f)
  by_cases hb : B ≤ ‖f‖
  · exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (norm_nonneg _)) hB0).trans
      ((norm_nonneg _).trans (hB _ hb))
  · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hb) (norm_nonneg (tfPatchLinear R Φ))
    have hp := mul_nonneg hT.le (Real.rpow_nonneg (norm_nonneg f) (5 / 3 : ℝ))
    linarith

lemma tfPatchFunctional_coercive (R : ℝ) (Φ : TFField R) (a : ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ B : ℝ, ∀ f : TFLp (ballMeasure R), tfPatchFunctional R T Φ f ≤ a → ‖f‖ ≤ B := by
  obtain ⟨B, _, hB⟩ := tf_power_dominates_linear hT ‖tfPatchLinear R Φ‖
  refine ⟨max B a, fun f hf => ?_⟩
  by_cases hb : B ≤ ‖f‖
  · exact ((hB _ hb).trans ((tfPatchFunctional_lower R T Φ f).trans hf)).trans (le_max_right _ _)
  · exact (le_of_not_ge hb).trans (le_max_left _ _)

lemma tfPatchFunctional_gap (R T : ℝ) (Φ : TFField R) (hT : 0 ≤ T) {f g : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hg : NonnegDensity g) :
    (T * (5 / 36 : ℝ)) * densityWeight f g ≤
      (tfPatchFunctional R T Φ f + tfPatchFunctional R T Φ g) / 2 -
        tfPatchFunctional R T Φ ((1 / 2 : ℝ) • (f + g)) := by
  have hk := mul_le_mul_of_nonneg_left (tfLp_midpoint_gap hf hg) hT
  have hD := tfCoulombL_midpoint_gap R f g
  unfold tfPatchFunctional
  simp only [map_smul, map_add, smul_apply, add_apply, smul_eq_mul] at hD ⊢
  nlinarith

theorem tfPatchFunctional_exists_minimizer (R : ℝ) (Φ : TFField R) {T : ℝ} (hT : 0 < T) :
    ∃ f : TFLp (ballMeasure R), NonnegDensity f ∧
      ∀ g : TFLp (ballMeasure R), NonnegDensity g →
        tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ g := by
  apply exists_minimizer_of_tf_gap (C := {f | NonnegDensity f}) isClosed_nonnegDensity
  · refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ (5 / 3) (ballMeasure R)] with x hx
    rw [hx]
    exact le_rfl
  · exact fun _ hf => hf
  · exact fun _ hf _ hg => nonnegDensity_smul (nonnegDensity_add hf hg) (by norm_num)
  · exact (tfPatchFunctional_continuous R T Φ).continuousOn
  · exact (tfPatchFunctional_bddBelow R Φ hT).mono (Set.image_subset_range _ _)
  · intro a
    obtain ⟨B, hB⟩ := tfPatchFunctional_coercive R Φ a hT
    exact ⟨B, fun f _ hf => hB f hf⟩
  · exact mul_pos hT (by norm_num : (0 : ℝ) < 5 / 36)
  · exact fun _ hf _ hg => tfPatchFunctional_gap R T Φ hT.le hf hg

lemma tfPatchFunctional_min_unique (R : ℝ) (Φ : TFField R) {T : ℝ} (hT : 0 < T)
    {f g : TFLp (ballMeasure R)} (hf : NonnegDensity f) (hg : NonnegDensity g)
    (hminf : ∀ u, NonnegDensity u → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ u)
    (hming : ∀ u, NonnegDensity u → tfPatchFunctional R T Φ g ≤ tfPatchFunctional R T Φ u) : f = g := by
  have hh := nonnegDensity_smul (nonnegDensity_add hf hg) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h1 := hminf _ hh
  have h2 := hming _ hh
  have hgap := tfPatchFunctional_gap R T Φ hT.le hf hg
  have hw : densityWeight f g = 0 := by
    apply le_antisymm _ (densityWeight_nonneg hf hg)
    have hp : 0 < T * (5 / 36 : ℝ) := mul_pos hT (by norm_num)
    nlinarith
  have hi := tfLp_interpolation hf hg
  rw [hw, Real.zero_rpow (by norm_num : (5 / 6 : ℝ) ≠ 0), zero_mul] at hi
  have he := le_antisymm hi (Real.rpow_nonneg (norm_nonneg (f - g)) (5 / 3 : ℝ))
  have hz : ‖f - g‖ = 0 := (Real.rpow_eq_zero (norm_nonneg _) (by norm_num)).mp he
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

def tfPatchMinimizer (R T : ℝ) (hT : 0 < T) (Φ : TFField R) : TFLp (ballMeasure R) :=
  (tfPatchFunctional_exists_minimizer R Φ hT).choose

lemma tfPatchMinimizer_nonneg (R T : ℝ) (hT : 0 < T) (Φ : TFField R) :
    NonnegDensity (tfPatchMinimizer R T hT Φ) :=
  (tfPatchFunctional_exists_minimizer R Φ hT).choose_spec.1

lemma tfPatchMinimizer_min (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {f : TFLp (ballMeasure R)} (hf : NonnegDensity f) :
    tfPatchFunctional R T Φ (tfPatchMinimizer R T hT Φ) ≤ tfPatchFunctional R T Φ f :=
  (tfPatchFunctional_exists_minimizer R Φ hT).choose_spec.2 f hf

lemma nonnegDensity_zero (R : ℝ) : NonnegDensity (0 : TFLp (ballMeasure R)) := by
  filter_upwards [Lp.coeFn_zero ℝ (5/3) (ballMeasure R)] with x hx
  rw [hx]
  exact le_rfl

@[simp] lemma tfPatchFunctional_zero (R T : ℝ) (Φ : TFField R) :
    tfPatchFunctional R T Φ 0 = 0 := by
  simp only [tfPatchFunctional, map_zero, mul_zero, add_zero, norm_zero]
  rw [Real.zero_rpow (by norm_num : (5/3:ℝ) ≠ 0), mul_zero]

def tfPatchNormBound (R T : ℝ) (Φ : TFField R) : ℝ :=
  (‖tfPatchLinear R Φ‖ / T) ^ (3/2:ℝ)

lemma tfPatchMinimizer_norm_le (R T : ℝ) (hT : 0 < T) (Φ : TFField R) :
    ‖tfPatchMinimizer R T hT Φ‖ ≤ tfPatchNormBound R T Φ := by
  let f := tfPatchMinimizer R T hT Φ
  have hmin := tfPatchMinimizer_min R T hT Φ (nonnegDensity_zero R)
  rw [tfPatchFunctional_zero] at hmin
  have hlow := tfPatchFunctional_lower R T Φ f
  by_cases hz : ‖f‖ = 0
  · change ‖f‖ ≤ _
    rw [hz]
    exact Real.rpow_nonneg (div_nonneg (norm_nonneg _) hT.le) _
  have hr : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have he : ‖f‖ ^ (5/3:ℝ) = ‖f‖ * ‖f‖ ^ (2/3:ℝ) := by
    rw [show (5/3:ℝ) = 1+2/3 by norm_num, Real.rpow_add hr, Real.rpow_one]
  have hp : ‖f‖ ^ (2/3:ℝ) ≤ ‖tfPatchLinear R Φ‖ / T := by
    apply (le_div_iff₀ hT).mpr
    rw [he] at hlow
    nlinarith
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg f) (2/3:ℝ)) hp
    (show (0:ℝ) ≤ 3/2 by norm_num)
  rw [← Real.rpow_mul (norm_nonneg f)] at hh
  norm_num at hh
  exact hh

lemma tfPatchLinear_continuous (R : ℝ) : Continuous (tfPatchLinear R) :=
  (tfPatchPair R).continuous.neg

lemma tfPatchNormBound_continuous (R T : ℝ) : Continuous (tfPatchNormBound R T) :=
  (((tfPatchLinear_continuous R).norm).div_const T).rpow_const (fun _ => Or.inr (by norm_num))

lemma tfPatchNormBound_nonneg (R T : ℝ) (hT : 0 < T) (Φ : TFField R) :
    0 ≤ tfPatchNormBound R T Φ := Real.rpow_nonneg (by positivity) _

lemma tfPatchMinimizer_distance_rpow (R T : ℝ) (hT : 0 < T) (Φ Ψ : TFField R) :
    ‖tfPatchMinimizer R T hT Φ - tfPatchMinimizer R T hT Ψ‖ ^ (5/3:ℝ) ≤
      (‖tfPatchLinear R Φ - tfPatchLinear R Ψ‖ *
        (tfPatchNormBound R T Φ + tfPatchNormBound R T Ψ) / (2*(T*(5/36:ℝ)))) ^ (5/6:ℝ) *
      (tfPatchNormBound R T Φ + tfPatchNormBound R T Ψ) ^ (5/18:ℝ) := by
  have hBΦ := tfPatchNormBound_nonneg R T hT Φ
  have hBΨ := tfPatchNormBound_nonneg R T hT Ψ
  let f := tfPatchMinimizer R T hT Φ
  let g := tfPatchMinimizer R T hT Ψ
  have hf := tfPatchMinimizer_nonneg R T hT Φ
  have hg := tfPatchMinimizer_nonneg R T hT Ψ
  have hm := tfPatchMinimizer_min R T hT Φ
    (nonnegDensity_smul (nonnegDensity_add hf hg) (show (0:ℝ) ≤ 1/2 by norm_num))
  have hgap := tfPatchFunctional_gap R T Φ hT.le hf hg
  have hgmin := tfPatchMinimizer_min R T hT Ψ hf
  have hdiff : tfPatchFunctional R T Φ g - tfPatchFunctional R T Φ f ≤
      (tfPatchLinear R Φ - tfPatchLinear R Ψ) (g-f) := by
    simp only [tfPatchFunctional] at hgmin ⊢
    simp only [sub_apply, map_sub]
    dsimp only [f,g]
    nlinarith
  have hD := (tfPatchLinear R Φ - tfPatchLinear R Ψ).le_opNorm (g-f)
  have hs : ‖g-f‖ ≤ tfPatchNormBound R T Φ + tfPatchNormBound R T Ψ := by
    have hb1 : ‖f‖ ≤ tfPatchNormBound R T Φ := tfPatchMinimizer_norm_le R T hT Φ
    have hb2 : ‖g‖ ≤ tfPatchNormBound R T Ψ := tfPatchMinimizer_norm_le R T hT Ψ
    exact (norm_sub_le g f).trans (by linarith)
  have hupper : (tfPatchLinear R Φ - tfPatchLinear R Ψ) (g-f) ≤
      ‖tfPatchLinear R Φ - tfPatchLinear R Ψ‖ *
        (tfPatchNormBound R T Φ + tfPatchNormBound R T Ψ) :=
    (le_abs_self _).trans (hD.trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _)))
  have hc : 0 < 2*(T*(5/36:ℝ)) := by positivity
  have hw : densityWeight f g ≤ ‖tfPatchLinear R Φ - tfPatchLinear R Ψ‖ *
      (tfPatchNormBound R T Φ + tfPatchNormBound R T Ψ) / (2*(T*(5/36:ℝ))) := by
    apply (le_div_iff₀ hc).mpr
    dsimp only [f,g] at *
    linarith
  have hib := tfLp_interpolation hf hg
  have hsum : ‖f+g‖ ≤ tfPatchNormBound R T Φ + tfPatchNormBound R T Ψ :=
    (norm_add_le f g).trans (add_le_add (tfPatchMinimizer_norm_le R T hT Φ)
      (tfPatchMinimizer_norm_le R T hT Ψ))
  apply hib.trans
  exact mul_le_mul (Real.rpow_le_rpow (densityWeight_nonneg hf hg) hw (by norm_num))
    (Real.rpow_le_rpow (norm_nonneg _) hsum (by norm_num))
    (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (by positivity) _)

theorem tfPatchMinimizer_continuous (R T : ℝ) (hT : 0 < T) :
    Continuous (tfPatchMinimizer R T hT) := by
  apply continuous_iff_continuousAt.mpr
  intro Φ
  have hL := (tfPatchLinear_continuous R).continuousAt (x := Φ)
  have hB := (tfPatchNormBound_continuous R T).continuousAt (x := Φ)
  have h0 : Tendsto (fun Ψ => ‖tfPatchLinear R Ψ - tfPatchLinear R Φ‖)
      (𝓝 Φ) (𝓝 0) := by simpa using (hL.sub_const (tfPatchLinear R Φ)).norm
  have hu : Tendsto (fun Ψ =>
      (‖tfPatchLinear R Ψ - tfPatchLinear R Φ‖ *
        (tfPatchNormBound R T Ψ + tfPatchNormBound R T Φ) / (2*(T*(5/36:ℝ)))) ^ (5/6:ℝ) *
      (tfPatchNormBound R T Ψ + tfPatchNormBound R T Φ) ^ (5/18:ℝ))
      (𝓝 Φ) (𝓝 0) := by
    have ha := ((h0.mul (hB.add_const (tfPatchNormBound R T Φ))).div_const
      (2*(T*(5/36:ℝ)))).rpow_const (Or.inr (by norm_num : (0:ℝ) ≤ 5/6))
    have hb := (hB.add_const (tfPatchNormBound R T Φ)).rpow_const
      (Or.inr (by norm_num : (0:ℝ) ≤ 5/18))
    simpa using ha.mul hb
  have hp : Tendsto (fun Ψ =>
      ‖tfPatchMinimizer R T hT Ψ - tfPatchMinimizer R T hT Φ‖ ^ (5/3:ℝ))
      (𝓝 Φ) (𝓝 0) :=
    squeeze_zero (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      (fun Ψ => tfPatchMinimizer_distance_rpow R T hT Ψ Φ) hu
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := hp.rpow_const (Or.inr (by norm_num : (0:ℝ) ≤ 3/5))
  simpa only [← Real.rpow_mul (norm_nonneg _), show (5/3:ℝ)*(3/5) = 1 by norm_num,
    Real.rpow_one, Real.zero_rpow (by norm_num : (3/5:ℝ) ≠ 0)] using hh

local instance (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
local instance (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma tfPatchMinimizer_measurable (R T : ℝ) (hT : 0 < T) :
    Measurable (tfPatchMinimizer R T hT) := (tfPatchMinimizer_continuous R T hT).measurable

end CoulombAnalysis

end

end OAI
