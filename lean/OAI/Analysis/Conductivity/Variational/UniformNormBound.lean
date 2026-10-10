import Mathlib
import OAI.Analysis.Conductivity.Variational.SmoothCompose

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

section
open Filter Topology

lemma uniform_zero_norm_of_bound {X I V : Type*} [NormedAddCommGroup V]
    {l : Filter I} {f : I → X → V} {b : I → ℝ}
    (hb : Tendsto b l (𝓝 0)) (hf : ∀ᶠ i in l, ∀ x, ‖f i x‖ ≤ b i) :
    TendstoUniformly f (fun _ => 0) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hf, hb.eventually_lt_const hε] with i hi hib x
  simpa only [dist_zero_left] using (hi x).trans_lt hib

lemma nonlinearFirstPotential_fderiv_error_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (hχ : HasCompactSupport χ.val) (hH : ∃ C : ℝ, ∀ t, |H.val t| ≤ C) :
    TendstoUniformly
      (fun k x => fderiv ℝ (nonlinearFirstPotential χ φ H k).val x -
        (χ.val x * (smoothDirection 1 H).val (k * φ.val x)) • fderiv ℝ φ.val x)
      (fun _ => 0) atTop := by
  obtain ⟨A, hA⟩ := ((smoothScalar_contDiff χ).continuous_fderiv (by simp))
    |>.bounded_above_of_compact_support (hχ.fderiv (𝕜 := ℝ))
  obtain ⟨B, hB⟩ := hH
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  apply uniform_zero_norm_of_bound (b := fun k : ℝ => |k⁻¹| * B * A)
  · simpa using ((tendsto_inv_atTop_zero.abs.mul_const B).mul_const A)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk x
    rw [nonlinearFirstPotential_fderiv χ φ H hk.ne', add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)) (hA x)
      (norm_nonneg _) (mul_nonneg (abs_nonneg _) hB0)

lemma scalar_cutoff_segment {a b c z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c ∧ c ≤ 1) (hz : -a ≤ z ∧ z ≤ b) :
    -a ≤ c * z ∧ c * z ≤ b := by
  constructor
  · calc
      -a ≤ c * (-a) := by nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) ha]
      _ ≤ c * z := mul_le_mul_of_nonneg_left hz.1 hc.1
  · calc
      c * z ≤ c * b := mul_le_mul_of_nonneg_left hz.2 hc.1
      _ ≤ b := by nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) hb]

lemma nonlinear_phase_leading_positive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E) (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (hχb : ∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1)
    {a b c m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (_hm : 0 < m) (hpath : ∀ z ∈ Set.Icc (-a) b, m ≤ 1 + c * z)
    (hH : ∀ t, -a ≤ (smoothDirection 1 H).val t ∧ (smoothDirection 1 H).val t ≤ b)
    (hphase : ∀ x ∈ tsupport χ.val,
      |(smoothDirection d φ).val x - 1| ≤ m / (2 * (|c| + 1))) :
    ∀ k x, m / 2 ≤ 1 + c *
      ((smoothDirection d φ).val x * χ.val x * (smoothDirection 1 H).val (k * φ.val x)) := by
  intro k x
  let z := χ.val x * (smoothDirection 1 H).val (k * φ.val x)
  have hz := scalar_cutoff_segment ha hb (hχb x) (hH (k * φ.val x))
  change -a ≤ z ∧ z ≤ b at hz
  have hzabs : |z| ≤ 1 := abs_le.mpr ⟨by linarith only [hz.1, ha1],
    by linarith only [hz.2, hb1]⟩
  have hp := hpath z hz
  by_cases hx : x ∈ tsupport χ.val
  · have hden : 0 < 2 * (|c| + 1) := by positivity
    have hd := (le_div_iff₀ hden).mp (hphase x hx)
    have he : |c * ((smoothDirection d φ).val x - 1) * z| ≤ m / 2 := by
      rw [abs_mul, abs_mul]
      have hmul : |c| * |(smoothDirection d φ).val x - 1| ≤ m / 2 := by
        nlinarith only [hd, abs_nonneg ((smoothDirection d φ).val x - 1)]
      exact (mul_le_mul_of_nonneg_left hzabs (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans
        (by simpa using hmul)
    have hlow := (abs_le.mp he).1
    change m / 2 ≤ 1 + c * ((smoothDirection d φ).val x * χ.val x * _)
    have hzdef : (smoothDirection d φ).val x * χ.val x *
        (smoothDirection 1 H).val (k * φ.val x) = (smoothDirection d φ).val x * z := by
      dsimp [z]; ring
    rw [hzdef]
    nlinarith only [hp, hlow]
  · have hzero := image_eq_zero_of_notMem_tsupport hx
    have hm1 := hpath 0 ⟨by linarith, hb⟩
    simp only [hzero, mul_zero, zero_mul, add_zero]
    linarith only [hm1, _hm]

end

open Set Filter Topology

lemma lineShift_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : E) {f : E → ℝ} {x : E} {L : E →L[ℝ] ℝ} (hf : HasFDerivAt f L x) :
    HasFDerivAt (lineShift d f) (ContinuousLinearMap.id ℝ E + L.smulRight d) x := by
  exact (hasFDerivAt_id x).add (hf.smul_const d)

def lineShiftGradientOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : E) (c : ℝ) : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E) :=
  c • (ContinuousLinearMap.smulRightL ℝ E E).flip d

lemma lineShiftGradientOperator_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E) (c : ℝ) (L : E →L[ℝ] ℝ) :
    lineShiftGradientOperator d c L = c • L.smulRight d := rfl

lemma nonlinearLineShift_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E) (c k : ℝ) (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (x : E) :
    fderiv ℝ (lineShift d (c • nonlinearFirstPotential χ φ H k).val) x =
      ContinuousLinearMap.id ℝ E + lineShiftGradientOperator d c
        (fderiv ℝ (nonlinearFirstPotential χ φ H k).val x) := by
  rw [(lineShift_hasFDerivAt d
    ((smoothScalar_contDiff (c • nonlinearFirstPotential χ φ H k)).differentiable
      (by simp) x).hasFDerivAt).fderiv]
  congr 1
  ext v
  change fderiv ℝ (fun y => c • (nonlinearFirstPotential χ φ H k).val y) x v • d = _
  have hs := (((smoothScalar_contDiff (nonlinearFirstPotential χ φ H k)).differentiable
    (by simp) x).hasFDerivAt.const_smul c).fderiv
  change (fderiv ℝ (c • (nonlinearFirstPotential χ φ H k).val) x) v • d = _
  rw [hs]
  simp [lineShiftGradientOperator, smul_smul]

lemma nonlinearLineShift_fderiv_error_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E) (c : ℝ) (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (hχ : HasCompactSupport χ.val) (hH : ∃ B : ℝ, ∀ t, |H.val t| ≤ B) :
    TendstoUniformly
      (fun k x => fderiv ℝ (lineShift d (c • nonlinearFirstPotential χ φ H k).val) x -
        (ContinuousLinearMap.id ℝ E + lineShiftGradientOperator d c
          ((χ.val x * (smoothDirection 1 H).val (k * φ.val x)) • fderiv ℝ φ.val x)))
      (fun _ => 0) atTop := by
  have ht := (lineShiftGradientOperator d c).uniformContinuous.comp_tendstoUniformly
    (nonlinearFirstPotential_fderiv_error_tendsto χ φ H hχ hH)
  simpa only [Function.comp_def, map_sub, map_zero, nonlinearLineShift_fderiv,
    add_sub_add_left_eq_sub] using ht

lemma equiv_image_set_of_eq_off {E : Type*} (X : E ≃ E) (V : Set E)
    (h : ∀ x ∉ V, X x = x) : X '' V = V := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_contra hy
    have he := X.injective (h (X x) hy)
    exact hy (by simpa only [he] using hx)
  · intro hy
    refine ⟨X.symm y, ?_, X.apply_symm_apply y⟩
    by_contra hx
    have he : y = X.symm y := (X.apply_symm_apply y).symm.trans (h _ hx)
    exact hx (he ▸ hy)

theorem exists_local_phase_diffeomorphisms
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (d : E) (φ : SmoothScalar E)
    {p : E} {L : E →L[ℝ] ℝ} (hLp : fderiv ℝ φ.val p = L) (hLd : L d = 1)
    {a b c m ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hm : 0 < m) (hε : 0 < ε)
    (hpath : ∀ z ∈ Icc (-a) b, m ≤ 1 + c * z)
    {U : Set E} (hU : IsOpen U) (hp : p ∈ U) :
    ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      ∀ H : SmoothScalar ℝ, (∃ B : ℝ, ∀ t, |H.val t| ≤ B) →
        (∀ t, -a ≤ (smoothDirection 1 H).val t ∧ (smoothDirection 1 H).val t ≤ b) →
      ∀ χ : SmoothScalar E, HasCompactSupport χ.val → tsupport χ.val ⊆ V →
        (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) →
        ∀ᶠ k : ℝ in atTop, ∃ X : E ≃ E,
          (∀ x, X x = lineShift d (c • nonlinearFirstPotential χ φ H k).val x) ∧
          ContDiff ℝ (↑(⊤ : ℕ∞)) X ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) X.symm ∧
          (∀ x ∉ V, X x = x) ∧ X '' V = V ∧
          ∀ x, ‖fderiv ℝ X x -
            (ContinuousLinearMap.id ℝ E + lineShiftGradientOperator d c
              ((χ.val x * (smoothDirection 1 H).val (k * φ.val x)) • L))‖ < ε := by
  let T := lineShiftGradientOperator d c
  let δ := min (ε / (2 * (‖T‖ + 1))) (m / (2 * (|c| + 1) * (‖d‖ + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hevent : ∀ᶠ x in 𝓝 p, ‖fderiv ℝ φ.val x - L‖ < δ := by
    simpa only [dist_eq_norm, hLp] using
      ((smoothScalar_contDiff φ).continuous_fderiv (by simp)).continuousAt.eventually
        (Metric.ball_mem_nhds (fderiv ℝ φ.val p) hδ)
  obtain ⟨W, hW, hWo, hpW⟩ := mem_nhds_iff.mp hevent
  let V := U ∩ W
  refine ⟨V, hU.inter hWo, ⟨hp, hpW⟩, inter_subset_left, ?_⟩
  intro H hH hHr χ hχ hχV hχb
  have hphase : ∀ x ∈ tsupport χ.val,
      |(smoothDirection d φ).val x - 1| ≤ m / (2 * (|c| + 1)) := by
    intro x hx
    have hd := (fderiv ℝ φ.val x - L).le_opNorm d
    change ‖(fderiv ℝ φ.val x) d - L d‖ ≤ ‖fderiv ℝ φ.val x - L‖ * ‖d‖ at hd
    rw [hLd, Real.norm_eq_abs] at hd
    change |(fderiv ℝ φ.val x) d - 1| ≤ _
    have hsmall := (show ‖fderiv ℝ φ.val x - L‖ < δ from hW (hχV hx).2).le.trans (min_le_right _ _)
    have hden : 0 < 2 * (|c| + 1) * (‖d‖ + 1) := by positivity
    have hmul := (le_div_iff₀ hden).mp hsmall
    apply (le_div_iff₀ (by positivity : 0 < 2 * (|c| + 1))).mpr
    nlinarith only [hd, hmul, norm_nonneg (fderiv ℝ φ.val x - L), abs_nonneg c]
  have hpos := nonlinear_phase_leading_positive d χ φ H hχb ha hb ha1 hb1 hm hpath hHr hphase
  have hmaps := nonlinearFirstPotential_diffeomorphisms d χ φ H hχ hH c (m/2)
    (half_pos hm) hpos
  have he := (Metric.tendstoUniformly_iff.mp
    (nonlinearLineShift_fderiv_error_tendsto d c χ φ H hχ hH)) (ε/2) (half_pos hε)
  filter_upwards [hmaps, he] with k hk hke
  obtain ⟨X, hX, hXs, hXi⟩ := hk
  have hXeq : (X : E → E) = lineShift d (c • nonlinearFirstPotential χ φ H k).val :=
    funext hX
  have hoff : ∀ x ∉ V, X x = x := by
    intro x hx
    have hz : (nonlinearFirstPotential χ φ H k).val x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hx (hχV (nonlinearFirstPotential_support χ φ H k ht)))
    rw [hX]
    simp only [hz, mul_zero, zero_smul, add_zero]
  refine ⟨X, hX, hXs, hXi, hoff, equiv_image_set_of_eq_off X V hoff, ?_⟩
  intro x
  let z := χ.val x * (smoothDirection 1 H).val (k * φ.val x)
  have he1 : ‖fderiv ℝ X x - (ContinuousLinearMap.id ℝ E + T (z • fderiv ℝ φ.val x))‖ < ε/2 := by
    simpa only [hXeq, dist_zero_left] using hke x
  have he2 : ‖(ContinuousLinearMap.id ℝ E + T (z • fderiv ℝ φ.val x)) -
      (ContinuousLinearMap.id ℝ E + T (z • L))‖ ≤ ε/2 := by
    rw [add_sub_add_left_eq_sub, ← map_sub, ← smul_sub z (fderiv ℝ φ.val x) L, map_smul, norm_smul, Real.norm_eq_abs]
    by_cases hx : x ∈ tsupport χ.val
    · have hz := scalar_cutoff_segment ha hb (hχb x) (hHr (k * φ.val x))
      change -a ≤ z ∧ z ≤ b at hz
      have hza : |z| ≤ 1 := abs_le.mpr ⟨by linarith only [hz.1, ha1], by linarith only [hz.2, hb1]⟩
      have hsmall := (show ‖fderiv ℝ φ.val x - L‖ < δ from hW (hχV hx).2).le.trans (min_le_left _ _)
      have hbound := T.le_opNorm (fderiv ℝ φ.val x - L)
      have hden : 0 < 2 * (‖T‖ + 1) := by positivity
      have hmul := (le_div_iff₀ hden).mp hsmall
      have hbnd : ‖T (fderiv ℝ φ.val x - L)‖ ≤ ε/2 := by
        nlinarith only [hbound, hmul, norm_nonneg (fderiv ℝ φ.val x - L)]
      exact (mul_le_mul_of_nonneg_right hza (norm_nonneg _)).trans (by simpa using hbnd)
    · have hz : z = 0 := by dsimp [z]; rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
      rw [hz, abs_zero, zero_mul]
      exact (half_pos hε).le
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_lt (by linarith only [he1, he2])

end ScalarConductivity

end

end OAI
