import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.RadialPower

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
namespace CoulombPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

lemma lower_barrier_laplacian {d B e s c c₀ F : ℝ} (hd : 0 ≤ d)
    (he : 0 ≤ e) (hs : 0 ≤ s) (hc : 0 ≤ c) (hc₀ : 0 < c₀)
    (hq : d * B ^ (1 / 2 : ℝ) ≤ 12)
    (hκ : (14 * s + 4 * s ^ 2) * B ≤ (12 - d * B ^ (1 / 2 : ℝ)) * c₀)
    {x : Space} (hx : x ≠ 0) (hlow : c₀ * radialPower (-2) x ≤ F)
    (hgt : F < radialCombination B (-e) s (-c) x) :
    reaction d F ≤ Δ (radialCombination B (-e) s (-c)) x := by
  let z := e * radialPower (-s) x
  let v := B - z
  have hz : 0 ≤ z := mul_nonneg he (radialPower_nonneg _ _)
  have hp := radialPower_pos (-2) hx
  have hfac : radialCombination B (-e) s (-c) x = radialPower (-2) x * v - c := by
    rw [radialCombination_factor _ _ _ _ hx]; dsimp [v, z]; ring
  have hv : c₀ < v := by
    rw [hfac] at hgt
    nlinarith
  have hvpos : 0 < v := hc₀.trans hv
  have hvB : v ≤ B := by dsimp [v]; linarith
  have hzB : z ≤ B := by dsimp [v] at hvpos; linarith
  have hf : max (F - 1) 0 ≤ radialPower (-2) x * v := by
    apply max_le
    · rw [hfac] at hgt; linarith
    · positivity
  have hcoeff : 0 ≤ 14 * s + 4 * s ^ 2 := by positivity
  have hscalar : d * B ^ (1 / 2 : ℝ) * v ≤ 12 * B - (12 + 14 * s + 4 * s ^ 2) * z := by
    have h1 := mul_le_mul_of_nonneg_left hzB hcoeff
    have h2 := mul_le_mul_of_nonneg_left hv.le (sub_nonneg.mpr hq)
    dsimp [v] at *
    nlinarith
  calc
    reaction d F ≤ d * (radialPower (-2) x * v) ^ (3 / 2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_max_right _ _) hf (by norm_num)) hd
    _ = radialPower (-3) x * (d * v ^ (3 / 2 : ℝ)) := by
      rw [radial_scaled_reaction hvpos.le]; ring
    _ ≤ radialPower (-3) x * (d * B ^ (1 / 2 : ℝ) * v) := by
      apply mul_le_mul_of_nonneg_left _ (radialPower_nonneg _ _)
      have h := mul_le_mul_of_nonneg_left (rpow_three_halves_upper hvpos.le hvB) hd
      nlinarith
    _ ≤ radialPower (-3) x * (12 * B - (12 + 14 * s + 4 * s ^ 2) * z) :=
      mul_le_mul_of_nonneg_left hscalar (radialPower_nonneg _ _)
    _ = Δ (radialCombination B (-e) s (-c)) x := by
      rw [radialCombination_laplacian _ _ _ _ hx]; dsimp [z]; ring

theorem singular_upper_bound {F : Space → ℝ} {d C R B : ℝ}
    (hd : 0 < d) (hC : 0 ≤ C) (hR : 0 < R) (hB : 0 < B)
    (hq : 12 < d * B ^ (1 / 2 : ℝ))
    (hreg : ∀ x, x ≠ 0 → ‖x‖ ≤ R → ContDiffAt ℝ 2 F x)
    (hpde : ∀ x, x ≠ 0 → ‖x‖ ≤ R → Δ F x = reaction d (F x))
    (hupper : ∀ x, x ≠ 0 → ‖x‖ ≤ R → F x ≤ C * radialPower (-2) x) :
    ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      F x ≤ B * radialPower (-2) x + C * (R ^ 2) ^ (-2 : ℝ) + 1 := by
  obtain ⟨s, hs, hκ⟩ := exists_small_exponent hq
  let c : ℝ := C * (R ^ 2) ^ (-2 : ℝ)
  have hc : 0 ≤ c := mul_nonneg hC (Real.rpow_nonneg (sq_nonneg R) _)
  have heBound (e : ℝ) (he : 0 < e) : ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      F x ≤ radialCombination B e s (c + 1) x := by
    have hm := punctured_ball_maximum_principle (u := F - radialCombination B e s (c + 1))
      (fun x hx hr => (hreg x hx hr).sub (radialCombination_contDiffAt _ _ _ _ hx))
      (fun x hx hr hp => ?_) (fun x hx => ?_) ?_
    · intro x hx hr
      exact sub_nonpos.mp (hm x hx hr)
    · rw [(hreg x hx hr).laplacian_sub (radialCombination_contDiffAt _ _ _ _ hx), hpde x hx hr]
      have hu := upper_barrier_laplacian hd.le hB he.le (by linarith : 1 ≤ c + 1) hq.le hκ hx
      have hmon := reaction_monotone hd.le (show radialCombination B e s (c + 1) x ≤ F x by
        exact le_of_lt (sub_pos.mp hp))
      linarith
    · have hx0 : x ≠ 0 := norm_pos_iff.mp (hx ▸ hR)
      have hu := hupper x hx0 hx.le
      have hrad : C * radialPower (-2) x = c := by simp only [radialPower, hx, c]
      rw [hrad] at hu
      have h1 := radialPower_nonneg (-2 : ℝ) x
      have h2 := radialPower_nonneg (-2 - s) x
      change F x - radialCombination B e s (c + 1) x ≤ 0
      unfold radialCombination
      nlinarith [mul_nonneg hB.le h1, mul_nonneg he.le h2]
    · obtain ⟨a, ha, hsmall⟩ := exists_small_radialPower_bound (E := Space) hs (C / e)
      refine ⟨min a R, lt_min ha hR, ?_⟩
      intro x hx hxa
      have ht := hsmall x hx (hxa.trans (min_le_left _ _))
      have hu := hupper x hx (hxa.trans (min_le_right _ _))
      have heC : C ≤ e * radialPower (-s) x := by
        have ht' := (div_le_iff₀ he).mp ht
        nlinarith
      change F x - radialCombination B e s (c + 1) x ≤ 0
      rw [radialCombination_factor _ _ _ _ hx]
      nlinarith [mul_nonneg (radialPower_nonneg (-2) x) (sub_nonneg.mpr heC),
        mul_nonneg hB.le (radialPower_nonneg (-2) x)]
  intro x hx hr
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hp := radialPower_pos (-2 - s) hx
  have h := heBound (δ / radialPower (-2 - s) x) (div_pos hδ hp) x hx hr
  unfold radialCombination at h
  rw [div_mul_cancel₀ _ hp.ne'] at h
  change F x ≤ B * radialPower (-2) x + c + 1 + δ
  linarith

theorem singular_lower_bound {F : Space → ℝ} {d c₀ R B : ℝ}
    (hd : 0 < d) (hc₀ : 0 < c₀) (hR : 0 < R) (hB : 0 < B)
    (hq : d * B ^ (1 / 2 : ℝ) < 12)
    (hreg : ∀ x, x ≠ 0 → ‖x‖ ≤ R → ContDiffAt ℝ 2 F x)
    (hpde : ∀ x, x ≠ 0 → ‖x‖ ≤ R → Δ F x = reaction d (F x))
    (hlower : ∀ x, x ≠ 0 → ‖x‖ ≤ R → c₀ * radialPower (-2) x ≤ F x) :
    ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      B * radialPower (-2) x - B * (R ^ 2) ^ (-2 : ℝ) ≤ F x := by
  let q := d * B ^ (1 / 2 : ℝ)
  have hgap : 0 < (12 - q) * c₀ / B := div_pos (mul_pos (sub_pos.mpr hq) hc₀) hB
  obtain ⟨s, hs, hsκ⟩ := exists_small_exponent (show 12 < 12 + (12 - q) * c₀ / B by linarith)
  have hκ : (14 * s + 4 * s ^ 2) * B ≤ (12 - q) * c₀ := by
    apply (le_div_iff₀ hB).mp
    linarith
  let c : ℝ := B * (R ^ 2) ^ (-2 : ℝ)
  have hc : 0 ≤ c := mul_nonneg hB.le (Real.rpow_nonneg (sq_nonneg R) _)
  have heBound (e : ℝ) (he : 0 < e) : ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      radialCombination B (-e) s (-c) x ≤ F x := by
    have hm := punctured_ball_maximum_principle (u := radialCombination B (-e) s (-c) - F)
      (fun x hx hr => (radialCombination_contDiffAt _ _ _ _ hx).sub (hreg x hx hr))
      (fun x hx hr hp => ?_) (fun x hx => ?_) ?_
    · intro x hx hr
      exact sub_nonpos.mp (hm x hx hr)
    · rw [(radialCombination_contDiffAt _ _ _ _ hx).laplacian_sub (hreg x hx hr), hpde x hx hr]
      exact sub_nonneg.mpr (lower_barrier_laplacian hd.le he.le hs.le hc hc₀ hq.le hκ hx
        (hlower x hx hr) (sub_pos.mp hp))
    · have hx0 : x ≠ 0 := norm_pos_iff.mp (hx ▸ hR)
      have hl := hlower x hx0 hx.le
      have hrad : B * radialPower (-2) x = c := by simp only [radialPower, hx, c]
      change radialCombination B (-e) s (-c) x - F x ≤ 0
      unfold radialCombination
      rw [hrad]
      nlinarith [mul_nonneg hc₀.le (radialPower_nonneg (-2) x),
        mul_nonneg he.le (radialPower_nonneg (-2 - s) x)]
    · obtain ⟨a, ha, hsmall⟩ := exists_small_radialPower_bound (E := Space) hs (B / e)
      refine ⟨min a R, lt_min ha hR, ?_⟩
      intro x hx hxa
      have ht := hsmall x hx (hxa.trans (min_le_left _ _))
      have hl := hlower x hx (hxa.trans (min_le_right _ _))
      have heB : B ≤ e * radialPower (-s) x := by
        have ht' := (div_le_iff₀ he).mp ht
        nlinarith
      change radialCombination B (-e) s (-c) x - F x ≤ 0
      rw [radialCombination_factor _ _ _ _ hx]
      nlinarith [mul_nonneg (radialPower_nonneg (-2) x) (sub_nonneg.mpr heB),
        mul_nonneg hc₀.le (radialPower_nonneg (-2) x)]
  intro x hx hr
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hp := radialPower_pos (-2 - s) hx
  have h := heBound (δ / radialPower (-2 - s) x) (div_pos hδ hp) x hx hr
  unfold radialCombination at h
  rw [neg_mul, div_mul_cancel₀ _ hp.ne'] at h
  change B * radialPower (-2) x - c ≤ F x + δ
  linarith

def sommerfeldCoefficient (d : ℝ) : ℝ := (12 / d) ^ 2

lemma sommerfeldCoefficient_pos {d : ℝ} (hd : 0 < d) : 0 < sommerfeldCoefficient d := by
  unfold sommerfeldCoefficient
  positivity

lemma sommerfeldCoefficient_half {d : ℝ} (hd : 0 < d) :
    d * (sommerfeldCoefficient d) ^ (1 / 2 : ℝ) = 12 := by
  have hp : 0 ≤ 12 / d := by positivity
  unfold sommerfeldCoefficient
  rw [← Real.rpow_natCast (12 / d) 2, ← Real.rpow_mul hp]
  norm_num
  field_simp

lemma norm_four_mul_radialPower {x : Space} (hx : x ≠ 0) :
    ‖x‖ ^ 4 * radialPower (-2) x = 1 := by
  rw [radialPower, Real.rpow_neg (sq_nonneg ‖x‖) 2, Real.rpow_two]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp

theorem sommerfeld_asymptotic {F : Space → ℝ} {d c C R : ℝ}
    (hd : 0 < d) (hc : 0 < c) (hC : 0 ≤ C) (hR : 0 < R)
    (hreg : ∀ x, x ≠ 0 → ‖x‖ ≤ R → ContDiffAt ℝ 2 F x)
    (hpde : ∀ x, x ≠ 0 → ‖x‖ ≤ R → Δ F x = reaction d (F x))
    (hlower : ∀ x, x ≠ 0 → ‖x‖ ≤ R → c * radialPower (-2) x ≤ F x)
    (hupper : ∀ x, x ≠ 0 → ‖x‖ ≤ R → F x ≤ C * radialPower (-2) x) :
    Tendsto (fun x => ‖x‖ ^ 4 * F x) (𝓝[≠] (0 : Space)) (𝓝 (sommerfeldCoefficient d)) := by
  have hA : 0 < sommerfeldCoefficient d := sommerfeldCoefficient_pos hd
  have hn : Tendsto (fun x : Space => ‖x‖) (𝓝[≠] (0 : Space)) (𝓝 0) := by
    simpa only [norm_zero] using (continuous_norm.continuousAt.tendsto (x := (0 : Space))).mono_left nhdsWithin_le_nhds
  have hfour : Tendsto (fun x : Space => ‖x‖ ^ 4) (𝓝[≠] (0 : Space)) (𝓝 0) := by
    simpa using hn.pow 4
  have hball : ∀ᶠ x : Space in 𝓝[≠] (0 : Space), x ≠ 0 ∧ ‖x‖ ≤ R := by
    have hsmall : ∀ᶠ x : Space in 𝓝 (0 : Space), ‖x‖ < R := by
      filter_upwards [Metric.ball_mem_nhds (0 : Space) hR] with x hx
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with x hx hr
    exact ⟨hx, hr.le⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨B, hB₁, hB₂⟩ := exists_between (max_lt hA ha)
    have hB : 0 < B := (le_max_left _ _).trans_lt hB₁
    have haB : a < B := (le_max_right _ _).trans_lt hB₁
    have hq : d * B ^ (1 / 2 : ℝ) < 12 := by
      have h := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hB.le hB₂ (by norm_num : (0 : ℝ) < 1 / 2)) hd
      rwa [sommerfeldCoefficient_half hd] at h
    let D := B * (R ^ 2) ^ (-2 : ℝ)
    have ht : Tendsto (fun x : Space => B - ‖x‖ ^ 4 * D) (𝓝[≠] (0 : Space)) (𝓝 B) := by
      simpa using tendsto_const_nhds.sub (hfour.mul_const D)
    have he := ht.eventually (eventually_gt_nhds haB)
    filter_upwards [hball, he] with x hx he
    have hl := singular_lower_bound hd hc hR hB hq hreg hpde hlower x hx.1 hx.2
    have hmul := mul_le_mul_of_nonneg_left hl (pow_nonneg (norm_nonneg x) 4)
    have hu := norm_four_mul_radialPower hx.1
    dsimp [D] at he
    nlinarith
  · intro b hb
    obtain ⟨B, hB₁, hB₂⟩ := exists_between hb
    have hB : 0 < B := hA.trans hB₁
    have hq : 12 < d * B ^ (1 / 2 : ℝ) := by
      have h := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hA.le hB₁ (by norm_num : (0 : ℝ) < 1 / 2)) hd
      rwa [sommerfeldCoefficient_half hd] at h
    let D := C * (R ^ 2) ^ (-2 : ℝ) + 1
    have ht : Tendsto (fun x : Space => B + ‖x‖ ^ 4 * D) (𝓝[≠] (0 : Space)) (𝓝 B) := by
      simpa using tendsto_const_nhds.add (hfour.mul_const D)
    have he := ht.eventually (eventually_lt_nhds hB₂)
    filter_upwards [hball, he] with x hx he
    have hl := singular_upper_bound hd hC hR hB hq hreg hpde hupper x hx.1 hx.2
    have hmul := mul_le_mul_of_nonneg_left hl (pow_nonneg (norm_nonneg x) 4)
    have hu := norm_four_mul_radialPower hx.1
    dsimp [D] at he
    nlinarith

structure SingularProfile (d : ℝ) (F : Space → ℝ) : Prop where
  regular : ∀ x, x ≠ 0 → ContDiffAt ℝ 2 F x
  equation : ∀ x, x ≠ 0 → Δ F x = reaction d (F x)
  decay : ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → |F x| < ε
  bounds : ∃ c > 0, ∃ C > 0, ∃ R > 0,
    (∀ x, x ≠ 0 → ‖x‖ ≤ R → c * radialPower (-2) x ≤ F x) ∧
    (∀ x, x ≠ 0 → ‖x‖ ≤ R → F x ≤ C * radialPower (-2) x)

lemma SingularProfile.asymptotic {d : ℝ} {F : Space → ℝ} (h : SingularProfile d F)
    (hd : 0 < d) :
    Tendsto (fun x => ‖x‖ ^ 4 * F x) (𝓝[≠] (0 : Space)) (𝓝 (sommerfeldCoefficient d)) := by
  obtain ⟨c, hc, C, hC, R, hR, hl, hu⟩ := h.bounds
  exact sommerfeld_asymptotic hd hc hC.le hR (fun x hx _ => h.regular x hx)
    (fun x hx _ => h.equation x hx) hl hu

lemma reaction_superlinear {d α δ v : ℝ} (hd : 0 ≤ d) (hα : 1 ≤ α) (hδ : 0 ≤ δ) :
    α * reaction d v ≤ reaction d (α * v + δ) := by
  have hα₀ : 0 ≤ α := by linarith
  have hm : α * max (v - 1) 0 ≤ max (α * v + δ - 1) 0 := by
    by_cases hv : v ≤ 1
    · rw [max_eq_right (sub_nonpos.mpr hv), mul_zero]
      exact le_max_right _ _
    · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hv))]
      apply le_trans _ (le_max_left _ _)
      nlinarith
  have hpow : α ≤ α ^ (3 / 2 : ℝ) := by
    simpa using rpow_three_halves_lower (by norm_num : (0 : ℝ) ≤ 1) hα
  unfold reaction
  calc
    α * (d * max (v - 1) 0 ^ (3 / 2 : ℝ))
        = d * (α * max (v - 1) 0 ^ (3 / 2 : ℝ)) := by ring
    _ ≤ d * (α ^ (3 / 2 : ℝ) * max (v - 1) 0 ^ (3 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hd
      exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (le_max_right _ _) _)
    _ = d * (α * max (v - 1) 0) ^ (3 / 2 : ℝ) := by
      rw [Real.mul_rpow hα₀ (le_max_right _ _)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hα₀ (le_max_right _ _)) hm (by norm_num)) hd

lemma deleted_eventually_to_small_ball {P : Space → Prop}
    (h : ∀ᶠ x in 𝓝[≠] (0 : Space), P x) :
    ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → P x := by
  obtain ⟨a, ha, hbound⟩ := Metric.mem_nhdsWithin_iff.mp h
  refine ⟨a / 2, by positivity, ?_⟩
  intro x hx hxa
  apply hbound
  refine ⟨?_, hx⟩
  simpa only [Metric.mem_ball, dist_zero_right] using (show ‖x‖ < a by linarith)

theorem global_punctured_maximum_principle {u : Space → ℝ}
    (hd : ∀ x, x ≠ 0 → ContDiffAt ℝ 2 u x)
    (hl : ∀ x, x ≠ 0 → 0 < u x → 0 ≤ Δ u x)
    (hz : ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → u x ≤ 0)
    (hinfty : ∃ R > 0, ∀ x, R ≤ ‖x‖ → u x ≤ 0) :
    ∀ x, x ≠ 0 → u x ≤ 0 := by
  obtain ⟨R, _hR, hfar⟩ := hinfty
  intro x hx
  by_cases hxr : R ≤ ‖x‖
  · exact hfar x hxr
  · exact punctured_ball_maximum_principle (fun y hy _ => hd y hy)
      (fun y hy _ => hl y hy) (fun y hy => hfar y hy.ge) hz x hx (le_of_not_ge hxr)

lemma SingularProfile.scaled_comparison {d α δ : ℝ} {F₁ F₂ : Space → ℝ}
    (h₁ : SingularProfile d F₁) (h₂ : SingularProfile d F₂)
    (hd : 0 < d) (hα : 1 < α) (hδ : 0 < δ) :
    ∀ x, x ≠ 0 → F₂ x ≤ α * F₁ x + δ := by
  let G : Space → ℝ := fun x => α * F₁ x + δ
  have hG (x : Space) (hx : x ≠ 0) : ContDiffAt ℝ 2 G x :=
    (contDiffAt_const.mul (h₁.regular x hx)).add contDiffAt_const
  have hGlap (x : Space) (hx : x ≠ 0) : Δ G x ≤ reaction d (G x) := by
    have hm : ContDiffAt ℝ 2 (α • F₁) x := contDiffAt_const.smul (h₁.regular x hx)
    change (Δ (α • F₁ + fun _ => δ) : Space → ℝ) x ≤ reaction d (α * F₁ x + δ)
    rw [hm.laplacian_add (show ContDiffAt ℝ 2 (fun _ : Space => δ) x from contDiffAt_const),
      laplacian_smul α (h₁.regular x hx), laplacian_const, Pi.zero_apply, add_zero, h₁.equation x hx]
    exact reaction_superlinear hd.le hα.le hδ.le
  have hnear : ∀ᶠ x in 𝓝[≠] (0 : Space), F₂ x - G x ≤ 0 := by
    have ht : Tendsto (fun x : Space => ‖x‖ ^ 4 * (α * F₁ x - F₂ x))
        (𝓝[≠] (0 : Space)) (𝓝 ((α - 1) * sommerfeldCoefficient d)) := by
      convert ((h₁.asymptotic hd).const_mul α).sub (h₂.asymptotic hd) using 1 <;> (try funext x) <;> ring_nf
    have hp : 0 < (α - 1) * sommerfeldCoefficient d :=
      mul_pos (sub_pos.mpr hα) (sommerfeldCoefficient_pos hd)
    filter_upwards [ht.eventually (eventually_gt_nhds hp), self_mem_nhdsWithin] with x hx hxn
    have hn : 0 < ‖x‖ ^ 4 := pow_pos (norm_pos_iff.mpr hxn) _
    have hu : 0 < α * F₁ x - F₂ x := (mul_pos_iff_of_pos_left hn).mp hx
    dsimp [G]
    linarith
  have hfar : ∃ R > 0, ∀ x, R ≤ ‖x‖ → F₂ x - G x ≤ 0 := by
    let ε := δ / (2 * (α + 1))
    have he : 0 < ε := div_pos hδ (by linarith)
    have heq : ε * (2 * (α + 1)) = δ := by
      exact div_mul_cancel₀ _ (by linarith)
    obtain ⟨R₁, hR₁, hb₁⟩ := h₁.decay ε he
    obtain ⟨R₂, _hR₂, hb₂⟩ := h₂.decay ε he
    refine ⟨max R₁ R₂, hR₁.trans_le (le_max_left _ _), ?_⟩
    intro x hx
    have h1 := (abs_lt.mp (hb₁ x ((le_max_left _ _).trans hx))).1
    have h2 := (abs_lt.mp (hb₂ x ((le_max_right _ _).trans hx))).2
    dsimp [G]
    nlinarith [mul_nonneg (show 0 ≤ α by linarith) (show 0 ≤ F₁ x + ε by linarith)]
  have hm := global_punctured_maximum_principle
    (u := F₂ - G) (fun x hx => (h₂.regular x hx).sub (hG x hx))
    (fun x hx hp => ?_) (deleted_eventually_to_small_ball hnear) hfar
  · exact fun x hx => sub_nonpos.mp (hm x hx)
  · rw [(h₂.regular x hx).laplacian_sub (hG x hx), h₂.equation x hx]
    have hmon := reaction_monotone hd.le (le_of_lt (sub_pos.mp hp))
    linarith [hGlap x hx]

theorem singular_profile_unique {d : ℝ} {F₁ F₂ : Space → ℝ}
    (hd : 0 < d) (h₁ : SingularProfile d F₁) (h₂ : SingularProfile d F₂) :
    EqOn F₁ F₂ ({0}ᶜ) := by
  have hle {F G : Space → ℝ} (hF : SingularProfile d F) (hG : SingularProfile d G)
      (x : Space) (hx : x ≠ 0) : G x ≤ F x := by
    have hscaled (α : ℝ) (hα : 1 < α) : G x ≤ α * F x := by
      apply le_of_forall_pos_le_add
      intro δ hδ
      exact hF.scaled_comparison hG hd hα hδ x hx
    have ht : Tendsto (fun t : ℝ => (1 + t) * F x) (𝓝[>] 0) (𝓝 (F x)) := by
      have h : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
      simpa using (h.const_add 1).mul_const (F x)
    apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hscaled (1 + t) (by change 0 < t at ht; linarith)
  intro x hx
  exact le_antisymm (hle h₂ h₁ x hx) (hle h₁ h₂ x hx)

lemma laplacian_comp_isometry {f : E → ℝ} (e : E ≃ₗᵢ[ℝ] E) (x : E)
    (hf : ContDiffAt ℝ 2 f (e x)) : Δ (fun y => f (e y)) x = Δ f (e x) := by
  have hc : ContDiffAt ℝ 2 (fun y => f (e y)) x := hf.comp x e.contDiff.contDiffAt
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f ((stdOrthonormalBasis ℝ E).map e)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, OrthonormalBasis.map_apply]
  rw [← second_deriv_line hc, ← second_deriv_line hf]
  congr 2
  funext t
  simp only [map_add, map_smul]

lemma SingularProfile.comp_isometry {d : ℝ} {F : Space → ℝ}
    (h : SingularProfile d F) (e : Space ≃ₗᵢ[ℝ] Space) :
    SingularProfile d (fun x => F (e x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (h.regular (e x) (fun he => hx (e.map_eq_zero_iff.mp he))).comp x
      e.contDiff.contDiffAt
  · intro x hx
    rw [laplacian_comp_isometry e x (h.regular _ (fun he => hx (e.map_eq_zero_iff.mp he)))]
    exact h.equation _ (fun he => hx (e.map_eq_zero_iff.mp he))
  · intro ε hε
    obtain ⟨R, hR, hb⟩ := h.decay ε hε
    exact ⟨R, hR, fun x hx => hb (e x) (by simpa using hx)⟩
  · obtain ⟨c, hc, C, hC, R, hR, hl, hu⟩ := h.bounds
    refine ⟨c, hc, C, hC, R, hR, ?_, ?_⟩
    · intro x hx hr
      simpa [radialPower] using hl (e x) (fun he => hx (e.map_eq_zero_iff.mp he)) (by simpa using hr)
    · intro x hx hr
      simpa [radialPower] using hu (e x) (fun he => hx (e.map_eq_zero_iff.mp he)) (by simpa using hr)

theorem SingularProfile.rotation_invariant {d : ℝ} {F : Space → ℝ}
    (hd : 0 < d) (h : SingularProfile d F) (e : Space ≃ₗᵢ[ℝ] Space)
    (x : Space) (hx : x ≠ 0) : F (e x) = F x :=
  singular_profile_unique hd (h.comp_isometry e) h hx

theorem SingularProfile.radial {d : ℝ} {F : Space → ℝ}
    (hd : 0 < d) (h : SingularProfile d F) {x y : Space} (hxy : ‖x‖ = ‖y‖) :
    F x = F y := by
  by_cases hx : x = 0
  · have hy : y = 0 := norm_eq_zero.mp (by simpa [hx] using hxy.symm)
    simp [hx, hy]
  · have hr := h.rotation_invariant hd (Submodule.reflection (ℝ ∙ (x - y))ᗮ) x hx
    rw [Submodule.reflection_sub hxy] at hr
    exact hr.symm

end CoulombPDE

end

end OAI
