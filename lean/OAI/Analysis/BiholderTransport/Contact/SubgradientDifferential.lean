import Mathlib
import OAI.Analysis.BiholderTransport.Contact.Subgradient

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma quadraticTaylor_increment (f0 : ℝ) (p : E) (A : E →L[ℝ] E)
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)) (h e : E) (t : ℝ) :
    quadraticTaylor f0 p A (h + t • e) - quadraticTaylor f0 p A h =
      t * inner ℝ (p + A h) e + t ^ 2 / 2 * inner ℝ (A e) e := by
  have hs : inner ℝ (A e) h = inner ℝ (A h) e := (hA e h).trans (real_inner_comm _ _)
  simp only [quadraticTaylor, map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hs]
  ring

lemma subgradient_directional_bound {f : E → ℝ} {f0 : ℝ} {p h zeta e : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    {r alpha w : ℝ} (hr : 0 < r) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hw : 0 ≤ w) (hh : ‖h‖ ≤ r) (he : ‖e‖ = 1)
    (hrem : ∀ z : E, ‖z‖ ≤ 2*r →
      |f z - quadraticTaylor f0 p A z| ≤ w * ‖z‖ ^ 2)
    (hsub : IsSubgradientOn f (Metric.closedBall 0 (2*r)) h zeta) :
    inner ℝ (zeta - p - A h) e ≤ ‖A‖ * alpha * r / 2 + 5*w*r/alpha := by
  have hat : 0 < alpha*r := mul_pos ha hr
  have hz : ‖h + (alpha*r) • e‖ ≤ 2*r := by
    calc
      ‖h + (alpha*r) • e‖ ≤ ‖h‖ + ‖(alpha*r) • e‖ := norm_add_le _ _
      _ = ‖h‖ + alpha*r := by rw [norm_smul_of_nonneg hat.le, he, mul_one]
      _ ≤ 2*r := by nlinarith
  have hxbound := hrem h (by linarith)
  have hzbound := hrem (h + (alpha*r) • e) hz
  have hsg := hsub (h + (alpha*r) • e) (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  have hnormsq : ‖h + (alpha*r) • e‖ ^ 2 ≤ 4*r^2 := by
    nlinarith [norm_nonneg (h + (alpha*r) • e)]
  have hhsq : ‖h‖ ^ 2 ≤ r^2 := by nlinarith [norm_nonneg h]
  have hremdiff : (f (h + (alpha*r) • e) - quadraticTaylor f0 p A (h + (alpha*r) • e)) -
      (f h - quadraticTaylor f0 p A h) ≤ 5*w*r^2 := by
    have h1 := (abs_le.mp hzbound).2
    have h2 := (abs_le.mp hxbound).1
    have h3 := mul_le_mul_of_nonneg_left hnormsq hw
    have h4 := mul_le_mul_of_nonneg_left hhsq hw
    nlinarith
  have hquad := quadraticTaylor_increment f0 p A hA h e (alpha*r)
  have hAe : inner ℝ (A e) e ≤ ‖A‖ := by
    calc
      inner ℝ (A e) e ≤ ‖inner ℝ (A e) e‖ := le_abs_self _
      _ ≤ ‖A e‖ * ‖e‖ := norm_inner_le_norm _ _
      _ ≤ ‖A‖ := by simpa only [he, mul_one] using A.le_opNorm e
  simp only [add_sub_cancel_left, real_inner_smul_right] at hsg
  have hdir : alpha*r * inner ℝ (zeta - p - A h) e ≤
      (alpha*r)^2/2 * ‖A‖ + 5*w*r^2 := by
    simp only [inner_sub_left, inner_add_left] at hquad ⊢
    have hm := mul_le_mul_of_nonneg_left hAe (by positivity : 0 ≤ (alpha*r)^2/2)
    nlinarith
  apply (mul_le_mul_iff_right₀ hat).mp
  have hcancel : (5*w*r/alpha) * (alpha*r) = 5*w*r^2 := by field_simp
  nlinarith

lemma subgradient_norm_bound {f : E → ℝ} {f0 : ℝ} {p h zeta : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    {r alpha w : ℝ} (hr : 0 < r) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hw : 0 ≤ w) (hh : ‖h‖ ≤ r)
    (hrem : ∀ z : E, ‖z‖ ≤ 2*r →
      |f z - quadraticTaylor f0 p A z| ≤ w * ‖z‖ ^ 2)
    (hsub : IsSubgradientOn f (Metric.closedBall 0 (2*r)) h zeta) :
    ‖zeta - p - A h‖ ≤ ‖A‖ * alpha * r / 2 + 5*w*r/alpha := by
  by_cases hzero : zeta - p - A h = 0
  · rw [hzero, norm_zero]
    positivity
  let v := zeta - p - A h
  let e := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hzero
  have hd := subgradient_directional_bound hA hr ha ha1 hw hh he hrem hsub
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr hzero
  have hip : inner ℝ (zeta - p - A h) e = ‖zeta - p - A h‖ := by
    change inner ℝ v (‖v‖⁻¹ • v) = ‖v‖
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  exact hip ▸ hd

lemma subgradient_zero_of_quadraticExpansion {f : E → ℝ} {p zeta : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0 < R)
    (hsub : IsSubgradientOn f (Metric.ball 0 R) 0 zeta) : zeta = p := by
  obtain ⟨delta, hdelta, hrem⟩ := hexp 1 zero_lt_one
  let eps := min R delta / 4
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hbound (r : ℝ) (hr : r ∈ Ioo 0 eps) :
      ‖zeta - p‖ ≤ ‖A‖ * 1 * r / 2 + 5*1*r/1 := by
    have hrR : 2*r < R := by
      have hh : 4*eps ≤ R := by dsimp [eps]; linarith [min_le_left R delta]
      linarith [hr.2]
    have hrdelta : 2*r < delta := by
      have hh : 4*eps ≤ delta := by dsimp [eps]; linarith [min_le_right R delta]
      linarith [hr.2]
    have hh := subgradient_norm_bound (p := p) (h := 0) hA hr.1 zero_lt_one
      le_rfl zero_le_one (by simpa using hr.1.le)
      (fun z hz => hrem z (hz.trans_lt hrdelta))
      (fun z hz => hsub z (by
        rw [Metric.mem_ball, dist_zero_right]
        exact (show ‖z‖ ≤ 2 * r from by simpa only [Metric.mem_closedBall, dist_zero_right] using hz).trans_lt hrR))
    simpa only [map_zero, sub_zero] using hh
  have hcl : (0 : ℝ) ∈ closure (Ioo 0 eps) := by
    rw [closure_Ioo heps.ne]
    exact ⟨le_rfl, heps.le⟩
  have hcont : Continuous (fun r : ℝ => ‖A‖ * 1 * r / 2 + 5*1*r/1) := by fun_prop
  have hlim := ContinuousWithinAt.closure_le hcl
    (continuousWithinAt_const (b := ‖zeta-p‖)) hcont.continuousWithinAt hbound
  have hz : ‖zeta-p‖ = 0 := le_antisymm (by simpa using hlim) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma subgradient_uniform_differential {f : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0 < R) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ h zeta : E, ‖h‖ < delta → IsSubgradientOn f (Metric.ball 0 R) h zeta →
        ‖zeta - p - A h‖ ≤ eps * ‖h‖ := by
  intro eps heps
  let alpha : ℝ := min 1 (eps / (‖A‖ + 1))
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have ha1 : alpha ≤ 1 := min_le_left _ _
  have hAa : ‖A‖ * alpha ≤ eps := by
    have hh := (le_div_iff₀ (by positivity : 0 < ‖A‖ + 1)).mp (min_le_right 1 (eps/(‖A‖+1)))
    change alpha * (‖A‖+1) ≤ eps at hh
    nlinarith
  let w : ℝ := eps * alpha / 20
  have hw : 0 < w := by dsimp [w]; positivity
  obtain ⟨d, hd, hrem⟩ := hexp w hw
  let delta := min R d / 4
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  refine ⟨delta, hdelta, ?_⟩
  intro h zeta hh hsub
  by_cases hz : h = 0
  · subst h
    have hzet := subgradient_zero_of_quadraticExpansion hA hexp hR hsub
    simp [hzet]
  have hnorm : 0 < ‖h‖ := norm_pos_iff.mpr hz
  have hhr : 2*‖h‖ < R := by
    have ht : 4*delta ≤ R := by dsimp [delta]; linarith [min_le_left R d]
    linarith
  have hhd : 2*‖h‖ < d := by
    have ht : 4*delta ≤ d := by dsimp [delta]; linarith [min_le_right R d]
    linarith
  have hb := subgradient_norm_bound hA hnorm ha ha1 hw.le le_rfl
    (fun z hz => hrem z (hz.trans_lt hhd))
    (fun z hz => hsub z (by
      rw [Metric.mem_ball, dist_zero_right]
      exact (show ‖z‖ ≤ 2 * ‖h‖ from by simpa only [Metric.mem_closedBall, dist_zero_right] using hz).trans_lt hhr))
  apply hb.trans
  have hwcalc : 5*w*‖h‖/alpha = eps*‖h‖/4 := by
    dsimp [w]
    field_simp
    ring
  rw [hwcalc]
  have hm := mul_le_mul_of_nonneg_right hAa hnorm.le
  nlinarith

def IsSemiconvexSubgradientOn (f : E → ℝ) (s : Set E) (K : ℝ)
    (h zeta : E) : Prop :=
  ∀ y ∈ s, f h + inner ℝ zeta (y - h) - K / 2 * ‖y - h‖ ^ 2 ≤ f y

lemma semiconvex_subgradient_iff {f : E → ℝ} {s : Set E} {K : ℝ} {h zeta : E} :
    IsSemiconvexSubgradientOn f s K h zeta ↔
      IsSubgradientOn (fun x => f x + K / 2 * ‖x‖ ^ 2) s h (zeta + K • h) := by
  have heq (y : E) :
      f h + K / 2 * ‖h‖ ^ 2 + inner ℝ (zeta + K • h) (y - h) -
          (f y + K / 2 * ‖y‖ ^ 2) =
      f h + inner ℝ zeta (y-h) - K/2*‖y-h‖^2 - f y := by
    simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_sub_left,
      inner_sub_right, real_inner_smul_left]
    rw [real_inner_comm y h]
    ring
  constructor <;> intro hs y hy
  · have hh := hs y hy
    linarith [heq y]
  · have hh := hs y hy
    linarith [heq y]

lemma quadraticExpansion_add_quadratic {f : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hexp : HasQuadraticExpansion f p A) (K : ℝ) :
    HasQuadraticExpansion (fun x => f x + K / 2 * ‖x‖ ^ 2) p
      (A + K • ContinuousLinearMap.id ℝ E) := by
  intro w hw
  obtain ⟨d, hd, hr⟩ := hexp w hw
  refine ⟨d, hd, fun z hz => ?_⟩
  have heq : (f z + K/2*‖z‖ ^ 2) -
      quadraticTaylor (f 0 + K/2*‖(0 : E)‖ ^ 2) p
        (A + K • ContinuousLinearMap.id ℝ E) z = f z - quadraticTaylor (f 0) p A z := by
    simp only [quadraticTaylor, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero,
      add_zero, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    ring
  rw [heq]
  exact hr z hz

lemma semiconvex_subgradient_uniform_differential {f : E → ℝ} {p : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0 < R) (K : ℝ) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ h zeta : E, ‖h‖ < delta →
        IsSemiconvexSubgradientOn f (Metric.ball 0 R) K h zeta →
        ‖zeta - p - A h‖ ≤ eps * ‖h‖ := by
  have hs : ∀ x y : E,
      inner ℝ ((A + K • ContinuousLinearMap.id ℝ E) x) y =
        inner ℝ x ((A + K • ContinuousLinearMap.id ℝ E) y) := by
    intro x y
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hA]
  intro eps heps
  obtain ⟨delta, hdelta, hb⟩ := subgradient_uniform_differential hs
    (quadraticExpansion_add_quadratic hexp K) hR eps heps
  refine ⟨delta, hdelta, ?_⟩
  intro h zeta hh hsub
  have hhbound := hb h (zeta + K • h) hh (semiconvex_subgradient_iff.mp hsub)
  have heq : zeta + K • h - p - (A + K • ContinuousLinearMap.id ℝ E) h =
      zeta - p - A h := by
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply]
    abel
  rwa [heq] at hhbound


end WeakMTWTransport
end

end OAI
