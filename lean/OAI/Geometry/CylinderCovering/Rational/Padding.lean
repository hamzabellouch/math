import Mathlib

namespace OAI

open Asymptotics Filter
open scoped Topology

namespace CylinderCovering.RationalPadding

theorem rpow_littleO_at_zero {p q : ℝ} (hpq : p < q) :
    (fun x : ℝ => x ^ q) =o[𝓝[>] 0] (fun x => x ^ p) := by
  apply (isLittleO_iff_tendsto' ?_).2
  · have hlim : Tendsto (fun x : ℝ => x ^ (q - p)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (q - p))) :=
      (Real.continuous_rpow_const (sub_nonneg.mpr hpq.le)).continuousAt.tendsto
    have hzero : (0 : ℝ) ^ (q - p) = 0 := Real.zero_rpow (sub_pos.mpr hpq).ne'
    rw [hzero] at hlim
    apply (hlim.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Real.rpow_sub hx q p
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact fun h => False.elim ((Real.rpow_pos_of_pos hx p).ne' h)

theorem vanishing_padding_rates :
    (fun x : ℝ => x ^ (5 / 2 : ℝ)) =o[𝓝[>] 0] (fun x => x ^ (2 : ℕ)) ∧
    (fun x : ℝ => x ^ (3 : ℕ)) =o[𝓝[>] 0] (fun x => x ^ (5 / 2 : ℝ)) := by
  constructor
  · simpa only [Real.rpow_two] using rpow_littleO_at_zero (p := 2) (q := 5 / 2) (by norm_num)
  · simpa only [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast] using
      rpow_littleO_at_zero (p := 5 / 2) (q := 3) (by norm_num)

theorem eventually_cost_lt_of_littleO {C : ℝ → ℝ} {A Δ : ℝ} (hΔ : 0 < Δ)
    (hrem : (fun x => C x - (A - Δ * x ^ 2)) =o[𝓝[>] 0] (fun x => x ^ (2 : ℕ))) :
    ∀ᶠ x : ℝ in 𝓝[>] 0, C x < A := by
  filter_upwards [self_mem_nhdsWithin, hrem.bound (show 0 < Δ / 2 by positivity)] with x hx hr
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)] at hr
  have hb := (abs_le.mp hr).2
  have hp : 0 < Δ * x ^ 2 := mul_pos hΔ (sq_pos_of_pos hx)
  nlinarith

theorem eventually_cost_lt_of_fourth_order {C : ℝ → ℝ} {A Δ : ℝ} (hΔ : 0 < Δ)
    (hrem : (fun x => C x - (A - Δ * x ^ 2)) =O[𝓝[>] 0] (fun x => x ^ (4 : ℕ))) :
    ∀ᶠ x : ℝ in 𝓝[>] 0, C x < A := by
  apply eventually_cost_lt_of_littleO hΔ
  exact hrem.trans_isLittleO ((isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 4 by norm_num)).mono nhdsWithin_le_nhds)

theorem eventually_cost_lt_vanishing_padding {C q : ℝ → ℝ} {A Δ : ℝ}
    (hΔ : 0 < Δ) (hq : q =o[𝓝[>] 0] (fun x => x ^ (2 : ℕ)))
    (hrem : (fun x => C x - (A - Δ * x ^ 2 + q x / 2)) =O[𝓝[>] 0]
      (fun x => x ^ (4 : ℕ))) :
    ∀ᶠ x : ℝ in 𝓝[>] 0, C x < A := by
  apply eventually_cost_lt_of_littleO hΔ
  have hr := hrem.trans_isLittleO
    ((isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 4 by norm_num)).mono nhdsWithin_le_nhds)
  have hsum := hr.add (hq.const_mul_left (1 / 2 : ℝ))
  have heq : (fun x => C x - (A - Δ * x ^ 2 + q x / 2) + (1 / 2 : ℝ) * q x) =
      (fun x => C x - (A - Δ * x ^ 2)) := by funext x; ring
  rw [heq] at hsum
  exact hsum

theorem quadratic_padding_rates {η : ℝ} (hη : 0 < η) :
    (fun x : ℝ => η * x ^ (2 : ℕ)) =O[𝓝[>] 0] (fun x => x ^ (2 : ℕ)) ∧
    (fun x : ℝ => x ^ (3 : ℕ)) =o[𝓝[>] 0] (fun x => η * x ^ (2 : ℕ)) := by
  refine ⟨(isBigO_refl (fun x : ℝ => x ^ (2 : ℕ)) _).const_mul_left η, ?_⟩
  exact Asymptotics.IsLittleO.const_mul_right hη.ne'
    ((isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 3 by norm_num)).mono nhdsWithin_le_nhds)

theorem eventually_cost_lt_quadratic_padding {C : ℝ → ℝ} {A Δ η : ℝ}
    (hgap : η / 2 < Δ)
    (hrem : (fun x => C x - (A - Δ * x ^ 2 + η * x ^ 2 / 2)) =O[𝓝[>] 0]
      (fun x => x ^ (4 : ℕ))) :
    ∀ᶠ x : ℝ in 𝓝[>] 0, C x < A := by
  apply eventually_cost_lt_of_fourth_order (sub_pos.mpr hgap)
  exact hrem.congr_left (fun x => by ring)

theorem eventually_cost_lt_five_halves {C : ℝ → ℝ} {A Δ : ℝ}
    (hgap : 0 < Δ)
    (hrem : (fun x => C x - (A - Δ * x ^ 2 + x ^ (5 / 2 : ℝ) / 2)) =O[𝓝[>] 0]
      (fun x => x ^ (4 : ℕ))) :
    ∀ᶠ x : ℝ in 𝓝[>] 0, C x < A :=
  eventually_cost_lt_vanishing_padding hgap vanishing_padding_rates.1 hrem

theorem exists_eventual_quadratic_control {q : ℝ → ℝ}
    (hq0 : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 ≤ q x)
    (hq : q =O[𝓝[>] 0] (fun x => x ^ (2 : ℕ))) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ᶠ x : ℝ in 𝓝[>] 0,
      0 ≤ q x ∧ q x ≤ Q * x ^ 2 ∧ x ^ 2 ≤ 1 ∧ x ^ 2 + q x ≤ 1 / 4 := by
  obtain ⟨Q, hQ, hb⟩ := hq.exists_pos
  refine ⟨Q, hQ, ?_⟩
  have ht : Tendsto (fun x : ℝ => x ^ (2 : ℕ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((continuous_pow 2).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hδ : Tendsto (fun x : ℝ => (1 + Q) * x ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using ht.const_mul (1 + Q)
  filter_upwards [hq0, hb.bound, ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hδ.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))] with x hx0 hxb hx1 hxδ
  simp only [Real.norm_eq_abs, abs_of_nonneg hx0, abs_of_nonneg (sq_nonneg x)] at hxb
  exact ⟨hx0, hxb, hx1.le, by nlinarith⟩

end CylinderCovering.RationalPadding

end OAI
