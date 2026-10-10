import Mathlib

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace HardSphere.Calibration

def scaleQ (a α n L : ℝ) : ℝ := Real.sqrt (a*n/(α*L))
def scaleK (a α n L : ℝ) : ℕ := ⌊scaleQ a α n L⌋₊

lemma scaleQ_div {a α n L : ℝ} (ha : 0<a) (hα : 0<α) (hn : 0≤n)
    (hL : 0<L) : scaleQ a α n L / L = Real.sqrt ((a/α)*(n/L^3)) := by
  have he : a*n/(α*L) = ((a/α)*(n/L^3))*L^2 := by
    field_simp
  unfold scaleQ
  rw [he, Real.sqrt_mul (by positivity), Real.sqrt_sq hL.le]
  exact mul_div_cancel_right₀ _ hL.ne'

theorem scale_limits {a α ρ : ℝ} (ha : 0<a) (hα : 0<α) (hρ : 0<ρ)
    (N : ℕ → ℕ) (L : ℕ → ℝ) (hN : ∀ k, 0<N k) (hL : ∀ k, 0<L k)
    (hLtop : Tendsto L atTop atTop)
    (hdensity : Tendsto (fun k ↦ (N k:ℝ)/L k^3) atTop (𝓝 ρ)) :
    Tendsto (fun k ↦ scaleK a α (N k) (L k)) atTop atTop ∧
    Tendsto (fun k ↦ (scaleK a α (N k) (L k):ℝ) / scaleQ a α (N k) (L k))
      atTop (𝓝 1) ∧
    Tendsto (fun k ↦ (scaleK a α (N k) (L k):ℝ) / L k)
      atTop (𝓝 (Real.sqrt ((a/α)*ρ))) := by
  have hc : 0<Real.sqrt ((a/α)*ρ) := Real.sqrt_pos.2 (by positivity)
  have hq : Tendsto (fun k ↦ scaleQ a α (N k) (L k)/L k)
      atTop (𝓝 (Real.sqrt ((a/α)*ρ))) := by
    convert (tendsto_const_nhds.mul hdensity).sqrt using 1
    ext k
    exact scaleQ_div ha hα (Nat.cast_nonneg _) (hL k)
  have hqtop : Tendsto (fun k ↦ scaleQ a α (N k) (L k)) atTop atTop := by
    simpa only [div_mul_cancel₀ _ (hL _).ne'] using hq.pos_mul_atTop hc hLtop
  have hkq := tendsto_nat_floor_div_atTop.comp hqtop
  refine ⟨tendsto_nat_floor_atTop.comp hqtop, hkq, ?_⟩
  have hqp (k) : scaleQ a α (N k) (L k) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    have hn : (0:ℝ)<N k := by exact_mod_cast hN k
    exact div_pos (mul_pos ha hn) (mul_pos hα (hL k))
  convert hkq.mul hq using 1
  · ext k
    dsimp only [Function.comp_def, scaleK]
    field_simp [hqp k]
  · simp

theorem scaled_parameters_limits {a α ρ : ℝ} (ha : 0<a) (hα : 0<α) (hρ : 0<ρ)
    (N : ℕ → ℕ) (L : ℕ → ℝ) (hN : ∀ k, 0<N k) (hL : ∀ k, 0<L k)
    (hLtop : Tendsto L atTop atTop)
    (hdensity : Tendsto (fun k ↦ (N k:ℝ)/L k^3) atTop (𝓝 ρ)) :
    Tendsto (fun k ↦ (N k:ℝ)/(scaleK a α (N k) (L k):ℝ)^3)
      atTop (𝓝 (ρ / (Real.sqrt ((a/α)*ρ))^3)) ∧
    Tendsto (fun k ↦ ((N k:ℝ)/(scaleK a α (N k) (L k):ℝ)^3) *
      (a*(scaleK a α (N k) (L k):ℝ)/L k)) atTop (𝓝 α) := by
  have hr := (scale_limits ha hα hρ N L hN hL hLtop hdensity).2.2
  have hc : Real.sqrt ((a/α)*ρ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  constructor
  · convert hdensity.div (hr.pow 3) (pow_ne_zero _ hc) using 1
    ext k
    dsimp only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply]
    by_cases hk : (scaleK a α (N k) (L k):ℝ)=0
    · simp [hk]
    · field_simp [hk, (hL k).ne']
  · have hv : a*ρ/(Real.sqrt ((a/α)*ρ))^2 = α := by
      rw [Real.sq_sqrt (by positivity)]
      field_simp
    have hh := (hdensity.const_mul a).div (hr.pow 2) (pow_ne_zero _ hc)
    rw [hv] at hh
    convert hh using 1
    ext k
    dsimp only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply]
    by_cases hk : (scaleK a α (N k) (L k):ℝ)=0
    · simp [hk]
    · field_simp [hk, (hL k).ne']

def densityLimit (a α ρ : ℝ) : ℝ := ρ/(Real.sqrt ((a/α)*ρ))^3

lemma densityLimit_pos {a α ρ : ℝ} (ha : 0<a) (hα : 0<α) (hρ : 0<ρ) :
    0<densityLimit a α ρ := by unfold densityLimit; positivity

lemma densityLimit_sq {a α ρ : ℝ} (ha : 0<a) (hα : 0<α) (hρ : 0<ρ) :
    (densityLimit a α ρ)^2 = α^3/(ρ*a^3) := by
  unfold densityLimit
  calc
    (ρ/(Real.sqrt ((a/α)*ρ))^3)^2 = ρ^2/((Real.sqrt ((a/α)*ρ))^2)^3 := by ring
    _ = α^3/(ρ*a^3) := by
      rw [Real.sq_sqrt (by positivity)]
      field_simp

lemma densityLimit_source {a α ρ : ℝ} (ha : 0<a) (hα : 0<α) (hρ : 0<ρ) :
    densityLimit a α ρ = α^(3/2:ℝ)/Real.sqrt (ρ*a^3) := by
  have hd := densityLimit_sq ha hα hρ
  have hn : (α^(3/2:ℝ))^2 = α^3 := by
    rw [Real.rpow_div_two_eq_sqrt (3:ℝ) hα.le]
    norm_cast
    calc
      ((Real.sqrt α)^3)^2 = ((Real.sqrt α)^2)^3 := by ring
      _ = α^3 := by rw [Real.sq_sqrt hα.le]
  have hr : (α^(3/2:ℝ)/Real.sqrt (ρ*a^3))^2 = α^3/(ρ*a^3) := by
    rw [div_pow, hn, Real.sq_sqrt (by positivity)]
  have hp := densityLimit_pos ha hα hρ
  have hq : 0<α^(3/2:ℝ)/Real.sqrt (ρ*a^3) := by positivity
  nlinarith

lemma densityLimit_above_threshold {a α ρ T : ℝ}
    (ha : 0<a) (hα : 0<α) (hρ : 0<ρ) (hT : 0<T)
    (hdilute : ρ*a^3 < α^3/(4*T^2)) : 2*T < densityLimit a α ρ := by
  have hn : 0<ρ*a^3 := by positivity
  have hden : 0<4*T^2 := by positivity
  have hh := (lt_div_iff₀ hden).mp hdilute
  have hs : (2*T)^2 < α^3/(ρ*a^3) := by
    apply (lt_div_iff₀ hn).2
    nlinarith
  rw [← densityLimit_sq ha hα hρ] at hs
  have hp := densityLimit_pos ha hα hρ
  nlinarith

theorem eventually_scaled_window {a α ρ T : ℝ}
    (ha : 0<a) (hα : 0<α) (hρ : 0<ρ) (hT : 0<T)
    (hdilute : ρ*a^3 < α^3/(4*T^2))
    (N : ℕ → ℕ) (L : ℕ → ℝ) (hN : ∀ k, 0<N k) (hL : ∀ k, 0<L k)
    (hLtop : Tendsto L atTop atTop)
    (hdensity : Tendsto (fun k ↦ (N k:ℝ)/L k^3) atTop (𝓝 ρ)) :
    ∀ᶠ k in atTop,
      α/2 < ((N k:ℝ)/(scaleK a α (N k) (L k):ℝ)^3) *
        (a*(scaleK a α (N k) (L k):ℝ)/L k) ∧
      ((N k:ℝ)/(scaleK a α (N k) (L k):ℝ)^3) *
        (a*(scaleK a α (N k) (L k):ℝ)/L k) < 2*α ∧
      (T+densityLimit a α ρ)/2 < (N k:ℝ)/(scaleK a α (N k) (L k):ℝ)^3 ∧
      (N k:ℝ)/(scaleK a α (N k) (L k):ℝ)^3 < 2*densityLimit a α ρ := by
  obtain ⟨hd, halpha⟩ := scaled_parameters_limits ha hα hρ N L hN hL hLtop hdensity
  have hp := densityLimit_pos ha hα hρ
  have habove := densityLimit_above_threshold ha hα hρ hT hdilute
  have hlow : (T+densityLimit a α ρ)/2 < densityLimit a α ρ := by linarith
  have hupp : densityLimit a α ρ < 2*densityLimit a α ρ := by linarith
  have hwa := halpha.eventually (Ioo_mem_nhds (show α/2<α by linarith)
    (show α<2*α by linarith))
  have hwd := hd.eventually (Ioo_mem_nhds hlow hupp)
  filter_upwards [hwa, hwd] with k ha' hd'
  exact ⟨ha'.1, ha'.2, hd'.1, hd'.2⟩

end HardSphere.Calibration

end
end

end OAI
