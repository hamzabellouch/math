import OAI.MathematicalPhysics.Boltzmann.Branching.GrowthContradiction
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Geometric mass growth using only almost-everywhere time traces -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.GrowthContradiction

theorem next_good_growth_time {G : Set ℝ} (hG : ∀ᵐ t ∂volume, t ∈ G)
    {m : ℝ → ℝ} {r₀ r₁ t : ℝ} (hr₀ : 0 < r₀) (hrr : r₀ < r₁) (ht : 0 < t)
    (hstep : ∀ᵐ u ∂volume, u ∈ Ioo (r₀*t) (r₁*t) → 3*m t ≤ m u) :
    ∃ u, u ∈ G ∧ 0 < u ∧ u < r₁*t ∧ 3*m t ≤ m u := by
  have hi : r₀*t < r₁*t := mul_lt_mul_of_pos_right hrr ht
  have hpos : (volume : Measure ℝ) (Ioo (r₀*t) (r₁*t)) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hi))
  have hae : ∀ᵐ u ∂volume.restrict (Ioo (r₀*t) (r₁*t)), u ∈ G ∧ 3*m t ≤ m u := by
    filter_upwards [ae_restrict_of_ae hG,ae_restrict_of_ae hstep,
      ae_restrict_mem measurableSet_Ioo] with u hu hs hiu
    exact ⟨hu,hs hiu⟩
  obtain ⟨u,hu,hgu,hmu⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos hae
  exact ⟨u,hgu,(mul_pos hr₀ ht).trans hu.1,hu.2,hmu⟩

theorem no_ae_growth_with_fourth_power_cap {G : Set ℝ}
    (hG : ∀ᵐ t ∂volume, t ∈ G) {m : ℝ → ℝ} {r₀ r₁ C t₀ : ℝ}
    (hr₀ : 0 < r₀) (hrr : r₀ < r₁) (hr₁ : 1 < r₁) (hgrowth : r₁^4 < 3)
    (hC : 0 ≤ C) (ht₀ : 0 < t₀) (htG : t₀ ∈ G) (hm₀ : 0 < m t₀)
    (hcap : ∀ t ∈ G, 0 < t → m t ≤ C*(1+t)^4)
    (hstep : ∀ t ∈ G, 0 < t → ∀ᵐ u ∂volume,
      u ∈ Ioo (r₀*t) (r₁*t) → 3*m t ≤ m u) : False := by
  have hex (n : ℕ) : ∃ t, t ∈ G ∧ 0 < t ∧ t ≤ r₁^n*t₀ ∧ 3^n*m t₀ ≤ m t := by
    induction n with
    | zero => exact ⟨t₀,htG,ht₀,by simp,by simp⟩
    | succ n ih =>
      obtain ⟨t,htG,ht,htbound,hm⟩ := ih
      obtain ⟨u,huG,hu,hub,hmu⟩ := next_good_growth_time hG hr₀ hrr ht (hstep t htG ht)
      refine ⟨u,huG,hu,?_,?_⟩
      · calc
          u ≤ r₁*t := hub.le
          _ ≤ r₁*(r₁^n*t₀) := mul_le_mul_of_nonneg_left htbound (zero_le_one.trans hr₁.le)
          _ = r₁^(n+1)*t₀ := by rw [pow_succ']; ring
      · calc
          3^(n+1)*m t₀ = 3*(3^n*m t₀) := by rw [pow_succ']; ring
          _ ≤ 3*m t := mul_le_mul_of_nonneg_left hm (by norm_num)
          _ ≤ m u := hmu
  apply no_uniform_branching_cap (a := r₁-1) (t₀ := t₀) (m₀ := m t₀) (C := C)
    (by linarith) ht₀ hm₀ hC (by simpa only [show 1+(r₁-1)=r₁ by ring] using hgrowth)
  intro n
  obtain ⟨t,htG,ht,htb,hm⟩ := hex n
  have hp : (1+t)^4 ≤ (1+r₁^n*t₀)^4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  simpa only [show 1+(r₁-1)=r₁ by ring] using
    hm.trans ((hcap t htG ht).trans (mul_le_mul_of_nonneg_left hp hC))

end BoltzmannNonuniqueness.GrowthContradiction

end

end OAI
