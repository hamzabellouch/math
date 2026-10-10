import OAI.Probability.SLE.Multipoint.MultipointInteraction

namespace OAI

/-! Geometric decay of the multipoint interaction follows from the
univalent disk growth inequality in Duren, *Univalent Functions* (1983),
Section 2.3. -/

noncomputable section
open Set Metric

namespace SLEExactGauge

def PublishedDiskUnivalentGrowth : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) →
    InjOn f (ball 0 1) → ∀ z ∈ ball (0 : ℂ) 1,
      ‖f z-f 0‖ ≤ ‖deriv f 0‖ * ‖z‖ / (1-‖z‖)^2

namespace Multipoint

/-- The hyperbolic interaction is bounded by the square root of the
ratio of conformal radius to point separation. -/
lemma neg_log_sq_le_radius_ratio {ρ R D : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hD : 0 < D)
    (hgrowth : D ≤ R*ρ/(1-ρ)^2) : (-Real.log ρ)^2 ≤ R/D := by
  let L := -Real.log ρ
  let E := Real.exp (L/2)
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hρ.le hρ1.le)
  have hE : 0 < E := Real.exp_pos _
  have he2 : E^2*ρ = 1 := by
    dsimp only [E]
    rw [pow_two, ← Real.exp_add, show L/2+L/2 = L by ring]
    dsimp only [L]
    rw [Real.exp_neg, Real.exp_log hρ, inv_mul_cancel₀ hρ.ne']
  have hminus : Real.exp (-(L/2)) = E*ρ := by
    have hrho : ρ = Real.exp (-L) := by simp [L, Real.exp_log hρ]
    rw [hrho]
    dsimp only [E]
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : L ≤ E-E*ρ := by
    have hh := Real.self_le_sinh_iff.mpr (show 0 ≤ L/2 by positivity)
    rw [Real.sinh_eq, hminus] at hh
    change L/2 ≤ (E-E*ρ)/2 at hh
    linarith
  have hsquare : L^2 ≤ (E-E*ρ)^2 := by nlinarith
  have hweighted := mul_le_mul_of_nonneg_right hsquare hρ.le
  have hid : (E-E*ρ)^2*ρ = (1-ρ)^2 := by
    calc
      _ = (E^2*ρ)*(1-ρ)^2 := by ring
      _ = _ := by rw [he2, one_mul]
  rw [hid] at hweighted
  have hcross := (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hρ1))).mp hgrowth
  have hratio : (1-ρ)^2/ρ ≤ R/D := by
    apply (div_le_div_iff₀ hρ hD).mpr
    nlinarith
  exact ((le_div_iff₀ hρ).mpr hweighted).trans hratio

lemma interaction_decay_of_growth {ρ b D a u : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hD : 0 < D) (hb : b ≤ D)
    (hgrowth : D ≤ (b*Real.exp (-2*a*u))*ρ/(1-ρ)^2) :
    -Real.log ρ ≤ Real.exp (-a*u) := by
  have hsq := neg_log_sq_le_radius_ratio hρ hρ1 hD hgrowth
  have hratio : (b*Real.exp (-2*a*u))/D ≤ Real.exp (-2*a*u) := by
    apply (div_le_iff₀ hD).mpr
    nlinarith [mul_le_mul_of_nonneg_right hb (Real.exp_pos (-2*a*u)).le]
  have hexp : Real.exp (-2*a*u) = (Real.exp (-a*u))^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hfinal := hsq.trans hratio
  rw [hexp] at hfinal
  exact (sq_le_sq₀ (neg_nonneg.mpr (Real.log_nonpos hρ.le hρ1.le))
    (Real.exp_pos _).le).mp hfinal

/-- A physical disk uniformization supplies the growth hypothesis used
above. No derivative of the original half-plane map is bounded. -/
theorem disk_interaction_decay (hgrowth : PublishedDiskUnivalentGrowth)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1)
    (hz0 : z ≠ 0) (b a u : ℝ) (hb : b ≤ ‖f z-f 0‖)
    (hradius : ‖deriv f 0‖ = b*Real.exp (-2*a*u)) :
    -Real.log ‖z‖ ≤ Real.exp (-a*u) := by
  have hρ : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hρ1 : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
  have hD : 0 < ‖f z-f 0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by
    intro he
    exact hz0 (hinj hz (by simp) he)))
  apply interaction_decay_of_growth hρ hρ1 hD hb
  simpa only [hradius] using hgrowth f hf hinj z hz

lemma interaction_decay_max {L a u v : ℝ}
    (hu : L ≤ Real.exp (-a*u)) (hv : L ≤ Real.exp (-a*v)) :
    L ≤ Real.exp (-a*max u v) := by
  rcases le_total u v with h | h
  · simpa only [max_eq_right h] using hv
  · simpa only [max_eq_left h] using hu

end Multipoint
end SLEExactGauge

end

end OAI
