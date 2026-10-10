import OAI.Geometry.IsometricImmersion.Pulses.PulseOperatorMoment

namespace OAI

noncomputable section
open Set
namespace SmoothLocal.Pulse

theorem pulse_moment_bounds_incompatible {m c3 delta tau E C0 C1 : ℝ} (N : ℕ)
    (hc3 : 0 < c3) (hd : 0 < delta) (ht : 0 < tau)
    (hsmall : C0*delta ≤ c3/4)
    (hedge : E ≤ (c3/4)*delta*tau)
    (hlower : C1*delta ≤ (c3/4)*tau)
    (hpositive : c3*delta*tau/tau^N ≤ |m|)
    (hcost : |m| ≤ E/tau^N+C0*delta^2*tau/tau^N+C1*delta^2/tau^N) : False := by
  have hquot : c3*delta*tau/tau^N ≤ (E+C0*delta^2*tau+C1*delta^2)/tau^N := by
    calc
      _ ≤ |m| := hpositive
      _ ≤ _ := hcost
      _ = _ := by ring
  have hnum : c3*delta*tau ≤ E+C0*delta^2*tau+C1*delta^2 :=
    (div_le_div_iff_of_pos_right (pow_pos ht N)).mp hquot
  have hscaled := mul_le_mul_of_nonneg_right hsmall (mul_pos hd ht).le
  have hlowscaled := mul_le_mul_of_nonneg_right hlower hd.le
  have hlead : 0 < c3*delta*tau := mul_pos (mul_pos hc3 hd) ht
  nlinarith

theorem exists_delta_then_frequency_for_moment_contradiction {c3 C0 : ℝ}
    (hc3 : 0 < c3) (hC0 : 0 ≤ C0) (N : ℕ) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1/2 ∧
      ∀ E C1 : ℝ, ∃ T : ℝ, 1 ≤ T ∧ ∀ tau : ℝ, T ≤ tau → ∀ m : ℝ,
        c3*delta*tau/tau^N ≤ |m| →
        |m| ≤ E/tau^N+C0*delta^2*tau/tau^N+C1*delta^2/tau^N → False := by
  let delta := min (1/4) (c3/(8*(C0+1)))
  have hden : 0 < 8*(C0+1) := by positivity
  have hd : 0 < delta := lt_min (by norm_num) (div_pos hc3 hden)
  have hd1 : delta ≤ 1/4 := min_le_left _ _
  have hd2 : delta ≤ c3/(8*(C0+1)) := min_le_right _ _
  have hsmall : C0*delta ≤ c3/4 := by
    have hh := (le_div_iff₀ hden).mp hd2
    nlinarith
  refine ⟨delta,hd,by linarith,?_⟩
  intro E C1
  let T := max 1 (max (4*E/(c3*delta)) (4*C1*delta/c3))
  refine ⟨T,le_max_left _ _,?_⟩
  intro tau ht m hpositive hcost
  have ht1 : 1 ≤ tau := (le_max_left _ _).trans ht
  have htpos : 0 < tau := zero_lt_one.trans_le ht1
  have heT : 4*E/(c3*delta) ≤ tau := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hlT : 4*C1*delta/c3 ≤ tau := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hedge : E ≤ (c3/4)*delta*tau := by
    have hh := (div_le_iff₀ (mul_pos hc3 hd)).mp heT
    nlinarith
  have hlower : C1*delta ≤ (c3/4)*tau := by
    have hh := (div_le_iff₀ hc3).mp hlT
    nlinarith
  exact pulse_moment_bounds_incompatible N hc3 hd htpos hsmall hedge hlower hpositive hcost

end SmoothLocal.Pulse

end

end OAI
