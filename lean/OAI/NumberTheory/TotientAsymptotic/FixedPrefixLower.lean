import OAI.NumberTheory.TotientAsymptotic.FixedTerminalLower

namespace OAI

/-! Positive comparison of a fixed prefix dimension with the natural scale. -/
noncomputable section
open scoped Topology
open Filter MeasureTheory
namespace TotientAsymptotic

theorem fixed_prefix_volume_lower (H : ℕ) : ∃ c : ℝ,0 < c ∧
    ∀ᶠ x : ℝ in atTop, c*G x (m x) ≤ G x (m x-H) := by
  let a := rho^(H*(H-1)/2)*gamma^H
  let b := (lam/rho)^H
  have ha : 0 < a := mul_pos (pow_pos rho_pos _) (pow_pos gamma_pos _)
  have hb : 0 < b := by dsimp [b]; exact pow_pos (div_pos lam_pos rho_pos) H
  refine ⟨a/(2*b),by positivity,?_⟩
  have hp := normalized_prefactor_limit fordRenewalInput H
  filter_upwards [hp.eventually (eventually_gt_nhds (show a/2 < a by linarith)),
    theta_eventually_mem,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hphase hB
  have hg := G_pos hB (m x)
  have hratio : 0 ≤ G x (m x-H)/G x (m x) := div_nonneg (G_pos hB _).le hg.le
  have halpha : alpha (theta x)^H ≤ b :=
    pow_le_pow_left₀ (alpha_pos _).le (alpha_le _ hphase) H
  have hlo : a/2 ≤ b*(G x (m x-H)/G x (m x)) := by
    have hh := mul_le_mul_of_nonneg_right halpha hratio
    have hx' : a/2 ≤ alpha (theta x)^H*(G x (m x-H)/G x (m x)) := by
      simpa only [R,mul_div_assoc] using hx.le
    exact hx'.trans hh
  have hdiv : a/(2*b) ≤ G x (m x-H)/G x (m x) := by
    have hh : (a/2)/b ≤ G x (m x-H)/G x (m x) :=
      (div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hlo)
    simpa only [div_div] using hh
  exact (le_div_iff₀ hg).mp hdiv

theorem fixed_terminal_natural_volume_lower (t : ℝ) (ht : 0 ≤ t) :
    ∀ᶠ H : ℕ in atTop, ∃ c : ℝ,0 < c ∧ ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ,N+1+H=m x →
      c*G x (m x) ≤ volume.real
        (prefixRegion (N+1) (B x) 0 0 ∩ {u | t ≤ u (Fin.last N)}) := by
  filter_upwards [fixed_terminal_volume_lower t ht] with H hH
  obtain ⟨c,hc,hprefix⟩ := fixed_prefix_volume_lower H
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [hH,hprefix] with x hx hp
  intro N hN
  have he : m x-H=N+1 := by omega
  rw [he] at hp
  have hh := hx N hN
  calc
    _ = (c*G x (m x))/2 := by ring
    _ ≤ G x (N+1)/2 := div_le_div_of_nonneg_right hp (by norm_num)
    _ ≤ _ := hh

end TotientAsymptotic

end

end OAI
