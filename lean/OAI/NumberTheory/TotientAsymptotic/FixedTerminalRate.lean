import OAI.NumberTheory.TotientAsymptotic.UnbandedCubeCost
import OAI.NumberTheory.TotientAsymptotic.TailBounds

namespace OAI

/-! A positive uniform terminal-cap rate a fixed distance from the natural dimension. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem fixed_terminal_rate (H : ℕ) {E : ℝ} (hE : 0 < E) :
    ∃ c : ℝ,0 < c ∧ ∀ᶠ x : ℝ in atTop,∀ N : ℕ,N+H=m x → ∀ κ : ℝ,0 < κ → κ ≤ E →
      c ≤ (N:ℝ)*g N/(κ*(B x+prefixCubeCost N)) := by
  obtain ⟨A,hA,hcost⟩ := prefixCubeCost_relative_bound
  let L : ℝ := (gamma*rho^H)*rho/(2*lam)
  have hL : 0 < L := div_pos (mul_pos (mul_pos gamma_pos (pow_pos rho_pos H)) rho_pos) (by have := lam_pos; positivity)
  refine ⟨L/(E*(1+A)),by positivity,?_⟩
  have hp := normalized_prefactor_step fordRenewalInput H
  filter_upwards [hcost,hp.eventually (eventually_gt_nhds
    (show (gamma*rho^H)/2 < gamma*rho^H by have := mul_pos gamma_pos (pow_pos rho_pos H); linarith)),theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ)),
    m_tendsto.eventually (eventually_ge_atTop (H+1))] with x hcost hp hphase hB hm
  intro N hN
  have hNsub : m x-H=N := by omega
  rw [hNsub] at hp
  have hm' : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hc0 : 0 ≤ prefixCubeCost N/B x := div_nonneg (prefixCubeCost_nonneg _) hB.le
  have hc : prefixCubeCost N/B x ≤ A := by
    have hh := (hcost N (by omega)).trans
      (mul_le_of_le_one_right hA.le (pow_le_one₀ rho_pos.le rho_lt_one.le))
    have he : (N:ℝ)*prefixCubeCost N/B x=
        (N:ℝ)*(prefixCubeCost N/B x) := by ring
    rw [he] at hh
    nlinarith only [hm',hc0,hh]
  have hbudget : B x+prefixCubeCost N ≤ (1+A)*B x := by
    have hh := (div_le_iff₀ hB).mp hc
    nlinarith only [hh]
  have hratio0 : 0 ≤ (N:ℝ)*g N/B x :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (g_pos _).le) hB.le
  have halpha := mul_le_mul_of_nonneg_right (alpha_le _ hphase) hratio0
  have hratio : L ≤ (N:ℝ)*g N/B x := by
    have hh : (gamma*rho^H)/2 ≤ (lam/rho)*((N:ℝ)*g N/B x) := hp.le.trans halpha
    have hh' : ((gamma*rho^H)/2)/(lam/rho) ≤ (N:ℝ)*g N/B x :=
      (div_le_iff₀ (div_pos lam_pos rho_pos)).mpr (by simpa only [mul_comm] using hh)
    convert hh' using 1
    dsimp [L]
    field_simp
  have hnumerator := (le_div_iff₀ hB).mp hratio
  intro κ hκ hκE
  apply (le_div_iff₀ (mul_pos hκ (add_pos_of_pos_of_nonneg hB (prefixCubeCost_nonneg _)))).mpr
  have hden : κ*(B x+prefixCubeCost N) ≤ E*((1+A)*B x) :=
    mul_le_mul hκE hbudget (add_nonneg hB.le (prefixCubeCost_nonneg _)) hE.le
  have hh := mul_le_mul_of_nonneg_left hden (show 0 ≤ L/(E*(1+A)) by positivity)
  have hid : (L/(E*(1+A)))*(E*((1+A)*B x))=L*B x := by field_simp
  rw [hid] at hh
  exact hh.trans hnumerator

end TotientAsymptotic

end

end OAI
