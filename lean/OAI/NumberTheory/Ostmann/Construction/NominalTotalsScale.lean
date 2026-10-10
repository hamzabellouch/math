import OAI.NumberTheory.Ostmann.Construction.BinScale
import OAI.NumberTheory.Ostmann.Construction.NominalTotalsBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped Topology

theorem nominalTotals_eventually (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ G₀ c tb td : ℝ, 0≤G₀ →
      (G₀-2≤c ∧ c≤G₀+favorableBlockWidth L+2) →
      |tb|≤favorableBlockWidth L/16 → |td|≤favorableBlockWidth L/16 →
      (favorableBlockWidth L/2≤nominalJ Bs BD Bz k L G₀ c td ∧
        nominalJ Bs BD Bz k L G₀ c td≤3*favorableBlockWidth L) ∧
      (favorableBlockWidth L/4≤nominalJ Bs BD Bz k L G₀ c td-2*tb ∧
        nominalJ Bs BD Bz k L G₀ c td-2*tb≤4*favorableBlockWidth L) ∧
      ∀j<k, favorableBlockWidth L/4≤nominalCompensation Bs BD Bz k L G₀ c td j ∧
        nominalCompensation Bs BD Bz k L G₀ c td j≤4*(2:ℝ)^k*favorableBlockWidth L := by
  have hgap := nominalGapMagnitude_eventually Bs BD Bz k (by norm_num : (0:ℝ)<1/16)
  have hh := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/100)).eventually_ge_atTop 8
  filter_upwards [hgap,hh] with L hg hh
  intro G₀ c tb td hG hc htb htd
  apply nominalTotals_bounds_of_small_errors Bs BD Bz hk hG hh hc htb htd
  simpa only [one_div,mul_comm (16:ℝ)⁻¹,← div_eq_mul_inv] using hg

theorem nominalCompensation_relative_eventually (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ G₀ c td : ℝ, 0≤G₀ →
      (G₀-2≤c ∧ c≤G₀+favorableBlockWidth L+2) → |td|≤favorableBlockWidth L/16 →
      ∀j<k, |nominalCompensation Bs BD Bz k L G₀ c td j-
        (2:ℝ)^(k-1-j)*nominalJ Bs BD Bz k L G₀ c td|≤ε*nominalJ Bs BD Bz k L G₀ c td := by
  filter_upwards [nominalTotals_eventually Bs BD Bz hk,
    nominalCompensation_error_eventually Bs BD Bz k (half_pos hε)] with L hL he
  intro G₀ c td hG hc htd j hj
  have hJ := (hL G₀ c 0 td hG hc (by simp only [abs_zero]; unfold favorableBlockWidth; positivity) htd).1.1
  exact (he G₀ c td j hj).trans (by nlinarith)

theorem nominalTotals_from_bins_eventually (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ G₀ c tb td : ℝ, 0≤G₀ →
      (G₀-2≤c ∧ c≤G₀+favorableBlockWidth L+2) →
      (∀t:ℝ, (t=tb ∨ t=td) → -2<t ∧
        t<(Conclusion.bulkSize k L:ℝ)*Real.exp ((3/500:ℝ)*L)+2) →
      (favorableBlockWidth L/2≤nominalJ Bs BD Bz k L G₀ c td ∧
        nominalJ Bs BD Bz k L G₀ c td≤3*favorableBlockWidth L) ∧
      (favorableBlockWidth L/4≤nominalJ Bs BD Bz k L G₀ c td-2*tb ∧
        nominalJ Bs BD Bz k L G₀ c td-2*tb≤4*favorableBlockWidth L) ∧
      ∀j<k, favorableBlockWidth L/4≤nominalCompensation Bs BD Bz k L G₀ c td j ∧
        nominalCompensation Bs BD Bz k L G₀ c td j≤4*(2:ℝ)^k*favorableBlockWidth L := by
  classical
  filter_upwards [nominalTotals_eventually Bs BD Bz hk,
    bin_center_small_eventually k (by norm_num : (3/500:ℝ)<1/100)
      (by norm_num : (0:ℝ)<1/16)] with L hL hbin
  intro G₀ c tb td hG hc hb
  apply hL G₀ c tb td hG hc
  · have h := hb tb (Or.inl rfl)
    simpa only [one_div,mul_comm (16:ℝ)⁻¹,← div_eq_mul_inv] using
      hbin (Conclusion.bulkSize k L) (le_refl _) tb h.1 h.2
  · have h := hb td (Or.inr rfl)
    simpa only [one_div,mul_comm (16:ℝ)⁻¹,← div_eq_mul_inv] using
      hbin (Conclusion.bulkSize k L) (le_refl _) td h.1 h.2

end Ostmann.Construction

end

end OAI
