import OAI.NumberTheory.Ostmann.Supply.PrimeBandSelectionBalance

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter Ostmann.Construction
open scoped BigOperators

def supplyBandCutoff (L : ℝ) : ℕ := ⌊Real.exp (Real.exp ((9/10:ℝ)*L))⌋₊

theorem supplyBandCutoff_tendsto : Tendsto supplyBandCutoff atTop atTop := by
  have hlin : Tendsto (fun L : ℝ => (9/10:ℝ)*L) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b/(9/10:ℝ))] with L hL
    linarith
  exact (tendsto_nat_floor_atTop (α := ℝ)).comp
    (Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp hlin))

theorem unbalancedPrimePrefix_mass_small (d : Decomposition) {η : ℝ} (hη : 0<η) :
    ∀ᶠ L : ℝ in atTop,
      harmonicPrimeMass (unbalancedPrimePrefix d (supplyBandCutoff L))≤η*L := by
  obtain ⟨C,hC,hbudget⟩ := eventually_actualLogBudget_le d
  have htwo : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hsqrt := Real.tendsto_sqrt_atTop.eventually_ge_atTop (C/(η*Real.log 2))
  filter_upwards [supplyBandCutoff_tendsto.eventually hbudget,
    supplyBandCutoff_tendsto.eventually (eventually_ge_atTop (2:ℕ)),
    eventually_ge_atTop (0:ℝ),hsqrt] with L hb hQ hL hs
  have hQR : (2:ℝ)≤ supplyBandCutoff L := by exact_mod_cast hQ
  have hQ0 : (0:ℝ)<supplyBandCutoff L := by linarith
  have hlogQ : 0<Real.log (supplyBandCutoff L:ℝ) := Real.log_pos (by linarith)
  have hfloor : (supplyBandCutoff L:ℝ)≤Real.exp (Real.exp ((9/10:ℝ)*L)) :=
    Nat.floor_le (Real.exp_pos _).le
  have hl₁ := Real.log_le_log hQ0 hfloor
  rw [Real.log_exp] at hl₁
  have hl₂ := Real.log_le_log hlogQ hl₁
  rw [Real.log_exp] at hl₂
  have hloglog : Real.log (Real.log (supplyBandCutoff L:ℝ))≤L := by linarith
  have hroot : Real.sqrt (Real.log (Real.log (supplyBandCutoff L:ℝ)))≤Real.sqrt L :=
    Real.sqrt_le_sqrt hloglog
  have hscale : C≤η*Real.log 2*Real.sqrt L :=
    by simpa only [mul_comm] using (div_le_iff₀ (mul_pos hη htwo)).mp hs
  have hscale' := mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg L)
  have he : (η*Real.log 2*Real.sqrt L)*Real.sqrt L=Real.log 2*(η*L) := by
    rw [mul_assoc,Real.mul_self_sqrt hL]
    ring
  rw [he] at hscale'
  have hbudget' := hb.trans (mul_le_mul_of_nonneg_left hroot hC.le)
  have hbound := (unbalancedPrimePrefix_mass_le d (supplyBandCutoff L)).trans
    (hbudget'.trans hscale')
  nlinarith

end Ostmann.Supply

end

end OAI
