import OAI.NumberTheory.Ostmann.Construction.BinExponential
import OAI.NumberTheory.Ostmann.Construction.PrimeGroupBins

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter

theorem bin_center_small_eventually (k : ℕ) {β ε : ℝ}
    (hβ : β<(1/100:ℝ)) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, b ≤ Conclusion.bulkSize k L →
      ∀ t : ℝ, -2<t → t<(b:ℝ)*Real.exp (β*L)+2 →
        |t| ≤ ε*favorableBlockWidth L := by
  have hrate : ∀ᶠ L : ℝ in atTop,
      2*Conclusion.bulkScale k/ε ≤ Real.exp (((1/100:ℝ)-β)*L)/L := by
    simpa only [Real.rpow_one] using
      (tendsto_exp_mul_div_rpow_atTop 1 ((1/100:ℝ)-β) (by linarith)).eventually_ge_atTop
        (2*Conclusion.bulkScale k/ε)
  have hh := ((exp_mul_tendsto (by norm_num : (0:ℝ)<1/100)).const_mul_atTop hε).eventually_ge_atTop 4
  filter_upwards [hrate,hh,eventually_ge_atTop (1:ℝ)] with L hr hh hL
  intro b hb t htlo hthi
  have hL0 : 0<L := by linarith
  have hm := (Conclusion.bulkSize_bounds k hL0.le).2
  have hb' : (b:ℝ) ≤ Conclusion.bulkSize k L := by exact_mod_cast hb
  have hr' := (le_div_iff₀ hL0).mp hr
  have hr'' := mul_le_mul_of_nonneg_right hr' (Real.exp_pos (β*L)).le
  rw [← Real.exp_add,show ((1/100:ℝ)-β)*L+β*L=(1/100:ℝ)*L by ring] at hr''
  have hm' := mul_le_mul_of_nonneg_right (hb'.trans hm) (Real.exp_pos (β*L)).le
  have hc : 2*((b:ℝ)*Real.exp (β*L)) ≤ ε*favorableBlockWidth L := by
    have hx := mul_le_mul_of_nonneg_left hr'' hε.le
    have he : ε*(2*Conclusion.bulkScale k/ε*L*Real.exp (β*L))=
        2*(Conclusion.bulkScale k*L*Real.exp (β*L)) := by field_simp
    rw [he] at hx
    change _ ≤ ε*favorableBlockWidth L at hx
    linarith
  change 4 ≤ ε*favorableBlockWidth L at hh
  apply abs_le.mpr
  constructor <;> linarith

theorem exists_primeGroup_bin_eventually (d : Decomposition) {k : ℕ} (hk : 0<k)
    {α β ε : ℝ} (hαβ : α≤β) (hβ : β<(1/100:ℝ)) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, b ≤ Conclusion.bulkSize k L →
      ∀ S : PrimeSource,
        (∀ p : S.Sample, Real.exp (α*L) ≤ Real.log (p:ℕ) ∧
          Real.log (p:ℕ) ≤ Real.exp (β*L)) →
        (1/2:ℝ) ≤ S.law.mean (fun p => balancedPrimeIndicator d p) →
        ∃ t : ℤ, |(t:ℝ)| ≤ ε*favorableBlockWidth L ∧
          Real.exp (-3*(Conclusion.bulkSize k L:ℝ)) < primeGroupBinMass d S b t := by
  filter_upwards [bin_weight_lower_eventually hk hαβ (by linarith : β<1),
    bin_center_small_eventually k hβ hε,eventually_ge_atTop (0:ℝ)] with L hw hc hL
  intro b hb S hS hbal
  obtain ⟨t,htlo,hthi,htmass⟩ := exists_primeGroup_bin d S b
    (Real.exp (α*L)) (Real.exp (β*L))
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hαβ hL)) hS hbal
  refine ⟨t,hc b hb t ?_ hthi,(hw b hb).trans_lt htmass⟩
  have : 0 ≤ (b:ℝ)*Real.exp (α*L) := by positivity
  linarith

theorem exists_bulk_prior_bin (d : Decomposition) {k : ℕ} (hk : 0<k)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ E : Finset ℕ, E.card≤2 →
      ∃ hZ : 0<harmonicPrimeMass (logLogPrimeBand ((1/250:ℝ)*L) ((3/500:ℝ)*L) \ E),
      ∃ t : ℤ, |(t:ℝ)| ≤ ε*favorableBlockWidth L ∧
        Real.exp (-3*(Conclusion.bulkSize k L:ℝ)) <
          primeGroupBinMass d (harmonicPrimeSource
            (logLogPrimeBand ((1/250:ℝ)*L) ((3/500:ℝ)*L) \ E)
            (fun _p hp => logLogPrimeBand_prime (Finset.mem_sdiff.mp hp).1) hZ)
            (Conclusion.bulkSize k L/2) t := by
  filter_upwards [broadBand_balanced_prior_eventually d
      (by norm_num : (0:ℝ)≤1/250) (by norm_num : (1/250:ℝ)<3/500)
      (by norm_num : (3/500:ℝ)≤9/10),
    exists_primeGroup_bin_eventually d hk (by norm_num : (1/250:ℝ)≤3/500)
      (by norm_num : (3/500:ℝ)<1/100) hε] with L hbulk hbin
  intro E hE
  obtain ⟨hZ,hbal⟩ := hbulk E hE
  refine ⟨hZ,?_⟩
  exact hbin _ (Nat.div_le_self _ _) _ (harmonicBand_log_support hZ) hbal

end Ostmann.Construction

end

end OAI
