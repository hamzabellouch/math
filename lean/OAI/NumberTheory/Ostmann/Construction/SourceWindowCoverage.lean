import OAI.NumberTheory.Ostmann.Construction.GiantWindowScale
import OAI.NumberTheory.Ostmann.Construction.HalfListMean
import OAI.NumberTheory.Ostmann.Construction.SourcePriors

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter Ostmann.Preliminaries

lemma giantWindowScale_sqrt_lower (r G L : ℝ) (hr : 0≤r) :
    Real.exp G ≤ Real.sqrt (giantWindowScale r G L:ℝ) := by
  apply Real.le_sqrt_of_sq_le
  rw [pow_two,← Real.exp_add]
  apply le_trans _ (Nat.le_ceil (Real.exp (2*G+r*favorableBlockWidth L)))
  apply Real.exp_le_exp.mpr
  have hh : 0≤favorableBlockWidth L := (Real.exp_pos _).le
  nlinarith

lemma ceil_exp_le_exp_add_two {c : ℝ} (hc : 0≤c) :
    (⌈Real.exp (c+1)⌉₊:ℝ) ≤ Real.exp (c+2) := by
  have hceil := (Nat.ceil_lt_add_one (Real.exp_pos (c+1)).le).le
  have hlarge : 1≤Real.exp (c+1) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : (0:ℝ)≤c+1)
  have he1 : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hmul := mul_le_mul_of_nonneg_left he1 (Real.exp_pos (c+1)).le
  rw [← Real.exp_add,show c+1+1=c+2 by ring] at hmul
  linarith

lemma logCellPrimeSource_le_exp_add_two {c : ℝ} (hc : 0≤c) (E : Finset ℕ)
    (hZ : 0<logCellMass c E) (p : (logCellPrimeSource c E hZ).Sample) :
    (p:ℝ) ≤ Real.exp (c+2) := by
  have hp := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.property).1).1).2
  exact (by exact_mod_cast hp : (p:ℝ)≤(⌈Real.exp (c+1)⌉₊:ℝ)).trans (ceil_exp_le_exp_add_two hc)

theorem sourceWindowCoverage_eventually (d : Decomposition) {r : ℝ} (hr : 0≤r) :
    ∀ᶠ L : ℝ in atTop, ∀ G : ℝ, Real.exp ((1/20:ℝ)*L)≤G →
      ∀ S : PrimeSource, (∀p : S.Sample,Real.log (p:ℕ)≤G) →
        SourceWindowCoverage d S (giantWindowScale r G L) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (eventually_upperWindow_large d.cutoff)
  have hscale := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/20)).eventually_ge_atTop (M:ℝ)
  filter_upwards [hscale] with L hL
  intro G hG S hS p
  have hG0 : 0≤G := (Real.exp_pos _).le.trans hG
  have hX : M≤giantWindowScale r G L := by
    exact_mod_cast (hL.trans hG).trans (giantWindowScale_ge r G L hr hG0)
  have hp0 : (0:ℝ)<(p:ℕ) := by exact_mod_cast (S.prime _ p.property).pos
  have hp := Real.exp_le_exp.mpr (hS p)
  rw [Real.exp_log hp0] at hp
  have hp' := hp.trans (giantWindowScale_sqrt_lower r G L hr)
  change ((p:ℕ)+d.cutoff:ℝ)<(giantWindowScale r G L:ℝ)^(9/10:ℝ)
  linarith [hM _ hX]

theorem logCell_sourceWindowCoverage_eventually (d : Decomposition) {r : ℝ} (hr : 0≤r)
    (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ G : ℝ, Real.exp ((1/20:ℝ)*L)≤G →
      ∀ c : ℝ, 0≤c → c≤C*favorableBlockWidth L →
      ∀ E : Finset ℕ, ∀ hZ : 0<logCellMass c E,
        SourceWindowCoverage d (logCellPrimeSource c E hZ) (giantWindowScale r G L) := by
  have hratio := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/25)).eventually_ge_atTop (C+2)
  have hwidth := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/100)).eventually_ge_atTop 1
  filter_upwards [sourceWindowCoverage_eventually d hr,hratio,hwidth] with L hcover hrange hw
  intro G hG c hc hcmax E hZ
  apply hcover G hG
  intro p
  have hh : 0<favorableBlockWidth L := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hrange hh.le
  have he : favorableBlockWidth L*Real.exp ((1/25:ℝ)*L)=Real.exp ((1/20:ℝ)*L) := by
    unfold favorableBlockWidth
    rw [← Real.exp_add]; congr 1; ring
  rw [he] at hmul
  change 1≤favorableBlockWidth L at hw
  have hcenter : c+2≤G := by nlinarith
  have hp := logCellPrimeSource_le_exp_add_two hc E hZ p
  have hp0 : (0:ℝ)<(p:ℕ) := by exact_mod_cast ((logCellPrimeSource c E hZ).prime _ p.property).pos
  have hlog := Real.log_le_log hp0 hp
  rw [Real.log_exp] at hlog
  exact hlog.trans hcenter

end Ostmann.Construction

end

end OAI
