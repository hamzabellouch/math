import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellSumsDepth
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceGoodCells
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTargetCellsGrid
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTargetsShell

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries Filter

def GoodOriginalCellProducer (c aMin c0 δ : ℝ) : Prop :=
  ∀ (d : Decomposition) (Q : ℕ) (E : Finset (PrimeUpTo Q))
    (F : HigherBiasSourceFamily d Q E δ) (a : ℝ) (n : ℤ),aMin ≤ a →
    c0 ≤ primeShellMass (boundedInterval E a (a+1)) →
    ∀ hm : 0 < primeShellMass (boundedInterval E a (a+1)),
    δ/2 ≤ ((primeShellPrior (boundedInterval E a (a+1)) hm).cmean
      (fun p => F.test p (n:ZMod p.val))).re →
    ∃ I : Finset ℤ,c*Real.exp a ≤ I.card ∧ ∀ h∈I,
      Real.exp a < (h:ℝ) ∧ (h:ℝ)+1 ≤ Real.exp (a+1) ∧
      c/Real.exp a ≤ primeShellMass (boundedRawLogCell E h) ∧
      ∃ hp : 0 < primeShellMass (boundedRawLogCell E h),
        δ/4 ≤ ((primeShellPrior (boundedRawLogCell E h) hp).cmean
          (fun p => F.test p (n:ZMod p.val))).re

theorem exists_actual_good_target_cells (c0 δ : ℝ) (hc0 : 0 < c0) (hδ : 0 < δ) :
    ∃ c aMin : ℝ,0 < c ∧ GoodOriginalCellProducer c aMin c0 δ ∧
      ∃ K : ℕ,∀ k : ℕ,K ≤ k →
      ∀ (d : Decomposition) (Q : ℕ) (E : Finset (PrimeUpTo Q))
        (F : HigherBiasSourceFamily d Q E δ) (base : Fin 3 → Finset (PrimeUpTo Q))
        (U u T logX : ℝ) (n : ℤ),aMin ≤ U → U ≤ u → u ≤ U+2*(1/10000:ℝ)*k →
        (1/10:ℝ)*(2:ℝ)^k*Real.exp u ≤ T →
        T ≤ 600*(4:ℝ)^k*Real.exp u → 999*(4:ℝ)^k*Real.exp u ≤ logX →
        (∀ v : ℝ,U ≤ v → v+(1/10000:ℝ)*k ≤ U+5*k →
          Real.exp (v+(1/10000:ℝ)*k) ≤ logX/4 → ∃ i : ℕ,v ≤ U+(i:ℝ) ∧ U+(i:ℝ)+1 ≤ v+(1/10000:ℝ)*k ∧
            c0 ≤ primeShellMass (boundedInterval E (U+i) (U+i+1))) →
        ∀ hm : ∀ j,0 < primeShellMass (testedShellFamily E base c0 U logX k j),
        (∀ j,δ/2 ≤ ((primeShellPrior (testedShellFamily E base c0 U logX k j)
          (hm j)).cmean (fun p => F.test p (n:ZMod p.val))).re) →
        ∃ a : ℝ,∃ l : List ℤ,U ≤ a ∧ Real.log T-2*(1/10000:ℝ)*k ≤ a ∧
          a+1 ≤ Real.log T-(1/10000:ℝ)*k ∧
          (∀ h∈l,Real.exp a < (h:ℝ) ∧ (h:ℝ)+1 ≤ Real.exp (a+1) ∧
            c/Real.exp a ≤ primeShellMass (boundedRawLogCell E h) ∧
            ∃ hp : 0 < primeShellMass (boundedRawLogCell E h),
              δ/4 ≤ ((primeShellPrior (boundedRawLogCell E h) hp).cmean
                (fun p => F.test p (n:ZMod p.val))).re) ∧
          |(l.sum:ℝ)-T| ≤ 6/c ∧
          Real.exp ((1/10000:ℝ)*k)/6 ≤ (l.length:ℝ) ∧
          (l.length:ℝ) ≤ 2*Real.exp (2*((1/10000:ℝ)*k)) := by
  obtain ⟨c,a0,hc,hgood⟩ := exists_many_good_original_cells c0 δ hc0 hδ
  obtain ⟨b0,hb0,Klist,hlist⟩ := exists_good_cell_target_lists_at_depth
    c (1/10000:ℝ) hc (by norm_num)
  obtain ⟨Kshell,hshell⟩ := eventually_atTop.mp
    HigherBiasSourceTargets.eventually_source_target_shell_location
  have hproducer : GoodOriginalCellProducer c (max a0 (Real.log b0)) c0 δ := by
    intro d Q E F a n ha hm hp hmean
    exact hgood d Q E F a n ((le_max_left _ _).trans ha) hm hp hmean
  refine ⟨c,max a0 (Real.log b0),hc,hproducer,max Klist Kshell,?_⟩
  intro k hk d Q E F base U u T logX n hUmin hU hu hTlo hThi hX hrich hm hmean
  have hkl : Klist ≤ k := (le_max_left _ _).trans hk
  have hks : Kshell ≤ k := (le_max_right _ _).trans hk
  have hTp : 0 < T := lt_of_lt_of_le (by positivity) hTlo
  obtain ⟨hlo,hhi,hcut⟩ := hshell k hks U u T logX hU hu hTlo hThi hX
  obtain ⟨a,hUa,hal,hah,ham,hap,haMean⟩ := exists_tested_target_shell d Q E δ c0 U T logX k
    F base n hTp hm hmean hrich hlo hhi hcut
  have ha0 : a0 ≤ a := ((le_max_left _ _).trans hUmin).trans hUa
  have hb : b0 ≤ Real.exp a := by
    have hh : Real.log b0 ≤ a := ((le_max_right _ _).trans hUmin).trans hUa
    simpa only [Real.exp_log (lt_of_lt_of_le zero_lt_one hb0)] using Real.exp_le_exp.mpr hh
  obtain ⟨I,hcard,hcells⟩ := hgood d Q E F a n ha0 ham hap haMean
  have hband : ∀ h∈I,Real.exp a ≤ (h:ℝ) ∧ (h:ℝ) ≤ Real.exp 1*Real.exp a := by
    intro h hh
    have ht := hcells h hh
    refine ⟨ht.1.le,?_⟩
    have he : Real.exp (a+1)=Real.exp 1*Real.exp a := by rw [Real.exp_add]; ring
    rw [he] at ht
    linarith [ht.2.1]
  have hbl : T*Real.exp (-(2*((1/10000:ℝ)*k))) ≤ Real.exp a := by
    have hh := Real.exp_le_exp.mpr hal
    rw [sub_eq_add_neg,Real.exp_add,Real.exp_log hTp] at hh
    simpa only [mul_assoc] using hh
  have hbu : Real.exp a ≤ T*Real.exp (-((1/10000:ℝ)*k)) := by
    have hh := Real.exp_le_exp.mpr (show a ≤ Real.log T-(1/10000:ℝ)*k by linarith)
    simpa only [sub_eq_add_neg,Real.exp_add,Real.exp_log hTp] using hh
  obtain ⟨l,hl,herr,hlenlo,hlenhi⟩ := hlist k hkl (Real.exp a) T I hb hband hcard hbl hbu
  exact ⟨a,l,hUa,hal,hah,fun h hh => hcells h (hl h hh),herr,hlenlo,hlenhi⟩

end Ostmann.Characters.HigherBiasSource

end

end OAI
