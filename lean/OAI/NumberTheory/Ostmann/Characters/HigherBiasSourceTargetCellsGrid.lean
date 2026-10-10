import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFamily
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTestShells

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries

theorem exists_tested_target_shell (d : Decomposition) (Q : ℕ)
    (E : Finset (PrimeUpTo Q)) (δ c0 U T logX : ℝ) (k : ℕ)
    (F : HigherBiasSourceFamily d Q E δ) (base : Fin 3 → Finset (PrimeUpTo Q))
    (n : ℤ) (hT : 0 < T)
    (hm : ∀ j,0 < primeShellMass (testedShellFamily E base c0 U logX k j))
    (hmean : ∀ j,δ/2 ≤ ((primeShellPrior (testedShellFamily E base c0 U logX k j)
      (hm j)).cmean (fun p => F.test p (n:ZMod p.val))).re)
    (hrich : ∀ v : ℝ,U ≤ v → v+(1/10000:ℝ)*k ≤ U+5*k →
      Real.exp (v+(1/10000:ℝ)*k) ≤ logX/4 → ∃ i : ℕ,v ≤ U+(i:ℝ) ∧ U+(i:ℝ)+1 ≤ v+(1/10000:ℝ)*k ∧
        c0 ≤ primeShellMass (boundedInterval E (U+i) (U+i+1)))
    (hlo : U ≤ Real.log T-2*(1/10000:ℝ)*k)
    (hhi : Real.log T-(1/10000:ℝ)*k ≤ U+5*k)
    (hcut : T*Real.exp (-((1/10000:ℝ)*k)) < logX/4) :
    ∃ a : ℝ,U ≤ a ∧ Real.log T-2*(1/10000:ℝ)*k ≤ a ∧
      a+1 ≤ Real.log T-(1/10000:ℝ)*k ∧
      c0 ≤ primeShellMass (boundedInterval E a (a+1)) ∧
      ∃ hp : 0 < primeShellMass (boundedInterval E a (a+1)),
        δ/2 ≤ ((primeShellPrior (boundedInterval E a (a+1)) hp).cmean
          (fun p => F.test p (n:ZMod p.val))).re := by
  have hvcut : Real.exp ((Real.log T-2*(1/10000:ℝ)*k)+(1/10000:ℝ)*k) ≤ logX/4 := by
    have he : (Real.log T-2*(1/10000:ℝ)*k)+(1/10000:ℝ)*k =
        Real.log T-(1/10000:ℝ)*k := by ring
    rw [he,sub_eq_add_neg,Real.exp_add,Real.exp_log hT]
    exact hcut.le
  obtain ⟨i,hil,hih,him⟩ := hrich (Real.log T-2*(1/10000:ℝ)*k) hlo (by linarith) hvcut
  have hi : i < 5*k := by
    have hh : (i:ℝ) < (5*k:ℕ) := by push_cast; linarith
    exact_mod_cast hh
  let j : Fin (5*k) := ⟨i,hi⟩
  have ha : U+(i:ℝ)+1 ≤ Real.log T-(1/10000:ℝ)*k := by linarith
  have hc : Real.exp (U+(i:ℝ)+1) ≤ logX/4 := by
    calc
      _ ≤ Real.exp (Real.log T-(1/10000:ℝ)*k) := Real.exp_le_exp.mpr ha
      _ = T*Real.exp (-((1/10000:ℝ)*k)) := by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log hT]
      _ ≤ _ := hcut.le
  have he := testedShellFamily_grid E base c0 U logX k j ⟨him,hc⟩
  have hp : 0 < primeShellMass (boundedInterval E (U+i) (U+i+1)) := by
    rw [←he]
    exact hm _
  refine ⟨U+i,le_add_of_nonneg_right (Nat.cast_nonneg i),hil,ha,him,hp,?_⟩
  simpa only [he] using hmean (gridTestIndex k j)

end Ostmann.Characters.HigherBiasSource

end

end OAI
