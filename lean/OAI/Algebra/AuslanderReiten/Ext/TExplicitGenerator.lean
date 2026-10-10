import OAI.Algebra.AuslanderReiten.Ext.TExtPolynomial
import OAI.Algebra.AuslanderReiten.Cocycles.CocycleExt

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q
local notation "S" => ModuleCat.of T (Simple q)

def tExplicitP : TSelfExt q 3 := CocycleData.simpleExtClass q

theorem tExplicitP_ne_zero (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) : tExplicitP q ≠ 0 :=
  CocycleData.simpleExtClass_ne_zero q hq hq1

variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD
variable (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q)
include hq hq1 h

@[simp] theorem tTauPower_one : tTauPower q hq hq1 h 1 = tTau q hq hq1 h := by
  change (tTau q hq hq1 h).comp (tTauPower q hq hq1 h 0) (by omega) = tTau q hq hq1 h
  rw [tTauPower_zero]
  exact Abelian.Ext.comp_mk₀_id _

theorem tExplicitP_generator : ∃ a : k, a ≠ 0 ∧ tExplicitP q = a • tTau q hq hq1 h := by
  obtain ⟨a, ha, _⟩ := tSelfExt_coefficient q hq hq1 h 1 (tExplicitP q)
  have hpa : tExplicitP q = a • tTau q hq hq1 h := by
    simpa only [tTauPower_one] using ha.symm
  refine ⟨a, ?_, hpa⟩
  intro ha0
  apply tExplicitP_ne_zero q hq hq1
  simpa only [ha0, zero_smul] using hpa

theorem tExplicitP_multiply_bijective (n : ℕ) :
    Function.Bijective (fun b : TSelfExt q n => (tExplicitP q).comp b (by omega : 3 + n = n + 3)) := by
  obtain ⟨a, ha, hp⟩ := tExplicitP_generator q hq hq1 h
  rw [hp]
  simpa only [Function.comp_def, Abelian.Ext.smul_comp, LinearEquiv.smulOfNeZero_apply] using
    ((LinearEquiv.smulOfNeZero (K := k) (M := TSelfExt q (n + 3)) a ha).bijective.comp
      (tTau_multiply_bijective q hq hq1 h n))

end ArExplicit.Resolution

end

end OAI
