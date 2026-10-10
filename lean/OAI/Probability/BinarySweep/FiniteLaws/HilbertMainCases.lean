import Mathlib
import OAI.Probability.BinarySweep.Analytic.OneAxisBase
import OAI.Probability.BinarySweep.Conditional.ConditionalAverage
import OAI.Probability.BinarySweep.GridBounds.GroupedLogBounds

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Signed

lemma logMoment_le_iff_le_exp (T x : ℝ) : logMoment T ≤ (x:EReal) ↔ T ≤ Real.exp x := by
  by_cases hT : T ≤ 0
  · simp only [logMoment,ENNReal.ofReal_eq_zero.mpr hT, ENNReal.log_zero,bot_le,true_iff]
    exact hT.trans (Real.exp_pos _).le
  · have hT' := lt_of_not_ge hT
    rw [logMoment,ENNReal.log_ofReal_of_pos hT',EReal.coe_le_coe_iff]
    exact Real.log_le_iff_le_exp hT'

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma hilbert_conditional_dimension {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) (q : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V)
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) :
    evenMoment q (groupAverage ρ (fun g => (conditionalGroupLaw H z g:ℂ))) ≤ Module.finrank ℂ V := by
  let E := (stdOrthonormalBasis ℂ V).repr
  let σ := conjugateRep ρ E.toLinearEquiv
  have hσ (g) (v) : ‖σ g v‖=‖v‖ := by
    change ‖E (ρ g (E.symm v))‖=‖v‖
    rw [E.norm_map,hρ,E.symm.norm_map]
  have he := equivalent_evenMoment ρ σ (conjugateEquiv ρ E.toLinearEquiv) hρ hσ
    (fun g => (conditionalGroupLaw H z g:ℂ)) q
  rw [he,←conditionalMoment_evenMoment H z σ q]
  exact traceMoment_le_dimension q _ (conditionalOperator_norm_le_one H hz hz1 σ hσ)

lemma hilbert_conditional_automatic {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) (q : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V) [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖)
    (ha : (1+cExponent (gridSize bits))*Real.log (Module.finrank ℂ V) ≤
      eExponent (gridSize bits)*h*Real.log (gridSize bits)-pathCost H) :
    evenMoment q (groupAverage ρ (fun g => (conditionalGroupLaw H z g:ℂ))) ≤
    Real.exp (-cExponent (gridSize bits)*Real.log (Module.finrank ℂ V)+
      eExponent (gridSize bits)*h*Real.log (gridSize bits)-pathCost H) := by
  have hD : (0:ℝ) < Module.finrank ℂ V := by exact_mod_cast irreducible_finrank_pos ρ
  refine (hilbert_conditional_dimension H z hz hz1 q ρ hρ).trans ?_
  rw [←Real.exp_log hD]
  apply Real.exp_le_exp.mpr
  rw [Real.log_exp]
  linarith

lemma hilbert_conditional_one_axis {r q : ℕ}
    (hr : (400000000:ℝ) ≤ (r:ℝ)*Real.log 2) (hq : 0 < q)
    (bits : Fin 1 → ℕ) (hd : ∀j,r ≤ bits j ∧ bits j ≤ 2*r)
    {h : ℕ} (H : PathFamily bits h) {z : ℝ} (hz : 0 ≤ z) (hzr : z ≤ oneAxisRadius r)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V) [ρ.IsIrreducible]
    (hρ : ∀g v,‖ρ g v‖=‖v‖) :
    evenMoment q (groupAverage ρ (fun g => (conditionalGroupLaw H z g:ℂ))) ≤
    Real.exp (-cExponent (gridSize bits)*Real.log (Module.finrank ℂ V)+
      eExponent (gridSize bits)*h*Real.log (gridSize bits)-pathCost H) := by
  let E := (stdOrthonormalBasis ℂ V).repr
  let σ := conjugateRep ρ E.toLinearEquiv
  have : σ.IsIrreducible := irreducible_equiv ρ σ (conjugateEquiv ρ E.toLinearEquiv)
  have hσ (g) (v) : ‖σ g v‖=‖v‖ := by
    change ‖E (ρ g (E.symm v))‖=‖v‖
    rw [E.norm_map,hρ,E.symm.norm_map]
  have he := equivalent_evenMoment ρ σ (conjugateEquiv ρ E.toLinearEquiv) hρ hσ
    (fun g => (conditionalGroupLaw H z g:ℂ)) q
  rw [he,←conditionalMoment_evenMoment H z σ q]
  exact (logMoment_le_iff_le_exp _ _).mp (conditional_moment_one_axis hr hq bits hd H hz hzr σ hσ)

end BinaryCoordinateSweeps

end

end OAI
