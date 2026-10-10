import OAI.NumberTheory.Ostmann.Characters.TemplateActualPhasePairRows

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem actualPivotSurviving_pair (k j:ℕ) (hj:j<k) (width:Role→ℕ)
    (p:UnaryOutputIndex k j width→ℕ) [∀i,Fact (p i).Prime]
    (hc:Pairwise (fun i h => (p i).Coprime (p h)))
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (hχ:∀i,χ i≠1) (a:∀i,ZMod (p i))
    (P:ℕ) (s:ℤ) (t:HistoryReconstruction.Tree (j+1))
    (ht:∀i,HistoryFrequencyUnits (p i) (j+1) s t)
    (he:s*(P:ℤ)=t.1.1*(primeCopyProduct p false:ℤ)-t.1.2*(primeCopyProduct p true:ℤ))
    (hP:∀i,(P:ZMod (p i))≠0) :
    actualPivotSurviving k j hj width (fun i => p (survivingBranchIndex true i))
      (fun i => χ (survivingBranchIndex true i)) (fun i => a (survivingBranchIndex true i))
      P t.1.1 t.2.1 *
    conj (actualPivotSurviving k j hj width (fun i => p (survivingBranchIndex false i))
      (fun i => χ (survivingBranchIndex false i)) (fun i => a (survivingBranchIndex false i))
      P t.1.2 t.2.2) =
    actualHistoryPhase k (j+1) width
      (fun i => p (nextConstituentEquiv (schedule k j) j width i))
      (fun i => χ (nextConstituentEquiv (schedule k j) j width i))
      (fun i => a (nextConstituentEquiv (schedule k j) j width i)) s t := by
  have hl := actualPivotSurviving_rows k j hj width p χ hχ a P s t ht true
  have hr := actualPivotSurviving_rows k j hj width p χ hχ a P s t ht false
  dsimp only at hl hr
  simp only [unaryChildFrequency,unaryChildTree,Bool.false_eq_true,ite_true,ite_false] at hl hr
  rw [hl,hr]
  have hh := complete_history_phase_constituent_transport k j hj width p hc χ hχ a
    (P:ℤ) s t ht he (by simpa only [Int.cast_natCast] using hP)
  dsimp only at hh
  rw [← hh]
  simp only [branchCopiedTranslation_true,branchCopiedTranslation_false,
    map_mul,map_prod,Finset.prod_mul_distrib]
  ring

end Ostmann.Characters.Template

end

end OAI
