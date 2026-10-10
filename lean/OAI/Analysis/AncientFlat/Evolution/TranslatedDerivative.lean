import OAI.Analysis.AncientFlat.Evolution.EvolutionAlgebra

namespace OAI
open Set Filter
open scoped ZeroAtInfty BoundedContinuousFunction
variable {V : Type} [NormedAddCommGroup V]
lemma hasDerivAt_translated_toBCF (u : ℝ → C₀(V,ℂ)) (p : V →ᵇ ℂ) (s t : ℝ)
 (hp : HasDerivAt (fun r : ℝ => (u r).toBCF) p (s+t)) :
 HasDerivAt (fun r : ℝ => (u (s+r)).toBCF) p t := by
 have ha : HasDerivAt (fun r : ℝ => s+r) 1 t := (hasDerivAt_id t).const_add s
 convert hp.scomp t ha using 1 <;> first | rfl | simp only [one_smul]
lemma zeroAtInfty_add_neg_smul (d : C₀(V,ℂ)) : d+(-1 : ℂ) • d=0 := by
 ext x
 simp

end OAI
