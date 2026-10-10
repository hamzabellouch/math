import Mathlib
import OAI.Probability.SKBarriers.Replicas.ReplicaFlip

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem replicaGibbsMass_le_or_or_flip {n d : ℕ} (a : Fin d) (β : ℝ) (J : Disorder n)
    (S T P : Finset (ReplicaConfig n d))
    (h : ∀ s∈S,s∈T ∨ replicaFlip a s∈T ∨ s∈P) :
    replicaGibbsMass β J S≤2*replicaGibbsMass β J T+replicaGibbsMass β J P := by
  classical
  have hsub : S⊆(T∪T.image (replicaFlip a))∪P := by
    intro s hs
    rcases h s hs with h|h|h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨replicaFlip a s,h,replicaFlip_involutive a s⟩))
    · exact Finset.mem_union_right _ h
  have H := (replicaGibbsMass_mono β J hsub).trans
    (replicaGibbsMass_union_le β J (T∪T.image (replicaFlip a)) P)
  have H' := replicaGibbsMass_union_le β J T (T.image (replicaFlip a))
  rw [replicaGibbsMass_flip] at H'
  linarith

theorem replicaGibbsMass_integral_or_or_flip {n d : ℕ} (a : Fin d) (β : ℝ)
    (S T P : Finset (ReplicaConfig n d))
    (h : ∀ s∈S,s∈T ∨ replicaFlip a s∈T ∨ s∈P) :
    (∫ J,replicaGibbsMass β J S ∂disorderLaw n)≤
      2*(∫ J,replicaGibbsMass β J T ∂disorderLaw n)+(∫ J,replicaGibbsMass β J P ∂disorderLaw n) := by
  have H := integral_mono (replicaGibbsMass_integrable β S)
    (((replicaGibbsMass_integrable β T).const_mul 2).add (replicaGibbsMass_integrable β P))
    (fun J => replicaGibbsMass_le_or_or_flip a β J S T P h)
  simpa only [Pi.add_apply,integral_add ((replicaGibbsMass_integrable β T).const_mul 2) (replicaGibbsMass_integrable β P),
    integral_const_mul] using H

end SK.Analytic

end
end

end OAI
