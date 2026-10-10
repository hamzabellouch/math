import Mathlib
import OAI.Probability.SKBarriers.Interpolation.RestrictedConcentration

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def replicaFlip {n d : ℕ} (a : Fin d) (s : ReplicaConfig n d) : ReplicaConfig n d :=
  fun i => if i=a then flip (s i) else s i

@[simp] theorem replicaFlip_apply_same {n d : ℕ} (a : Fin d) (s : ReplicaConfig n d) :
    replicaFlip a s a=flip (s a) := by simp [replicaFlip]

@[simp] theorem replicaFlip_involutive {n d : ℕ} (a : Fin d) :
    Function.Involutive (@replicaFlip n d a) := by
  intro s
  funext i
  by_cases hi : i=a <;> simp [replicaFlip,hi]

theorem replicaGibbsWeight_flip {n d : ℕ} (a : Fin d) (β : ℝ) (J : Disorder n)
    (s : ReplicaConfig n d) : (∏ i,gibbs β J (replicaFlip a s i))=∏ i,gibbs β J (s i) := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i=a <;> simp [replicaFlip,hi]

theorem replicaGibbsMass_flip {n d : ℕ} (a : Fin d) (β : ℝ) (J : Disorder n)
    (S : Finset (ReplicaConfig n d)) :
    replicaGibbsMass β J (S.image (replicaFlip a))=replicaGibbsMass β J S := by
  classical
  unfold replicaGibbsMass
  rw [Finset.sum_image (replicaFlip_involutive a).injective.injOn]
  exact Finset.sum_congr rfl (fun s _ => replicaGibbsWeight_flip a β J s)

theorem replicaGibbsMass_mono {n d : ℕ} (β : ℝ) (J : Disorder n)
    {S T : Finset (ReplicaConfig n d)} (h : S ⊆ T) :
    replicaGibbsMass β J S ≤ replicaGibbsMass β J T :=
  Finset.sum_le_sum_of_subset_of_nonneg h
    (fun s _ _ => Finset.prod_nonneg (fun a _ => (gibbs_pos β J (s a)).le))

theorem replicaGibbsMass_union_le {n d : ℕ} (β : ℝ) (J : Disorder n)
    (S T : Finset (ReplicaConfig n d)) :
    replicaGibbsMass β J (S∪T) ≤ replicaGibbsMass β J S+replicaGibbsMass β J T := by
  have H := @Finset.sum_union_inter _ ℝ S T _ (fun s : ReplicaConfig n d => ∏ a,gibbs β J (s a)) _
  have H' := replicaGibbsMass_nonneg β J (S∩T)
  change replicaGibbsMass β J (S∪T)+replicaGibbsMass β J (S∩T)=
    replicaGibbsMass β J S+replicaGibbsMass β J T at H
  linarith

theorem replicaGibbsMass_le_twice_oriented {n d : ℕ} (a : Fin d) (β : ℝ) (J : Disorder n)
    (S T : Finset (ReplicaConfig n d))
    (h : ∀ s∈S,s∈T ∨ replicaFlip a s∈T) :
    replicaGibbsMass β J S ≤ 2*replicaGibbsMass β J T := by
  classical
  have hsub : S ⊆ T∪T.image (replicaFlip a) := by
    intro s hs
    rcases h s hs with ht|ht
    · exact Finset.mem_union_left _ ht
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨replicaFlip a s,ht,replicaFlip_involutive a s⟩)
  have H := (replicaGibbsMass_mono β J hsub).trans (replicaGibbsMass_union_le β J T (T.image (replicaFlip a)))
  rw [replicaGibbsMass_flip] at H
  linarith

end SK.Analytic

end
end

end OAI
