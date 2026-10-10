import Mathlib
import OAI.Probability.SKBarriers.Interpolation.RestrictedConcentration

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem replicaGibbsMass_tail {n d : ℕ} (β : ℝ) (J : Disorder n)
    (S : Finset (ReplicaConfig n d)) :
    replicaGibbsMass β J (Finset.univ.filter (fun s : ReplicaConfig n (d+1) => Fin.tail s∈S))=
      replicaGibbsMass β J S := by
  classical
  unfold replicaGibbsMass
  rw [Finset.sum_filter]
  calc
    _ = ∑ p : Config n × ReplicaConfig n d,if p.2∈S then gibbs β J p.1*∏ a,gibbs β J (p.2 a) else 0 := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (d+1) => Config n)).symm
      intro s
      simp only [Fin.consEquiv_symm_apply,Fin.prod_univ_succ,Fin.tail]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [show ∀ (x : Config n) (s : ReplicaConfig n d),
          (if s∈S then gibbs β J x*∏ a,gibbs β J (s a) else 0)=
          gibbs β J x*(if s∈S then ∏ a,gibbs β J (s a) else 0) by intros; split_ifs <;> simp]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul,gibbs_sum,one_mul,← Finset.sum_filter]
      simp

end SK.Analytic

end
end

end OAI
