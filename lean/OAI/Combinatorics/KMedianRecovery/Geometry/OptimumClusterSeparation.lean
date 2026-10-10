import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Produce
import OAI.Combinatorics.KMedianRecovery.Recovery.PowerBound

namespace OAI

namespace MetricKMedianRecovery.Sensitivity
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma optimum_cluster_separation (F D O : Finset V) (hOF : O ⊆ F) (hO : O.Nonempty)
    (hO2 : 2 ≤ O.card) (beta : ℝ)
    (hcost : cost D O = optimum F D O.card)
    (hratio : (1+beta)*optimum F D O.card ≤ optimum F D (O.card-1)) :
    ∀ i ∈ O, beta*cost D O ≤ ((cluster D (nearest O hO) i).card:ℝ)*separation O i := by
  intro i hi
  have hrem : ∀ j ∈ ({i}:Finset V), neighbor O hO2 j ∉ ({i}:Finset V) := by
    intro j hj
    have he : j = i := Finset.mem_singleton.mp hj
    subst j
    simpa only [Finset.mem_singleton] using neighbor_ne O hO2 i
  have hr := removal_routing_bound D O {i} hO hO2 (Finset.singleton_subset_iff.mpr hi) hrem
  simp only [Finset.sdiff_singleton_eq_erase,Finset.sum_singleton] at hr
  have hop := optimum_le F D (O.erase i) (O.card-1)
    ((Finset.erase_subset i O).trans hOF) (erase_nonempty_of_two O hO2 i)
    (by rw [Finset.card_erase_of_mem hi])
  rw [← hcost] at hratio
  linarith

theorem sensitive_optimum (F D : Finset V) (hF : F.Nonempty) (k L : ℕ)
    (hL : 0 < L) (hk : 2*L < k) (hkF : k ≤ F.card)
    (xi : ℝ) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hsens : (1+xi)*optimum F D k < optimum F D (k-2*L)) :
    ∃ h : ℕ, k-2*L < h ∧ h ≤ k ∧
      (1+xi/(4*L))*optimum F D h ≤ optimum F D (h-1) ∧
      optimum F D h ≤ (1+xi)*optimum F D k ∧
      ∃ O : Finset V, ∃ hO : O.Nonempty, O ⊆ F ∧ O.card = h ∧
        cost D O = optimum F D h ∧
        ∀ i ∈ O, (xi/(4*L))*cost D O ≤
          ((cluster D (nearest O hO) i).card:ℝ)*separation O i := by
  obtain ⟨h,hlo,hhi,hratio,hcost⟩ := exists_sensitive (optimum F D) k L hL hk xi hxi hxi1
    (optimum_nonneg F D k) hsens
  obtain ⟨O,hOF,hO,hOh,hopt⟩ := optimum_attained_exact F D hF h (by omega) (hhi.trans hkF)
  refine ⟨h,hlo,hhi,hratio,hcost,O,hO,hOF,hOh,hopt,?_⟩
  apply optimum_cluster_separation F D O hOF hO (by omega) (xi/(4*L))
  · simpa only [hOh] using hopt
  · simpa only [hOh] using hratio

end MetricKMedianRecovery.Sensitivity

end OAI
