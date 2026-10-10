import Mathlib
import OAI.Probability.SKBarriers.Replicas.ReplicaVarianceSplit

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

section FiniteReplicaAlgebra
variable {S : Type} [Fintype S]

theorem finiteReplicaMoment_separable_square (p c : S → ℝ) :
    finiteReplicaMoment p (fun s t => c s*c t) = (∑ s, p s*c s)^2 := by
  simp only [finiteReplicaMoment,pow_two,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem finiteReplicaMoment_sum {I : Type} [Fintype I] (p : S → ℝ) (g : I → S → S → ℝ) :
    finiteReplicaMoment p (fun s t => ∑ i, g i s t) = ∑ i, finiteReplicaMoment p (g i) := by
  simp only [finiteReplicaMoment,Finset.mul_sum]
  calc
    _ = ∑ s, ∑ i, ∑ t, p s*p t*g i s t := by
      apply Finset.sum_congr rfl; intro s _; rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]
end FiniteReplicaAlgebra

theorem replica_edge_polynomial {N : ℕ} (hN : 0 < N) (s t : Config N) :
    2*(∑ e : Edge N, (spin (s e.val.1)*spin (s e.val.2))*(spin (t e.val.1)*spin (t e.val.2))) =
      (N:ℝ)^2*(normalizedDot (fun i => spin (s i)) (fun i => spin (t i)))^2-N := by
  have H := sum_sq_eq_edges (fun i => spin (s i)*spin (t i))
  have hd : (∑ i : Fin N, (spin (s i)*spin (t i))^2) = (N:ℝ) := by simp [mul_pow]
  rw [hd] at H
  have he : (∑ e : Edge N, (spin (s e.val.1)*spin (s e.val.2))*(spin (t e.val.1)*spin (t e.val.2))) =
      ∑ e : Edge N, (spin (s e.val.1)*spin (t e.val.1))*(spin (s e.val.2)*spin (t e.val.2)) := by
    apply Finset.sum_congr rfl; intro e _; ring
  rw [he]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold normalizedDot
  field_simp
  simp only [mul_assoc] at H ⊢
  nlinarith [H]

theorem finiteReplica_edge_variation {N : ℕ} (hN : 0 < N) (p : Config N → ℝ)
    (hp : ∑ s, p s = 1) :
    2*(∑ e : Edge N, (1-(∑ s, p s*(spin (s e.val.1)*spin (s e.val.2)))^2)) =
      (N:ℝ)^2*(1-finiteReplicaMoment p (fun s t =>
        (normalizedDot (fun i => spin (s i)) (fun i => spin (t i)))^2)) := by
  have hc := sum_sq_eq_edges (fun _ : Fin N => (1:ℝ))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,one_pow] at hc
  have H := congrArg (finiteReplicaMoment p) (funext fun s => funext fun t => replica_edge_polynomial hN s t)
  rw [finiteReplicaMoment_const_mul,finiteReplicaMoment_sum] at H
  simp_rw [finiteReplicaMoment_separable_square] at H
  have hr : finiteReplicaMoment p (fun s t => (N:ℝ)^2 *
      (normalizedDot (fun i => spin (s i)) (fun i => spin (t i)))^2-N) =
      (N:ℝ)^2*finiteReplicaMoment p (fun s t =>
        (normalizedDot (fun i => spin (s i)) (fun i => spin (t i)))^2)-N := by
    simp only [sub_eq_add_neg,finiteReplicaMoment_add,finiteReplicaMoment_const_mul,
      finiteReplicaMoment_const p hp]
  rw [hr] at H
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  linarith
end SK.Analytic

end
end

end

end OAI
