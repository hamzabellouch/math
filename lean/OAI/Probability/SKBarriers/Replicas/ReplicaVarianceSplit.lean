import Mathlib
import OAI.Probability.SKBarriers.Gaussian.BlockStein
import OAI.Probability.SKBarriers.Replicas.ReplicaOverlap

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
open Matrix
section ReplicaVarianceSplit
variable {S : Type} [Fintype S]

theorem finiteReplicaMoment_const (p : S → ℝ) (hp : ∑ s, p s = 1) (c : ℝ) :
    finiteReplicaMoment p (fun _ _ => c) = c := by
  simp only [finiteReplicaMoment,← Finset.mul_sum,← Finset.sum_mul,hp,mul_one,one_mul]

theorem finiteReplicaMoment_add (p : S → ℝ) (g h : S → S → ℝ) :
    finiteReplicaMoment p (fun s t => g s t+h s t) = finiteReplicaMoment p g+finiteReplicaMoment p h := by
  simp only [finiteReplicaMoment,mul_add,Finset.sum_add_distrib]

theorem finiteReplicaMoment_const_mul (p : S → ℝ) (g : S → S → ℝ) (c : ℝ) :
    finiteReplicaMoment p (fun s t => c*g s t) = c*finiteReplicaMoment p g := by
  simp only [finiteReplicaMoment,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro t _
  ring

theorem finiteReplicaMoment_sub_square (p : S → ℝ) (hp : ∑ s, p s = 1) (g : S → S → ℝ) (r : ℝ) :
    finiteReplicaMoment p (fun s t => (g s t-r)^2) =
      finiteReplicaMoment p (fun s t => (g s t)^2)-2*r*finiteReplicaMoment p g+r^2 := by
  have he : (fun s t => (g s t-r)^2) = fun s t => (g s t)^2+(-2*r)*g s t+r^2 := by
    funext s t; ring
  rw [he,finiteReplicaMoment_add,finiteReplicaMoment_add,finiteReplicaMoment_const_mul,finiteReplicaMoment_const p hp]
  ring

theorem finiteReplicaMoment_variance_split (p : S → ℝ) (hp : ∑ s, p s = 1) (g : S → S → ℝ) (r : ℝ) :
    finiteReplicaMoment p (fun s t => (g s t-r)^2) =
      finiteReplicaMoment p (fun s t => (g s t-finiteReplicaMoment p g)^2)+(finiteReplicaMoment p g-r)^2 := by
  rw [finiteReplicaMoment_sub_square p hp,finiteReplicaMoment_sub_square p hp]
  ring

theorem finiteReplicaMoment_normalizedDot {N : ℕ} (p : S → ℝ) (v : S → Fin N → ℝ) :
    finiteReplicaMoment p (fun s t => normalizedDot (v s) (v t)) = normalizedSquare (finiteMean p v) := by
  have he : (fun s t => normalizedDot (v s) (v t)) = fun s t => (N : ℝ)⁻¹*(v s ⬝ᵥ v t) := by
    funext s t; simp only [normalizedDot,dotProduct,div_eq_mul_inv]; ring
  rw [he,finiteReplicaMoment_const_mul,finiteReplicaMoment_dot]
  simp only [normalizedSquare,dotProduct,pow_two,div_eq_mul_inv,mul_comm]

theorem finiteCovariance_trace_square_nonneg {I : Type} [Fintype I]
    (p : S → ℝ) (v : S → I → ℝ) (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1) :
    0 ≤ ((finiteCovariance p v)*(finiteCovariance p v)).trace := by
  have h := (finiteCovariance_posSemidef p v hp hs).isHermitian
  simpa only [h.eq] using (Matrix.posSemidef_conjTranspose_mul_self (finiteCovariance p v)).trace_nonneg

theorem finiteReplica_normalized_variance_le {N : ℕ} (hN : 0 < N)
    (p : S → ℝ) (v : S → Fin N → ℝ) (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1)
    (hv : ∀ s i, |v s i| ≤ 1) :
    finiteReplicaMoment p (fun s t => (normalizedDot (v s) (v t)-normalizedSquare (finiteMean p v))^2) ≤
      ((finiteCovariance p v)*(finiteCovariance p v)).trace/(N : ℝ)^2+
      2*Real.sqrt (((finiteCovariance p v)*(finiteCovariance p v)).trace/(N : ℝ)^2) := by
  let T := ((finiteCovariance p v)*(finiteCovariance p v)).trace
  let m := finiteMean p v
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hT : 0 ≤ T := finiteCovariance_trace_square_nonneg p v hp hs
  have he : (fun s t => (normalizedDot (v s) (v t)-normalizedSquare m)^2) =
      fun s t => ((N : ℝ)^2)⁻¹*(v s ⬝ᵥ v t-m ⬝ᵥ m)^2 := by
    funext s t
    simp only [normalizedDot,normalizedSquare,dotProduct,pow_two,div_eq_mul_inv]
    ring
  rw [he,finiteReplicaMoment_const_mul]
  have H := mul_le_mul_of_nonneg_left (finiteReplica_variance_le p v hp hs hv)
    (inv_nonneg.2 (sq_nonneg (N : ℝ)))
  apply H.trans_eq
  simp only [Fintype.card_fin]
  rw [Real.sqrt_div hT,Real.sqrt_sq hn.le]
  change ((N : ℝ)^2)⁻¹*(T+2*(N : ℝ)*Real.sqrt T) = T/(N : ℝ)^2+2*(Real.sqrt T/(N : ℝ))
  field_simp [ne_of_gt hn]
end ReplicaVarianceSplit
end SK.Analytic

end
end

end

end OAI
