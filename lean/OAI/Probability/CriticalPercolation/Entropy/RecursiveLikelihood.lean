import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.MarkedBits

namespace OAI

section
section
namespace CriticalPercolation.ReverseReference
open scoped Classical

lemma trajectory_dominance (a r v : ℕ → ℝ) (n : ℕ)
    (hr : ∀ i < n, 0 ≤ r i) (hv : ∀ i < n, 0 ≤ v i)
    (hstep : ∀ i < n, a i * r i ≤ a (i+1) * v i) :
    a 0 * ∏ i : Fin n, r i.val ≤ a n * ∏ i : Fin n, v i.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := ih (fun i hi => hr i (hi.trans (Nat.lt_succ_self n)))
      (fun i hi => hv i (hi.trans (Nat.lt_succ_self n)))
      (fun i hi => hstep i (hi.trans (Nat.lt_succ_self n)))
    rw [Fin.prod_univ_castSucc,Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    calc
      _ = (a 0 * ∏ i : Fin n, r i.val) * r n := by ring
      _ ≤ (a n * ∏ i : Fin n, v i.val) * r n := mul_le_mul_of_nonneg_right hh (hr n (Nat.lt_succ_self n))
      _ = (a n*r n)*(∏ i : Fin n, v i.val) := by ring
      _ ≤ (a (n+1)*v n)*(∏ i : Fin n, v i.val) := mul_le_mul_of_nonneg_right
        (hstep n (Nat.lt_succ_self n)) (Finset.prod_nonneg fun i _ => hv i.val (i.isLt.trans (Nat.lt_succ_self n)))
      _ = _ := by ring

lemma joint_trajectory_dominance {X M : Type*} [Fintype X] [Fintype M]
    (μ : X → ℝ) (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X)
    (n : ℕ) (a : Fin n → X → M → ℝ) (σ : ℕ → X) (m : ℕ → M)
    (m' : Fin n → M) (r v : Fin n → ℝ)
    (hu : ∀ i < n, u i (σ (i+1)) (m i) = σ i)
    (hr : ∀ i, 0 ≤ r i)
    (hv : ∀ i, 0 ≤ k i.val (σ (i.val+1)) (m i.val) * a i (σ 0) (m' i) * v i)
    (hs : ∀ i : Fin n, μ (σ i.val) * r i ≤
      μ (σ (i.val+1)) * (k i.val (σ (i.val+1)) (m i.val) * a i (σ 0) (m' i) * v i)) :
    μ (σ 0) * ∏ i, r i ≤
      joint μ k u a n (σ n,(fun i => m i.val),m') * ∏ i, v i := by
  let r' : ℕ → ℝ := fun j => if hj : j<n then r ⟨j,hj⟩ else 0
  let v' : ℕ → ℝ := fun j => if hj : j<n then
    k j (σ (j+1)) (m j) * a ⟨j,hj⟩ (σ 0) (m' ⟨j,hj⟩) * v ⟨j,hj⟩ else 0
  have hh := trajectory_dominance (fun j => μ (σ j)) r' v' n
    (fun j hj => by simpa only [r',dite_eq_left hj] using hr ⟨j,hj⟩)
    (fun j hj => by simpa only [v',dite_eq_left hj] using hv ⟨j,hj⟩)
    (fun j hj => by simpa only [r',v',dite_eq_left hj] using hs ⟨j,hj⟩)
  simp only [r',v',dite_eq_left (Fin.isLt _),Finset.prod_mul_distrib] at hh
  unfold joint terminalWeight
  dsimp only
  rw [recover_trajectory u σ m n hu,
    weight_trajectory k u σ m (fun j => k j (σ (j+1)) (m j)) n hu (fun _ _ => rfl)]
  convert hh using 1
  ring

end CriticalPercolation.ReverseReference
end
end

end OAI
