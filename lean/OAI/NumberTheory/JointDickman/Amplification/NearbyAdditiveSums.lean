import OAI.NumberTheory.JointDickman.Amplification.AdditivePhaseVariation

namespace OAI

/-! # Transfer a uniform partial-sum bound to a nearby frequency -/
namespace JointDickman
open Finset

lemma sum_positive_as_shifted {R : Type*} [AddCommMonoid R] (f : ℕ → R) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, f n) = ∑ i ∈ range N, f (i+1) := by
  have hi : Ioc 0 N = Ico 1 (N+1) := by
    ext n
    simp only [mem_Ioc,mem_Ico]
    omega
  rw [hi]
  symm
  simpa only [Nat.zero_add,Nat.Ico_zero_eq_range] using sum_Ico_add' f 0 N 1

theorem nearby_additive_sum_bound (f : ℕ → ℂ) (N : ℕ) (θ φ T : ℝ)
    (hT : 0 ≤ T)
    (hf : ∀ k ≤ N, ‖∑ n ∈ Ioc 0 k, f n*additivePhase ((n:ℝ)*φ)‖ ≤ T) :
    ‖∑ n ∈ Ioc 0 N, f n*additivePhase ((n:ℝ)*θ)‖ ≤
      T*(1+2*Real.pi*N*|θ-φ|) := by
  let z := fun i : ℕ => f (i+1)*additivePhase (((i+1:ℕ):ℝ)*φ)
  let w := fun i : ℕ => additivePhase (((i+1:ℕ):ℝ)*(θ-φ))
  have hz (k : ℕ) (hk : k ≤ N) : ‖∑ i ∈ range k, z i‖ ≤ T := by
    simpa only [sum_positive_as_shifted] using hf k hk
  have hw (i : ℕ) (_hi : i < N) : ‖w i‖ ≤ 1 := (norm_additivePhase _).le
  have hd (i : ℕ) (_hi : i < N) : ‖w (i+1)-w i‖ ≤ 2*Real.pi*|θ-φ| := by
    apply (additivePhase_difference_norm_le _ _).trans_eq
    congr 2
    push_cast
    ring
  have he : (∑ n ∈ Ioc 0 N, f n*additivePhase ((n:ℝ)*θ)) =
      ∑ i ∈ range N, w i*z i := by
    rw [sum_positive_as_shifted]
    apply sum_congr rfl
    intro i hi
    dsimp [w,z]
    rw [show (((i+1:ℕ):ℝ)*θ) = (((i+1:ℕ):ℝ)*(θ-φ))+(((i+1:ℕ):ℝ)*φ) by ring,
      additivePhase_add]
    ring
  rw [he]
  have h := bounded_partial_sums_weighted z w N T 1 (2*Real.pi*|θ-φ|)
    hT zero_le_one (by positivity) hz hw hd
  convert h using 1
  ring

end JointDickman

end OAI
