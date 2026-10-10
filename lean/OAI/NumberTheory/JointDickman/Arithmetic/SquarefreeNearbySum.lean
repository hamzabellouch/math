import OAI.NumberTheory.JointDickman.Amplification.RationalPartialSums
import OAI.NumberTheory.JointDickman.Amplification.NearbyAdditiveSums

namespace OAI

/-! # The needed Montgomery--Vaughan special case near a rational -/
namespace JointDickman
open Finset

theorem squarefree_near_rational_sum_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
    (∀ n, ¬Squarefree n → f n=0) → ∀ (N B q : ℕ) (u : ℤ) (θ V : ℝ),
    0 < N → 2 ≤ B → (80:ℝ)*Real.log B ≤ B →
    (B:ℝ)/2 ≤ Real.log N → Real.log N ≤ 3*(B:ℝ) →
    0 < q → u.natAbs.Coprime q → (B:ℝ)^12 ≤ q → (q:ℝ) ≤ N/(B:ℝ)^10 →
    (N:ℝ)*|θ-(u:ℝ)/q| ≤ V →
    ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*θ)‖ ≤
      C*(1+2*Real.pi*V)*N*(1+Real.log B)/(B:ℝ) := by
  obtain ⟨C,hC,hpartial⟩ := squarefree_rational_uniform_partial_sums
  refine ⟨C,hC,?_⟩
  intro f hf hb hs N B q u θ V hN hB hlogB hloglo hloghi hq hu hqlo hqhi hV
  let T := C*N*(1+Real.log B)/(B:ℝ)
  have hT : 0 ≤ T := by
    dsimp [T]
    have hlog : 0 ≤ Real.log B := Real.log_natCast_nonneg B
    positivity
  have h := nearby_additive_sum_bound (fun n => (f n:ℂ)) N θ ((u:ℝ)/q) T hT
    (hpartial f hf hb hs N B q u hN hB hlogB hloglo hloghi hq hu hqlo hqhi)
  apply h.trans
  calc
    _ ≤ T*(1+2*Real.pi*V) := by
      apply mul_le_mul_of_nonneg_left _ hT
      nlinarith [Real.pi_pos]
    _ = _ := by dsimp [T]; ring

end JointDickman

end OAI
