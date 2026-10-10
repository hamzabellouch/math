import OAI.NumberTheory.JointDickman.Amplification.PolylogMultiplicativeSum

namespace OAI

/-! # Both signs of the rational numerator -/
namespace JointDickman
open Finset
open scoped ComplexConjugate

lemma real_additive_sum_norm_neg (f : ℕ → ℝ) (S : Finset ℕ) (θ : ℝ) :
    ‖∑ n ∈ S, (f n:ℂ)*additivePhase ((n:ℝ)*(-θ))‖ =
      ‖∑ n ∈ S, (f n:ℂ)*additivePhase ((n:ℝ)*θ)‖ := by
  have he : conj (∑ n ∈ S, (f n:ℂ)*additivePhase ((n:ℝ)*θ)) =
      ∑ n ∈ S, (f n:ℂ)*additivePhase ((n:ℝ)*(-θ)) := by
    rw [map_sum]
    apply sum_congr rfl
    intro n hn
    rw [map_mul,Complex.conj_ofReal,additivePhase_conj,mul_neg]
  rw [←he,Complex.norm_conj]

theorem squarefree_integer_rational_polylog_sum_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
    (∀ n, ¬Squarefree n → f n=0) → ∀ (N B q : ℕ) (u : ℤ),
    2 ≤ B → B^20 ≤ N → 0 < q → u.natAbs.Coprime q → Real.log N ≤ 3*(B:ℝ) →
    (B:ℝ)^12 ≤ q → (q:ℝ) ≤ N/(B:ℝ)^8 →
    ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*((u:ℝ)/q))‖ ≤
      C*N*(1+Real.log B)/Real.log N := by
  obtain ⟨C,hC,hbound⟩ := squarefree_rational_polylog_sum_bound
  refine ⟨C,hC,?_⟩
  intro f hf hb hs N B q u hB hBN hq hu hlog hqlo hqhi
  obtain ⟨a,rfl|rfl⟩ := Int.eq_nat_or_neg u
  · exact hbound f hf hb hs N B q a hB hBN hq (by simpa using hu) hlog hqlo hqhi
  · have h := hbound f hf hb hs N B q a hB hBN hq (by simpa using hu) hlog hqlo hqhi
    simpa only [Int.cast_neg,Int.cast_natCast,neg_div,real_additive_sum_norm_neg] using h

end JointDickman

end OAI
