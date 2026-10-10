import Mathlib
import OAI.Combinatorics.KMedian.Rounding.WeightedPartial
import OAI.Combinatorics.KMedian.Probability.ProbabilitySupport
import OAI.Combinatorics.KMedian.Probability.PushforwardLaw

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding
open Finset MarginalRounding
variable {I : Type} [Fintype I] [DecidableEq I]

theorem exact_law (p : I → ℝ) (K : ℕ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i=K) :
    ∃ μ : FiniteLaw (Finset I),
      (∀ S, 0 < μ.weight S → S.card=K) ∧
      (∀ i, μ.prob (fun S => i ∈ S)=p i) ∧
      (∀ i j, i ≠ j → μ.expect (fun S => indicator S i*indicator S j) ≤ p i*p j) := by
  classical
  obtain ⟨Ω,instΩ,hex⟩ := exists_partial_law p (fun _ => 1) hp0 hp1 (by intro i; norm_num)
  let := instΩ
  obtain ⟨μ,Q,hs,hm,hp⟩ := hex
  have hsumq : ∀ ω, 0 < μ.weight ω → (∑ i, Q ω i)=K := by
    intro ω hω
    simpa only [one_mul,hsum] using (hs ω hω).2.2.2
  have hint : ∀ ω, 0 < μ.weight ω → ∀ i, Q ω i=0 ∨ Q ω i=1 := by
    intro ω hω i
    have hb := hs ω hω
    apply nonfractional_integral hb.1 hb.2.1
    intro hi
    obtain ⟨j,hj,hji⟩ := second_fractional hb.1 hb.2.1 (hsumq ω hω) hi
    have hh : 1 < (fractional (Q ω)).card := one_lt_card.mpr ⟨j,hj,i,hi,hji⟩
    omega
  let S := fun ω => univ.filter (fun i => Q ω i=1)
  have hbit : ∀ ω, 0 < μ.weight ω → ∀ i, indicator (S ω) i=Q ω i := by
    intro ω hω i
    rcases hint ω hω i with h | h <;> simp only [indicator,S,mem_filter,mem_univ,true_and,h] <;> norm_num
  have hcard : ∀ ω, 0 < μ.weight ω → (S ω).card=K := by
    intro ω hω
    have he : ((S ω).card:ℝ)=∑ i, Q ω i := by
      calc
        _ = ∑ i, indicator (S ω) i := by simp only [indicator,sum_boole,filter_univ_mem]
        _ = _ := sum_congr rfl (fun i _ => hbit ω hω i)
    exact_mod_cast he.trans (hsumq ω hω)
  refine ⟨μ.map S,?_,?_,?_⟩
  · intro A hA
    obtain ⟨ω,hω,rfl⟩ := μ.support_map S A hA
    exact hcard ω hω
  · intro i
    change (μ.map S).expect (fun A => indicator A i)=p i
    rw [FiniteLaw.expect_map]
    exact (μ.expect_congr_support (fun ω hω => hbit ω hω i)).trans (hm i)
  · intro i j hij
    rw [FiniteLaw.expect_map]
    have he : μ.expect (fun ω => indicator (S ω) i*indicator (S ω) j)=
        μ.expect (fun ω => Q ω i*Q ω j) := μ.expect_congr_support (fun ω hω => by rw [hbit ω hω,hbit ω hω])
    rw [he]
    exact hp i j hij

end MetricKMedian.WeightedRounding
end
end

end OAI
