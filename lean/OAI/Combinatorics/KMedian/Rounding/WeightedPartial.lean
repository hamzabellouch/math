import Mathlib
import OAI.Combinatorics.KMedian.Rounding.WeightedRounding
import OAI.Combinatorics.KMedian.Probability.SumLaws

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding
open MarginalRounding
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_partial_law (p β : I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hβ : ∀ i, 0 < β i) :
    ∃ (Ω : Type) (inst : Fintype Ω), letI := inst;
      ∃ (μ : FiniteLaw Ω) (Q : Ω → I → ℝ),
        (∀ ω, 0 < μ.weight ω →
          (∀ i, 0 ≤ Q ω i) ∧ (∀ i, Q ω i ≤ 1) ∧
          (fractional (Q ω)).card ≤ 1 ∧ (∑ i, β i*Q ω i)=∑ i, β i*p i) ∧
        (∀ i, μ.expect (fun ω => Q ω i)=p i) ∧
        (∀ i j, i ≠ j → μ.expect (fun ω => Q ω i*Q ω j) ≤ p i*p j) := by
  classical
  suffices h : ∀ n : ℕ, ∀ p : I → ℝ, (fractional p).card=n →
      (∀ i, 0 ≤ p i) → (∀ i, p i ≤ 1) →
      ∃ (Ω : Type) (inst : Fintype Ω), letI := inst;
        ∃ (μ : FiniteLaw Ω) (Q : Ω → I → ℝ),
          (∀ ω, 0 < μ.weight ω →
            (∀ i, 0 ≤ Q ω i) ∧ (∀ i, Q ω i ≤ 1) ∧
            (fractional (Q ω)).card ≤ 1 ∧ (∑ i, β i*Q ω i)=∑ i, β i*p i) ∧
          (∀ i, μ.expect (fun ω => Q ω i)=p i) ∧
          (∀ i j, i ≠ j → μ.expect (fun ω => Q ω i*Q ω j) ≤ p i*p j) by
    exact h _ p rfl hp0 hp1
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hn hp0 hp1
    by_cases hsmall : (fractional p).card ≤ 1
    · refine ⟨PUnit, inferInstance, FiniteLaw.dirac PUnit.unit, fun _ => p, ?_, ?_, ?_⟩
      · exact fun _ _ => ⟨hp0, hp1, hsmall, rfl⟩
      · intro i; exact FiniteLaw.expect_dirac _ _
      · intro i j _; exact le_of_eq (FiniteLaw.expect_dirac _ _)
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (lt_of_not_ge hsmall)
    let r : ℝ := β i/β j
    have hr : 0 < r := div_pos (hβ i) (hβ j)
    let u := up p i j r
    let d := down p i j r
    have hu : 0 < u := up_pos hr hi hj
    have hd : 0 < d := down_pos hr hi hj
    have bud := move_bounds hp0 hp1 hij hr (show -d ≤ u by linarith) (le_refl u)
    have bdd := move_bounds hp0 hp1 hij hr (le_refl (-d)) (show -d ≤ u by linarith)
    obtain ⟨Ω, instΩ, hexμ⟩ := ih _ (hn ▸ up_smaller hr hij hi hj) (move p i j r u) rfl bud.1 bud.2
    let := instΩ
    obtain ⟨μ, Q, hsμ, hmμ, hpμ⟩ := hexμ
    obtain ⟨Ξ, instΞ, hexν⟩ := ih _ (hn ▸ down_smaller hr hij hi hj) (move p i j r (-d)) rfl bdd.1 bdd.2
    let := instΞ
    obtain ⟨ν, R, hsν, hmν, hpν⟩ := hexν
    let θ : ℝ := d/(u+d)
    have hθ0 : 0 ≤ θ := (div_pos hd (add_pos hu hd)).le
    have hθ1 : θ ≤ 1 := (div_le_one (add_pos hu hd)).mpr (by linarith)
    have hwμ : (∑ k, β k*move p i j r u k)=∑ k, β k*p k := weighted_sum β p (ne_of_gt (hβ j)) u
    have hwν : (∑ k, β k*move p i j r (-d) k)=∑ k, β k*p k := weighted_sum β p (ne_of_gt (hβ j)) (-d)
    refine ⟨Ω ⊕ Ξ, inferInstance, FiniteLaw.sumMix θ hθ0 hθ1 μ ν, Sum.elim Q R, ?_, ?_, ?_⟩
    · apply FiniteLaw.property_sumMix θ hθ0 hθ1 μ ν
      · intro ω hω
        simpa only [Sum.elim_inl, hwμ] using hsμ ω hω
      · intro ξ hξ
        simpa only [Sum.elim_inr, hwν] using hsν ξ hξ
    · intro k
      rw [FiniteLaw.expect_sumMix]
      simp only [Sum.elim_inl, Sum.elim_inr, hmμ, hmν]
      exact endpoint_mean p i j k r hu hd
    · intro k l hkl
      rw [FiniteLaw.expect_sumMix]
      simp only [Sum.elim_inl, Sum.elim_inr]
      calc
        _ ≤ θ*(move p i j r u k*move p i j r u l)+
            (1-θ)*(move p i j r (-d) k*move p i j r (-d) l) :=
          add_le_add (mul_le_mul_of_nonneg_left (hpμ k l hkl) hθ0)
            (mul_le_mul_of_nonneg_left (hpν k l hkl) (sub_nonneg.mpr hθ1))
        _ ≤ p k*p l := endpoint_pair p i j hkl hr.le hu hd

end MetricKMedian.WeightedRounding
end
end

end OAI
