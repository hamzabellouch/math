import OAI.Analysis.MarkovType.ChartAveraging
import OAI.Analysis.MarkovType.ChartTransport
import OAI.Analysis.MarkovType.MarkedLetters

namespace OAI

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

universe u

theorem exists_chart_transport {L : Type u} [Fintype L] [Nonempty L]
    (Λ : Finset ℝ) (ε : ℝ) (hε : 0 < ε)
    (inv : L → L) (hinv : Function.Involutive inv)
    (h : L → ℝ ≃o ℝ) (hh : ∀ s, h (inv s) = (h s).symm) :
    ∃ (B : ℕ) (ν : FiniteLaw (Chart Λ B)),
      1 - ε ≤ ∑ e : UniformCouplingEdge (PositiveMassSupport ν) L,
        if Chart.Good (h e.2.1) e.1.val e.2.2.val then
          (chartTransportChain ν inv hinv h).π e.1 *
            (chartTransportChain ν inv hinv h).q e else 0 := by
  obtain ⟨B, weights, hnonneg, hsum, havg⟩ := exists_chart_averaging Λ ε hε
  let ν : FiniteLaw (Chart Λ B) := ⟨weights, hnonneg, hsum⟩
  refine ⟨B, ν, chartTransportChain_good_mass ν inv hinv h hh ?_⟩
  intro s
  exact havg (chartTransportDomain Λ (h s)).card
    (chartTransportSourceTuple Λ (h s)) (chartTransportTargetTuple Λ (h s))

theorem chartTransportChain_uniform_letters {Λ : Finset ℝ} {B : ℕ} {L : Type u}
    [Fintype L] [Nonempty L] (ν : FiniteLaw (Chart Λ B))
    (inv : L → L) (hinv : Function.Involutive inv) (h : L → ℝ ≃o ℝ)
    (n : ℕ) (F : (Fin n → L) → ℝ) :
    markedExpect (chartTransportChain ν inv hinv h) n
      (fun ω => F (fun i => (ω.2 i).2.1)) =
        ((Fintype.card L : ℝ)⁻¹) ^ n * ∑ w : Fin n → L, F w := by
  apply markedExpect_uniform_letters (chartTransportChain ν inv hinv h)
    (fun e => e.2.1)
  intro C s
  refine Eq.trans ?_ (chartTransportChain_marked_letter_mass ν inv hinv h C s)
  apply Finset.sum_congr rfl
  intro e _
  have hsrc : (chartTransportChain ν inv hinv h).src e = e.1 := rfl
  by_cases hevent : e.1 = C ∧ e.2.1 = s
  · simp only [hsrc, ite_eq_left hevent]
  · simp only [hsrc, ite_eq_right hevent]

theorem chartTransportChain_word_probability {Λ : Finset ℝ} {B : ℕ} {L : Type u}
    [Fintype L] [Nonempty L] (ν : FiniteLaw (Chart Λ B))
    (inv : L → L) (hinv : Function.Involutive inv) (h : L → ℝ ≃o ℝ)
    (n : ℕ) (w : Fin n → L) :
    markedProb (chartTransportChain ν inv hinv h) n
      (fun ω => (fun i => (ω.2 i).2.1) = w) = ((Fintype.card L : ℝ)⁻¹) ^ n := by
  have hi := chartTransportChain_uniform_letters ν inv hinv h n
    (fun v => if v = w then 1 else 0)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one] at hi
  refine Eq.trans ?_ hi
  unfold markedProb markedExpect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hevent : (fun i => (ω.2 i).2.1) = w
  · simp only [ite_eq_left hevent, mul_one]
  · simp only [ite_eq_right hevent, mul_zero]

end MarkovSuperreflexivity

end

end OAI
