import OAI.Probability.SwitchChain.Definitions
import OAI.Probability.SwitchChain.InitialTV

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315

theorem tvDistanceFrom_zero_eq (n : Nat) (d : Fin n → Nat) (G : GraphState n d) :
    tvDistanceFrom n d 0 G = 1 - 1 / (stateCount n d : ℝ) := by
  classical
  have hid : tvDistanceFrom n d 0 G = Problem315Aux.deltaUniformTV G := by
    simp only [tvDistanceFrom, kernelPow, stateCount, allGraphStates,
      Problem315Aux.deltaUniformTV, Finset.card_univ]
    congr 1
    apply Finset.sum_congr rfl
    intro H _
    by_cases heq : G = H <;> simp [heq]
  rw [hid, Problem315Aux.deltaUniformTV_eq]
  rfl

theorem mixedAt_zero_of_stateCount_one (n : Nat) (d : Fin n → Nat)
    (hc : stateCount n d = 1) : MixedAt n d 0 := by
  intro G
  rw [tvDistanceFrom_zero_eq, hc]
  norm_num

theorem mixingTime_zero_of_mixedAt_zero (n : Nat) (d : Fin n → Nat)
    (hzero : MixedAt n d 0) (h : ∃ t : Nat, MixedAt n d t) :
    mixingTime n d h = 0 := by
  classical
  exact Nat.eq_zero_of_le_zero (Nat.find_min' h hzero)

theorem singleton_mixing_conclusion (n : Nat) (d : Fin n → Nat)
    (hc : stateCount n d = 1) :
    MixedAt n d 0 ∧ ∀ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h = 0 := by
  have hzero := mixedAt_zero_of_stateCount_one n d hc
  exact ⟨hzero, mixingTime_zero_of_mixedAt_zero n d hzero⟩

theorem mixedAt_zero_iff_stateCount_le_one (n : Nat) (d : Fin n → Nat) :
    MixedAt n d 0 ↔ stateCount n d ≤ 1 := by
  classical
  constructor
  · intro hm
    by_contra hc
    have htwo : 2 ≤ stateCount n d := by omega
    have hpos : 0 < (allGraphStates n d).card := by
      change 0 < stateCount n d
      omega
    obtain ⟨G, _⟩ := Finset.card_pos.mp hpos
    have htwoR : (2 : ℝ) ≤ stateCount n d := by exact_mod_cast htwo
    have hinv : (1 : ℝ) / stateCount n d ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) htwoR
    have hG := hm G
    rw [tvDistanceFrom_zero_eq] at hG
    linarith
  · intro hc G
    have : Nonempty (GraphState n d) := ⟨G⟩
    have hpos : 0 < stateCount n d := by
      simpa [stateCount, allGraphStates] using
        (Fintype.card_pos (α := GraphState n d))
    have hone : stateCount n d = 1 := by omega
    exact mixedAt_zero_of_stateCount_one n d hone G

end Problem315

end

end OAI
