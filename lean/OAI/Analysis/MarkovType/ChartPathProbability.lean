import OAI.Analysis.MarkovType.ChartChain
import OAI.Analysis.MarkovType.MarkedPaths
import OAI.Analysis.MarkovType.MarkedLetters
import OAI.Analysis.MarkovType.PeriodicArcs
import OAI.Analysis.MarkovType.WalkParameters
import OAI.Analysis.MarkovType.WalkDrift

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity.FiniteWalkDrift

variable {S E : Type*} [Fintype S] [Fintype E]

theorem markedPath_eventMass_edge (C : FiniteMarkedChain S E) (n : ℕ)
    (i : Fin n) (Q : E → Prop) :
    eventMass (markedPathWeight C n) (fun ω => Q (ω.2 i)) =
      ∑ e, if Q e then C.π (C.src e) * C.q e else 0 := by
  classical
  have h := markedExpect_edge C n i (fun e => if Q e then (1 : ℝ) else 0)
  simpa only [markedExpect, eventMass, mul_ite, mul_one, mul_zero] using h

theorem markedStationaryEdgeMass_sum (C : FiniteMarkedChain S E) :
    (∑ e, C.π (C.src e) * C.q e) = 1 := by
  have h := markedExpect_edge C 1 (0 : Fin 1) (fun _ => (1 : ℝ))
  simpa only [markedExpect, mul_one, sum_markedPathWeight] using h.symm

theorem markedPath_bad_step_mass_le (C : FiniteMarkedChain S E) (n : ℕ)
    (i : Fin n) (Q : E → Prop) (ε : ℝ)
    (hgood : 1 - ε ≤ ∑ e, if Q e then C.π (C.src e) * C.q e else 0) :
    eventMass (markedPathWeight C n) (fun ω => ¬ Q (ω.2 i)) ≤ ε := by
  classical
  rw [markedPath_eventMass_edge C n i (fun e => ¬ Q e)]
  have hsplit :
      (∑ e, if Q e then C.π (C.src e) * C.q e else 0) +
      (∑ e, @ite ℝ (¬ Q e) (Classical.propDecidable (¬ Q e))
        (C.π (C.src e) * C.q e) 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ e, C.π (C.src e) * C.q e := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : Q e <;> simp [he]
      _ = 1 := markedStationaryEdgeMass_sum C
  linarith

theorem markedProb_valid_and (C : FiniteMarkedChain S E) (n : ℕ)
    (Q : MarkedPath S E n → Prop) :
    markedProb C n (fun ω => markedValid C ω ∧ Q ω) = markedProb C n Q := by
  classical
  unfold markedProb
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hv : markedValid C ω
  · simp [hv]
  · rw [markedPathWeight_eq_zero_of_not_valid C ω hv]
    simp

variable {Λ : Finset ℝ} {B : ℕ}

abbrev ConcreteChartState (ν : FiniteLaw (Chart Λ B)) := PositiveMassSupport ν

abbrev ConcreteChartEdge (ν : FiniteLaw (Chart Λ B)) :=
  UniformCouplingEdge (ConcreteChartState ν) Letter

def concreteChartChain (ν : FiniteLaw (Chart Λ B)) :
    FiniteMarkedChain (ConcreteChartState ν) (ConcreteChartEdge ν) :=
  chartTransportChain ν Letter.inv Letter.inv_inv letterOrderIso

def concreteChartGood {ν : FiniteLaw (Chart Λ B)} (e : ConcreteChartEdge ν) : Prop :=
  Chart.Good (letterOrderIso e.2.1) e.1.val e.2.2.val

def concreteChartGoodMass (ν : FiniteLaw (Chart Λ B)) : ℝ :=
  ∑ e : ConcreteChartEdge ν, if concreteChartGood e then
    (concreteChartChain ν).π e.1 * (concreteChartChain ν).q e else 0

def concreteChartPathLetters {ν : FiniteLaw (Chart Λ B)} {n : ℕ}
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n) : Fin n → Letter :=
  fun i => (ω.2 i).2.1

def concreteChartTVBound (ν : FiniteLaw (Chart Λ B)) (ε : ℝ) : Prop :=
  ∀ s : Letter, finiteTotalVariation
    (finitePushforward ν.mass
      (fun C => (chartTransportSourceTuple Λ (letterOrderIso s)).trans C))
    (finitePushforward ν.mass
      (fun C => (chartTransportTargetTuple Λ (letterOrderIso s)).trans C)) < ε

theorem concreteChartPath_uniform_letters (ν : FiniteLaw (Chart Λ B)) (n : ℕ)
    (F : (Fin n → Letter) → ℝ) :
    (∑ ω, markedPathWeight (concreteChartChain ν) n ω *
      F (concreteChartPathLetters ω)) =
        ((Fintype.card Letter : ℝ)⁻¹) ^ n * ∑ w, F w := by
  unfold concreteChartChain concreteChartPathLetters
  simpa only [markedExpect] using
    chartTransportChain_uniform_letters ν Letter.inv Letter.inv_inv letterOrderIso n F

theorem concreteChartPath_word_mass (ν : FiniteLaw (Chart Λ B)) (n : ℕ)
    (w : Fin n → Letter) :
    markedProb (concreteChartChain ν) n
      (fun ω => concreteChartPathLetters ω = w) = ((4 : ℝ)⁻¹) ^ n := by
  unfold concreteChartChain concreteChartPathLetters
  simpa only [card_letter, Nat.cast_ofNat] using
    chartTransportChain_word_probability ν Letter.inv Letter.inv_inv letterOrderIso n w

theorem concreteChartPath_bad_step_of_good_mass (ν : FiniteLaw (Chart Λ B))
    (n : ℕ) (i : Fin n) (ε : ℝ) (hgood : 1 - ε ≤ concreteChartGoodMass ν) :
    eventMass (markedPathWeight (concreteChartChain ν) n)
      (fun ω => ¬ concreteChartGood (ω.2 i)) ≤ ε := by
  exact markedPath_bad_step_mass_le (concreteChartChain ν) n i concreteChartGood ε hgood

theorem concreteChartPath_bad_step (ν : FiniteLaw (Chart Λ B)) (n : ℕ)
    (i : Fin n) (ε : ℝ) (hTV : concreteChartTVBound ν ε) :
    eventMass (markedPathWeight (concreteChartChain ν) n)
      (fun ω => ¬ concreteChartGood (ω.2 i)) ≤ ε := by
  apply markedPath_bad_step_mass_le (concreteChartChain ν) n i
    concreteChartGood ε
  exact chartTransportChain_good_mass ν Letter.inv Letter.inv_inv letterOrderIso
    letterOrderIso_inv hTV

theorem concreteChartPath_bad_union (ν : FiniteLaw (Chart Λ B)) (n : ℕ)
    (ε : ℝ) (hTV : concreteChartTVBound ν ε) :
    markedProb (concreteChartChain ν) n
      (fun ω => ∃ i : Fin n, ¬ concreteChartGood (ω.2 i)) ≤ (n : ℝ) * ε := by
  change eventMass (markedPathWeight (concreteChartChain ν) n)
    (fun ω => ∃ i : Fin n, ¬ concreteChartGood (ω.2 i)) ≤ _
  calc
    _ ≤ ∑ i : Fin n, eventMass (markedPathWeight (concreteChartChain ν) n)
        (fun ω => ¬ concreteChartGood (ω.2 i)) :=
      eventMass_exists_le_sum _ (markedPathWeight_nonneg (concreteChartChain ν) n) _
    _ ≤ ∑ _i : Fin n, ε :=
      Finset.sum_le_sum (fun i _ => concreteChartPath_bad_step ν n i ε hTV)
    _ = (n : ℝ) * ε := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem concreteChartPath_bad_union_tenth (ν : FiniteLaw (Chart Λ B))
    (n : ℕ) (hn : 0 < n) (hTV : concreteChartTVBound ν (walkError n)) :
    markedProb (concreteChartChain ν) n
      (fun ω => ∃ i : Fin n, ¬ concreteChartGood (ω.2 i)) ≤ (1 : ℝ) / 10 := by
  simpa only [mul_walkError hn] using
    concreteChartPath_bad_union ν n (walkError n) hTV

theorem concreteChartPath_reducedLength_mean_ge (ν : FiniteLaw (Chart Λ B)) (n : ℕ) :
    (n : ℝ) / 2 ≤ markedExpect (concreteChartChain ν) n (fun ω =>
      (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ)) := by
  exact reducedLength_weighted_mean_ge n
    (markedPathWeight (concreteChartChain ν) n) concreteChartPathLetters
    (concreteChartPath_uniform_letters ν n)

theorem concreteChartPath_tail_all_good_of_good_mass (ν : FiniteLaw (Chart Λ B))
    (n : ℕ) (hn : 0 < n) (hgood : 1 - walkError n ≤ concreteChartGoodMass ν) :
    (3 : ℝ) / 20 ≤ markedProb (concreteChartChain ν) n (fun ω =>
      (n : ℝ) / 4 ≤ (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ) ∧
      ∀ i : Fin n, concreteChartGood (ω.2 i)) := by
  classical
  have h := reducedLength_tail_all_good n hn
    (markedPathWeight (concreteChartChain ν) n)
    (markedPathWeight_nonneg (concreteChartChain ν) n)
    (sum_markedPathWeight (concreteChartChain ν) n)
    concreteChartPathLetters (concreteChartPath_uniform_letters ν n)
    (fun i ω => ¬ concreteChartGood (ω.2 i)) (by
      intro i
      exact concreteChartPath_bad_step_of_good_mass ν n i (walkError n) hgood)
  change (3 : ℝ) / 20 ≤ eventMass (markedPathWeight (concreteChartChain ν) n)
    (fun ω => (n : ℝ) / 4 ≤
      (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ) ∧
      ∀ i : Fin n, concreteChartGood (ω.2 i))
  simpa only [not_not] using h

theorem concreteChartPath_valid_tail_all_good_of_good_mass
    (ν : FiniteLaw (Chart Λ B)) (n : ℕ) (hn : 0 < n)
    (hgood : 1 - walkError n ≤ concreteChartGoodMass ν) :
    (3 : ℝ) / 20 ≤ markedProb (concreteChartChain ν) n (fun ω =>
      markedValid (concreteChartChain ν) ω ∧
      (n : ℝ) / 4 ≤ (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ) ∧
      ∀ i : Fin n, concreteChartGood (ω.2 i)) := by
  rw [markedProb_valid_and]
  exact concreteChartPath_tail_all_good_of_good_mass ν n hn hgood

theorem exists_concreteChartPath_valid_tail_all_good (Λ : Finset ℝ)
    (n : ℕ) (hn : 0 < n) :
    ∃ (B : ℕ) (ν : FiniteLaw (Chart Λ B)),
      (3 : ℝ) / 20 ≤ markedProb (concreteChartChain ν) n (fun ω =>
        markedValid (concreteChartChain ν) ω ∧
        (n : ℝ) / 4 ≤ (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ) ∧
        ∀ i : Fin n, concreteChartGood (ω.2 i)) := by
  obtain ⟨B, ν, hgood⟩ := exists_chart_transport Λ (walkError n) (walkError_pos hn)
    Letter.inv Letter.inv_inv letterOrderIso letterOrderIso_inv
  exact ⟨B, ν, concreteChartPath_valid_tail_all_good_of_good_mass ν n hn hgood⟩

theorem concreteChartPath_tail_all_good (ν : FiniteLaw (Chart Λ B))
    (n : ℕ) (hn : 0 < n) (hTV : concreteChartTVBound ν (walkError n)) :
    (3 : ℝ) / 20 ≤ markedProb (concreteChartChain ν) n (fun ω =>
      (n : ℝ) / 4 ≤ (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ) ∧
      ∀ i : Fin n, concreteChartGood (ω.2 i)) := by
  classical
  have h := reducedLength_tail_all_good n hn
    (markedPathWeight (concreteChartChain ν) n)
    (markedPathWeight_nonneg (concreteChartChain ν) n)
    (sum_markedPathWeight (concreteChartChain ν) n)
    concreteChartPathLetters (concreteChartPath_uniform_letters ν n)
    (fun i ω => ¬ concreteChartGood (ω.2 i)) (by
      intro i
      exact concreteChartPath_bad_step ν n i (walkError n) hTV)
  change (3 : ℝ) / 20 ≤ eventMass (markedPathWeight (concreteChartChain ν) n)
    (fun ω => (n : ℝ) / 4 ≤
      (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ) ∧
      ∀ i : Fin n, concreteChartGood (ω.2 i))
  simpa only [not_not] using h

theorem concreteChartPath_valid_tail_all_good (ν : FiniteLaw (Chart Λ B))
    (n : ℕ) (hn : 0 < n) (hTV : concreteChartTVBound ν (walkError n)) :
    (3 : ℝ) / 20 ≤ markedProb (concreteChartChain ν) n (fun ω =>
      markedValid (concreteChartChain ν) ω ∧
      (n : ℝ) / 4 ≤ (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ) ∧
      ∀ i : Fin n, concreteChartGood (ω.2 i)) := by
  rw [markedProb_valid_and]
  exact concreteChartPath_tail_all_good ν n hn hTV

end MarkovSuperreflexivity.FiniteWalkDrift

end

end OAI
