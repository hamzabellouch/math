import Mathlib

namespace OAI

/-! Basic. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open scoped BigOperators ENNReal NNReal
open Filter

namespace ThreeState.TreeClauses

abbrev Spin := Fin 3

def Admissible (lam : ℝ) : Prop := -(1 / 2 : ℝ) ≤ lam ∧ lam ≤ 1

def channelWeight (lam : ℝ) (i j : Spin) : ℝ :=
  if i = j then (1 + 2 * lam) / 3 else (1 - lam) / 3

lemma channelWeight_nonneg {lam : ℝ} (hlam : Admissible lam) (i j : Spin) :
    0 ≤ channelWeight lam i j := by
  unfold channelWeight
  split_ifs <;> dsimp [Admissible] at hlam <;> linarith [hlam.1, hlam.2]

lemma channelWeight_sum (lam : ℝ) (i : Spin) : ∑ j, channelWeight lam i j = 1 := by
  fin_cases i <;> simp [channelWeight, Fin.sum_univ_three] <;> ring

def channel (lam : ℝ) (hlam : Admissible lam) (i : Spin) : PMF Spin :=
  PMF.ofFintype (fun j ↦ ENNReal.ofReal (channelWeight lam i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ channelWeight_nonneg hlam i j),
      channelWeight_sum]
    norm_num)

def Observation : ℕ → Type
  | 0 => Spin
  | n + 1 => Multiset (Observation n)

def iidList {α : Type} (p : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | n + 1 => p.bind fun x ↦ (iidList p n).map (List.cons x)

def observationLaw (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) :
    (ℓ : ℕ) → Spin → PMF (Observation ℓ)
  | 0, i => PMF.pure i
  | ℓ + 1, i => offspring.bind fun n ↦
      (iidList ((channel lam hlam i).bind (observationLaw lam hlam offspring ℓ)) n).map
        (fun xs ↦ (xs : Multiset (Observation ℓ)))

def jointWeight (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (i : Spin) (o : Observation ℓ) : ℝ≥0∞ :=
  (1 / 3 : ℝ≥0∞) * observationLaw lam hlam offspring ℓ i o

def marginalWeight (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (o : Observation ℓ) : ℝ≥0∞ :=
  ∑ i, jointWeight lam hlam offspring ℓ i o

def posterior (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (o : Observation ℓ) (i : Spin) : ℝ :=
  (jointWeight lam hlam offspring ℓ i o / marginalWeight lam hlam offspring ℓ o).toReal

def advantage (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) (ℓ : ℕ) : ℝ :=
  ∑' o : Observation ℓ, (marginalWeight lam hlam offspring ℓ o).toReal *
    ((∑ i : Spin, |posterior lam hlam offspring ℓ o i - (1 / 3 : ℝ)|) / 2)

def Reconstructs (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ Tendsto (advantage lam hlam offspring) atTop (nhds a)

def ThresholdAt (d lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) : Prop :=
  (Reconstructs lam hlam offspring ↔ 1 < d * lam ^ 2) ∧
  (d * lam ^ 2 ≤ 1 → Tendsto (advantage lam hlam offspring) atTop (nhds 0))

def ExactThreshold : Prop :=
  (∀ (b : ℕ), 2 ≤ b → ∀ (lam : ℝ) (hlam : Admissible lam),
    ThresholdAt (b : ℝ) lam hlam (PMF.pure b)) ∧
  (∀ (d : ℝ) (hd : 1 < d) (lam : ℝ) (hlam : Admissible lam),
    ThresholdAt d lam hlam (by
      let rate : ℝ≥0 := ⟨d, le_trans (by norm_num) hd.le⟩
      haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.poissonMeasure rate) :=
        (ProbabilityTheory.hasSum_one_poissonMeasure rate).isProbabilityMeasure_sum_dirac
          (fun _ ↦ by positivity)
      exact (ProbabilityTheory.poissonMeasure rate).toPMF))

end ThreeState.TreeClauses

end

end OAI
