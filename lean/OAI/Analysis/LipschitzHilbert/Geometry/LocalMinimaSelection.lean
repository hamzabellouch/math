import OAI.Analysis.LipschitzHilbert.Estimates.FirstArrival
import OAI.Analysis.LipschitzHilbert.Estimates.OrderDistribution
import OAI.Analysis.LipschitzHilbert.Phase.PhaseSelection

namespace OAI

/-! Weighted independent-set selection by local minima of a size-biased order. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def closedNeighborhood (G : ι → ι → Prop) (i : ι) : Finset ι :=
  Finset.univ.filter (fun j => j = i ∨ G i j)

theorem mem_closedNeighborhood (G : ι → ι → Prop) (i j : ι) :
    j ∈ closedNeighborhood G i ↔ j = i ∨ G i j := by
  simp [closedNeighborhood]

def localMinima (G : ι → ι → Prop) (l : List ι) : Finset ι :=
  Finset.univ.filter (fun i => firstFrom (closedNeighborhood G i) l = some i)

omit [Fintype ι] in
theorem firstFrom_incompatible (S T : Finset ι) (i j : ι)
    (hiT : i ∈ T) (hjS : j ∈ S) (hij : i ≠ j) (l : List ι)
    (hS : firstFrom S l = some i) (hT : firstFrom T l = some j) : False := by
  induction l with
  | nil => simp [firstFrom] at hS
  | cons k l ih =>
    by_cases hkS : k ∈ S
    · have hki : k = i := by simpa [firstFrom, hkS] using hS
      subst k
      have hij' : i = j := by simpa [firstFrom, hiT] using hT
      exact hij hij'
    · by_cases hkT : k ∈ T
      · have hkj : k = j := by simpa [firstFrom, hkT] using hT
        subst k
        exact hkS hjS
      · apply ih
        · simpa [firstFrom, hkS] using hS
        · simpa [firstFrom, hkT] using hT

theorem localMinima_independent (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i) (l : List ι) :
    (localMinima G l : Set ι).Pairwise (fun i j => ¬G i j) := by
  intro i hi j hj hij hijG
  exact firstFrom_incompatible (closedNeighborhood G i) (closedNeighborhood G j) i j
    ((mem_closedNeighborhood G j i).2 (Or.inr (hG hijG)))
    ((mem_closedNeighborhood G i j).2 (Or.inr hijG)) hij l
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

abbrev IndependentSelection (G : ι → ι → Prop) :=
  {s : Finset ι // (s : Set ι).Pairwise (fun i j => ¬G i j)}

def localMinimaOutcome (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i) (l : List ι) :
    IndependentSelection G := ⟨localMinima G l, localMinima_independent G hG l⟩

def localMinimaLaw (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    PhaseCombinatorics.FiniteSelectionLaw (IndependentSelection G) ι where
  weight := orderOutcomeWeight w Finset.univ (localMinimaOutcome G hG)
  nonnegative := orderOutcomeWeight_nonnegative w Finset.univ (fun i _ => hw i) _
  total := orderOutcomeWeight_total w Finset.univ (fun i _ => hw i) _
  retained := Subtype.val

theorem localMinimaLaw_independent (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (ω : IndependentSelection G) :
    ((localMinimaLaw G hG w hw).retained ω : Set ι).Pairwise (fun i j => ¬G i j) := ω.property

theorem localMinimaLaw_marginal (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (i : ι) :
    (localMinimaLaw G hG w hw).marginal i = w i / orderMass w (closedNeighborhood G i) := by
  have hevent := orderOutcomeWeight_event w Finset.univ (fun j _ => hw j)
    (localMinimaOutcome G hG) (fun s => i ∈ s.val)
  have heq : (fun l => if i ∈ (localMinimaOutcome G hG l).val then (1 : ℝ) else 0) =
      arrivalEvent (closedNeighborhood G i) i := by
    funext l
    simp [localMinimaOutcome, localMinima, arrivalEvent]
  rw [heq] at hevent
  have hfirst := orderAverage_arrivalEvent w Finset.univ (closedNeighborhood G i) i
    (fun j _ => hw j) (Finset.subset_univ _)
    ((mem_closedNeighborhood G i i).2 (Or.inl rfl))
  have hsum : (localMinimaLaw G hG w hw).marginal i =
      ∑ a : IndependentSelection G, if i ∈ a.val then
        orderOutcomeWeight w Finset.univ (localMinimaOutcome G hG) a else 0 := by
    unfold PhaseCombinatorics.FiniteSelectionLaw.marginal
    apply Finset.sum_congr rfl
    intro a _
    by_cases hi : i ∈ a.val <;> simp [localMinimaLaw, hi]
  exact hsum.trans (hevent.trans hfirst)

theorem localMinimaLaw_marginal_pos (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (i : ι) :
    0 < (localMinimaLaw G hG w hw).marginal i := by
  rw [localMinimaLaw_marginal]
  exact div_pos (hw i) (orderMass_pos w _ (fun j _ => hw j)
    ⟨i, (mem_closedNeighborhood G i i).2 (Or.inl rfl)⟩)

theorem localMinimaLaw_marginal_lower (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ι → ℝ)
    (hm : ∀ i, orderMass w (closedNeighborhood G i) ≤ m i) (i : ι) :
    w i / m i ≤ (localMinimaLaw G hG w hw).marginal i := by
  rw [localMinimaLaw_marginal]
  exact div_le_div_of_nonneg_left (hw i).le
    (orderMass_pos w _ (fun j _ => hw j)
      ⟨i, (mem_closedNeighborhood G i i).2 (Or.inl rfl)⟩) (hm i)

end LipschitzHilbert

end

end OAI
