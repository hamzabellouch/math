import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Counts
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Priority
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Bounds
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.PopulationRates

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldActiveLaws

open AllFieldParameters AllFieldHistory MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

def branchProbability {K : ℕ} (w : Work K) (b : w.Branch) : ℚ :=
  match w with
  | .stageA h => stageALaw (initialShape h.val) (aSplit ⟨h, b, false⟩)
  | .stageB h => stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩)
  | .stageC h => stageCWeight (cParameterParent h) (cShapeParent h) b

theorem branchProbability_nonneg {K : ℕ} (w : Work K) (b : w.Branch) :
    0 ≤ branchProbability w b := by
  cases w with
  | stageA h => exact (stageALaw_positive _ _ (aSplit_mem ⟨h, b, false⟩)).le
  | stageB h => exact (stageBLaw_positive _ _ (bSplit_mem ⟨h, b, false⟩)).le
  | stageC h => exact stageCWeight_nonnegative _ _ b

theorem branchProbability_total {K : ℕ} (w : Work K) :
    ∑ b : w.Branch, branchProbability w b = 1 := by
  cases w with
  | stageA h =>
      change (∑ b : ASplit h,
        stageALaw (initialShape h.val) (below (initialShape h.val))[b.val]) = 1
      rw [Fin.sum_univ_fun_getElem]
      exact stageALaw_normalized _ h.property
  | stageB h =>
      change (∑ b : BSplit h,
        stageBLaw (aShape h.val) (below (aShape h.val))[b.val]) = 1
      rw [Fin.sum_univ_fun_getElem]
      exact stageBLaw_normalized _ h.property
  | stageC h => exact stageCWeight_normalized _ _

def branchLaw {K : ℕ} (w : Work K) : FiniteLaw w.Branch where
  mass b := (branchProbability w b : ℝ)
  nonneg b := by exact_mod_cast branchProbability_nonneg w b
  total := by exact_mod_cast branchProbability_total w

@[simp] theorem branchLaw_mass {K : ℕ} (w : Work K) (b : w.Branch) :
    (branchLaw w).mass b = (branchProbability w b : ℝ) := rfl

def placedLaw {K : ℕ} (w : PlacedWork K) : FiniteLaw JointPopulation.Shape :=
  (branchLaw w.1).map (branchShape w)

@[simp] theorem placedLaw_mass {K : ℕ} (w : PlacedWork K)
    (u : JointPopulation.Shape) :
    (placedLaw w).mass u =
      ∑ b : w.1.Branch, if branchShape w b = u then
        (branchProbability w.1 b : ℝ) else 0 := by
  simp only [placedLaw, FiniteLaw.map_mass, branchLaw_mass]

theorem placedLaw_mass_branch {K : ℕ} (w : PlacedWork K) (b : w.1.Branch) :
    (placedLaw w).mass (branchShape w b) = (branchProbability w.1 b : ℝ) :=
  FiniteLaw.map_mass_apply _ _ (branchShape_injective w) b

theorem placedLaw_entropy {K : ℕ} (w : PlacedWork K) :
    finiteEntropy (placedLaw w).mass = finiteEntropy (branchLaw w.1).mass :=
  FiniteLaw.map_entropy_of_injective _ _ (branchShape_injective w)

theorem placedLaw_sideMass {K : ℕ} (w : PlacedWork K) (s : Fin 3)
    (k : Fin 17) :
    JointPopulationRates.sideMass (placedLaw w).mass s k =
      ∑ b : w.1.Branch, if JointPopulation.shapeSide s (branchShape w b) = k
        then (branchProbability w.1 b : ℝ) else 0 := by
  unfold JointPopulationRates.sideMass
  simp only [placedLaw_mass]
  calc
    _ = ∑ u : JointPopulation.Shape, ∑ b : w.1.Branch,
        if branchShape w b = u then
          if JointPopulation.shapeSide s u = k then (branchProbability w.1 b : ℝ) else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : JointPopulation.shapeSide s u = k <;> simp [hu]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem branchPopulation_cast_rat {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    (branchPopulation allocation dilation w b : ℚ) =
      (population allocation dilation (w.1.source, w.2) : ℚ) *
        branchProbability w.1 b := by
  rcases w with ⟨w, phi⟩
  cases w <;>
    simp only [branchPopulation, Work.child, Work.source, population_cast,
      amount, canonicalAmount, aAmount, bAmount, cAmount, branchProbability] <;> ring

theorem branchPopulation_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    (branchPopulation allocation dilation w b : ℝ) =
      (population allocation dilation (w.1.source, w.2) : ℝ) *
        (branchLaw w.1).mass b := by
  rw [branchLaw_mass]
  exact_mod_cast branchPopulation_cast_rat allocation dilation w b

theorem jointCounts_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) =
      (population allocation dilation (w.1.source, w.2) : ℝ) *
        (placedLaw w).mass u := by
  simp only [jointCounts, shapeCounts, Nat.cast_sum, placedLaw_mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : branchShape w b = u
  · simp only [hb, ite_true, branchPopulation_cast, branchLaw_mass]
  · simp [hb]

theorem jointCounts_ratio {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) /
      population allocation dilation (w.1.source, w.2) = (placedLaw w).mass u := by
  rw [jointCounts_cast]
  have hp : (population allocation dilation (w.1.source, w.2) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (work_source_population_pos allocation hd w)
  exact mul_div_cancel_left₀ _ hp

theorem jointCounts_normalized {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (w : PlacedWork K) :
    (∑ u, (jointCounts allocation dilation w u : ℝ) /
      population allocation dilation (w.1.source, w.2)) = 1 := by
  simp only [jointCounts_ratio allocation hd]
  exact (placedLaw w).total

theorem population_cast_real {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : History K) :
    (population allocation dilation h : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) * (amount allocation h : ℝ) := by
  exact_mod_cast population_cast allocation dilation h

theorem jointCounts_source_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) *
        ((amount allocation (w.1.source, w.2) : ℝ) * (placedLaw w).mass u) := by
  rw [jointCounts_cast, population_cast_real, mul_assoc]

theorem jointCounts_source_ratio {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) /
      populationLength (K := K) allocation dilation =
        (amount allocation (w.1.source, w.2) : ℝ) * (placedLaw w).mass u := by
  rw [jointCounts_source_cast]
  have hp : (populationLength (K := K) allocation dilation : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (AllFieldPopulationCounts.blockLength_pos (amount (K := K) allocation) hd)
  exact mul_div_cancel_left₀ _ hp

theorem jointCounts_source_rate {K : ℕ} (allocation : Allocation)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    Tendsto (fun dilation : ℕ => (jointCounts allocation dilation w u : ℝ) /
      populationLength (K := K) allocation dilation) atTop
      (𝓝 ((amount allocation (w.1.source, w.2) : ℝ) * (placedLaw w).mass u)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with dilation hd
  exact (jointCounts_source_ratio allocation hd w u).symm

theorem populationLength_dilation {K : ℕ} (allocation : Allocation) (dilation : ℕ) :
    populationLength (K := K) allocation dilation =
      dilation * populationLength (K := K) allocation 1 := by
  simp only [populationLength, AllFieldPopulationCounts.blockLength, one_mul]

theorem jointCounts_dilation_ratio {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) / (dilation : ℝ) =
      ((populationLength (K := K) allocation 1 : ℝ) *
        (amount allocation (w.1.source, w.2) : ℝ)) * (placedLaw w).mass u := by
  rw [jointCounts_source_cast, populationLength_dilation, Nat.cast_mul]
  have hd' : (dilation : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  field_simp [hd']

theorem jointCounts_dilation_rate {K : ℕ} (allocation : Allocation)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    Tendsto (fun dilation : ℕ => (jointCounts allocation dilation w u : ℝ) /
      (dilation : ℝ)) atTop
      (𝓝 (((populationLength (K := K) allocation 1 : ℝ) *
        (amount allocation (w.1.source, w.2) : ℝ)) * (placedLaw w).mass u)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with dilation hd
  exact (jointCounts_dilation_ratio allocation hd w u).symm

def orderLaw {K tick : ℕ} {sigma : Placement} (h : ActiveOrder K tick sigma) :
    FiniteLaw JointPopulation.Shape := placedLaw h.val.val

def orderMass {K tick : ℕ} {sigma : Placement} (allocation : Allocation)
    (h : ActiveOrder K tick sigma) : ℝ :=
  amount allocation (h.val.val.1.source, h.val.val.2)

def orderCounts {K tick : ℕ} {sigma : Placement} (allocation : Allocation)
    (dilation : ℕ) (h : ActiveOrder K tick sigma) : JointPopulation.Shape → ℕ :=
  activeCounts allocation dilation h.val

theorem orderMass_nonneg {K tick : ℕ} {sigma : Placement} (allocation : Allocation)
    (h : ActiveOrder K tick sigma) : 0 ≤ orderMass allocation h := by
  unfold orderMass
  exact_mod_cast amount_nonneg allocation (h.val.val.1.source, h.val.val.2)

theorem orderCounts_source_cast {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (dilation : ℕ) (h : ActiveOrder K tick sigma)
    (u : JointPopulation.Shape) :
    (orderCounts allocation dilation h u : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) *
        (orderMass allocation h * (orderLaw h).mass u) :=
  jointCounts_source_cast allocation dilation h.val.val u

theorem orderCounts_source_rate {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape) :
    Tendsto (fun dilation : ℕ => (orderCounts allocation dilation h u : ℝ) /
      populationLength (K := K) allocation dilation) atTop
      (𝓝 (orderMass allocation h * (orderLaw h).mass u)) :=
  jointCounts_source_rate allocation h.val.val u

theorem orderCounts_dilation_rate {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape) :
    Tendsto (fun dilation : ℕ => (orderCounts allocation dilation h u : ℝ) /
      (dilation : ℝ)) atTop
      (𝓝 (((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
        (orderLaw h).mass u)) :=
  jointCounts_dilation_rate allocation h.val.val u

end MatrixMultiplication.AllFieldActiveLaws

end

end OAI
