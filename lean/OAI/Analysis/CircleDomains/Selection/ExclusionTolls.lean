import OAI.Analysis.CircleDomains.Modulus.InteriorPhysicalCost

namespace OAI

/-! Infinite auxiliary tolls enforce avoidance without changing the cost
of the original paths. They are used only inside the collar construction. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {T X Y : Type*}

def exclusionToll (S : Set X) (m : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  if x ∈ S then ∞ else m x

theorem le_exclusionToll (S : Set X) (m : X → ℝ≥0∞) : m ≤ exclusionToll S m := by
  intro x
  by_cases hx : x ∈ S <;> simp [exclusionToll, hx]

theorem exclusionToll_eq (S : Set X) (m : X → ℝ≥0∞) {x : X} (hx : x ∉ S) :
    exclusionToll S m x = m x := by
  simp [exclusionToll, hx]

theorem timeToll_mono_weight (γ : T → X) (A : Set T) {m n : X → ℝ≥0∞} (h : m ≤ n) :
    timeToll γ A m ≤ timeToll γ A n :=
  ENNReal.tsum_le_tsum (fun t => h (γ t))

theorem avoids_of_finite_exclusionToll (γ : T → X) (A : Set T)
    (S : Set X) (m : X → ℝ≥0∞) (h : timeToll γ A (exclusionToll S m) < ∞) :
    ∀t ∈ A, γ t ∉ S := by
  intro t ht hs
  have hb : exclusionToll S m (γ t) ≤ timeToll γ A (exclusionToll S m) :=
    ENNReal.le_tsum (f := fun u : A => exclusionToll S m (γ u)) ⟨t, ht⟩
  simpa [exclusionToll, hs] using hb.trans_lt h

variable [MetricSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem physicalTollCost_exclusion (d : PathCodeData X Y)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (S : Set X)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) (h : ∀t, γ.val t ∉ S) :
    physicalTollCost d g (exclusionToll S m) γ = physicalTollCost d g m γ := by
  unfold physicalTollCost boundaryToll
  congr 1
  exact tsum_congr (fun t => exclusionToll_eq S m (h t))

theorem interiorPhysicalTollCost_mono_weight (d : PathCodeData X Y)
    (g : Y → ℝ≥0∞) {m n : X → ℝ≥0∞} (h : m ≤ n)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) :
    interiorPhysicalTollCost d g m γ ≤ interiorPhysicalTollCost d g n γ :=
  add_le_add le_rfl (timeToll_mono_weight γ.val _ h)

end CircleDomainRigidity

end

end OAI
