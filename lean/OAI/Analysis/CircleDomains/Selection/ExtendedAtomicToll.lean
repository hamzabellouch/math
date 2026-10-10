import OAI.Analysis.CircleDomains.Modulus.CostPerturbation

namespace OAI

/-! Extend a prescribed countable atomic metric by zero on the quotient.
Both its square norm and the full preterminal visit payment are preserved. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

def extendAtomicToll {D X : Type*} (p : D → X) (m : D → ℝ≥0∞) : X → ℝ≥0∞ :=
  Function.extend p m 0

theorem extendAtomicToll_apply {D X : Type*} {p : D → X}
    (hp : Injective p) (m : D → ℝ≥0∞) (s : D) :
    extendAtomicToll p m (p s) = m s := hp.extend_apply m 0 s

theorem extendAtomicToll_zero {D X : Type*} (p : D → X) (m : D → ℝ≥0∞)
    {x : X} (hx : x ∉ range p) : extendAtomicToll p m x = 0 :=
  Function.extend_apply' (f := p) m (fun _ : X => 0) x hx

theorem support_extendAtomicToll_subset {D X : Type*} (p : D → X) (m : D → ℝ≥0∞) :
    support (extendAtomicToll p m) ⊆ range p := by
  intro x hx
  by_contra h
  exact hx (extendAtomicToll_zero p m h)

theorem countingSquareNorm_extendAtomicToll {D X : Type*} {p : D → X}
    (hp : Injective p) (m : D → ℝ≥0∞) :
    countingSquareNorm (extendAtomicToll p m) = countingSquareNorm m := by
  unfold countingSquareNorm
  congr 1
  calc
    (∑'x, extendAtomicToll p m x ^ 2) = ∑'s, extendAtomicToll p m (p s) ^ 2 := by
      symm
      apply hp.tsum_eq (f := fun x : X => extendAtomicToll p m x ^ 2)
      intro x hx
      by_contra h
      exact hx (by
        change extendAtomicToll p m x ^ 2 = 0
        rw [extendAtomicToll_zero p m h, zero_pow (by decide)])
    _ = _ := by simp only [extendAtomicToll_apply hp]

theorem preterminalToll_extendAtomicToll {D X : Type*} [MetricSpace X]
    (γ : C(PathTime, X)) {p : D → X} (hp : Injective p) (m : D → ℝ≥0∞) :
    preterminalToll γ (extendAtomicToll p m) =
      ∑'s, m s * preterminalVisitCount γ (p s) := by
  rw [preterminalToll_eq_visits]
  calc
    (∑'x, extendAtomicToll p m x * preterminalVisitCount γ x) =
        ∑'s, extendAtomicToll p m (p s) * preterminalVisitCount γ (p s) := by
      symm
      apply hp.tsum_eq (f := fun x : X => extendAtomicToll p m x * preterminalVisitCount γ x)
      intro x hx
      by_contra h
      exact hx (by
        change extendAtomicToll p m x * preterminalVisitCount γ x = 0
        rw [extendAtomicToll_zero p m h, zero_mul])
    _ = _ := by simp only [extendAtomicToll_apply hp]

theorem extendAtomicToll_eq_zero_on_disjoint {D X : Type*} {p : D → X}
    {U B : Set X} (hUB : Disjoint U B) (hp : range p ⊆ B)
    (m : D → ℝ≥0∞) {x : X} (hx : x ∈ U) : extendAtomicToll p m x = 0 := by
  apply extendAtomicToll_zero
  intro h
  exact Set.disjoint_left.mp hUB hx (hp h)


theorem perturbed_endpoint_cost_ge_one
    {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace D] [BorelSpace D] [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (p : D → X) (hp : Injective p) (c : D → ℝ≥0∞)
    (ν : Measure X) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h)
    (hadm : CostAdmissible d p c ν h) {δ : ℝ≥0∞} (hδ : 0 < δ)
    (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot)
    (hΓ : EndpointCode d ν (tupleInfiniteExclusions (h ∘ costTuple)) (ρ.val, θ)) :
    1 ≤ (∫⁻y, perturbedPhysicalDensity h δ y
      ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
      preterminalToll ρ.val (extendAtomicToll p (perturbedAtomicToll h c δ)) := by
  let Γ := forgetCode d ν (tupleInfiniteExclusions (h ∘ costTuple)) ⟨(ρ.val, θ), hΓ⟩
  have hcost := perturbed_cost_ge_one d p c ν Γ h hh hΓ hadm hδ
  rw [preterminalToll_extendAtomicToll _ hp]
  exact hcost

end CircleDomainRigidity

end

end OAI
