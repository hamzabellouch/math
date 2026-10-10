import OAI.Analysis.CircleDomains.Topology.PathTolls
import OAI.Analysis.CircleDomains.Selection.PreterminalVisits

namespace OAI

/-! True boundary tolls with exactly the final parameter omitted, retaining
all multiplicities at earlier times. Positive added weights control code mass. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def preterminalToll (γ : C(PathTime, X)) (m : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' t : PathTime, if t = ⊤ then 0 else m (γ t)

theorem preterminalToll_eq_visits (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    preterminalToll γ m = ∑' x, m x * preterminalVisitCount γ x := by
  rw [preterminalToll, ← ENNReal.tsum_fiberwise (fun t => if t = ⊤ then 0 else m (γ t)) γ]
  apply tsum_congr
  intro x
  rw [preterminalVisitCount_eq_tsum, ← ENNReal.tsum_mul_left,
    tsum_subtype (γ ⁻¹' {x}) (fun t : PathTime => if t = ⊤ then 0 else m (γ t))]
  apply tsum_congr
  intro t
  by_cases ht : t = ⊤ <;> by_cases hx : γ t = x <;> simp [ht, hx, Set.indicator]

theorem preterminalToll_eq_support (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    preterminalToll γ m = ∑' x : Function.support m, m x * preterminalVisitCount γ x := by
  rw [preterminalToll_eq_visits]
  symm
  apply tsum_subtype_eq_of_support_subset (f := fun x : X => m x * preterminalVisitCount γ x)
  intro x hx
  contrapose! hx
  simp only [Function.mem_support] at hx ⊢
  simp [hx]

theorem preterminalToll_add_terminal (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    preterminalToll γ m + m (γ ⊤) = boundaryToll γ m := by
  rw [boundaryToll, ENNReal.tsum_eq_add_tsum_ite ⊤, add_comm]
  unfold preterminalToll
  congr 1
  apply tsum_congr
  intro t
  by_cases ht : t = ⊤ <;> simp [ht]

theorem preterminalToll_mono (γ : C(PathTime, X)) {m n : X → ℝ≥0∞}
    (hmn : m ≤ n) : preterminalToll γ m ≤ preterminalToll γ n := by
  unfold preterminalToll
  apply ENNReal.tsum_le_tsum
  intro t
  split_ifs
  · exact le_rfl
  · exact hmn _

theorem weighted_preterminal_sum_le {D : Type*} (γ : C(PathTime, X)) (p : D → X)
    {c m : D → ℝ≥0∞} {δ : ℝ≥0∞} (hm : ∀ s, δ * c s ≤ m s) :
    δ * (∑' s, c s * preterminalVisitCount γ (p s)) ≤
      ∑' s, m s * preterminalVisitCount γ (p s) := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro s
  rw [← mul_assoc]
  exact mul_le_mul' (hm s) le_rfl

theorem finite_preterminal_sum_of_positive_tolls {D : Type*}
    (γ : C(PathTime, X)) (p : D → X) {c m : D → ℝ≥0∞} {δ : ℝ≥0∞}
    (hδ : 0 < δ) (hm : ∀ s, δ * c s ≤ m s)
    (hfinite : (∑' s, m s * preterminalVisitCount γ (p s)) < ∞) :
    (∑' s, c s * preterminalVisitCount γ (p s)) < ∞ := by
  by_contra h
  have he : (∑' s, c s * preterminalVisitCount γ (p s)) = ∞ :=
    top_unique (not_lt.mp h)
  have hb := lt_of_le_of_lt (weighted_preterminal_sum_le γ p hm) hfinite
  simp only [he, ENNReal.mul_top hδ.ne', lt_self_iff_false] at hb

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_preterminalToll {m : X → ℝ≥0∞} (hm : (support m).Countable) :
    Measurable (fun γ : C(PathTime, X) => preterminalToll γ m) := by
  let : Countable (support m) := hm.to_subtype
  simp_rw [preterminalToll_eq_support]
  exact Measurable.tsum fun x => measurable_const.mul
    (measurable_preterminalVisitCount.comp (measurable_id.prodMk measurable_const))

end CircleDomainRigidity

end

end OAI
