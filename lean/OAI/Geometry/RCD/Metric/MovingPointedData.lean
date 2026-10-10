import OAI.Geometry.RCD.Metric.MovingPointedCompactness

namespace OAI

/-! # A single sequence of prescribed metric approximation maps -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem PointedSequenceConverges.subsequence_data {p : ℕ → X} {q : Y} {r : ℕ → ℝ}
    (h : PointedSequenceConverges p q r) {S : ℝ} (hS : 0<S) :
    ∃ (a : ℕ → ℕ) (V : ℕ → X → Y), StrictMono a ∧
      ∀ k, IsPointedApproximation (p (a k)) q (r (a k)) S (1/((k:ℝ)+1)) (V k) := by
  have htail (k : ℕ) : ∃ N : ℕ, ∀ i≥N, ∃ f : X → Y,
      IsPointedApproximation (p i) q (r i) S (1/((k:ℝ)+1)) f :=
    eventually_atTop.mp (h S hS _ (by positivity))
  choose N hN using htail
  let a : ℕ → ℕ := Nat.rec (N 0) (fun k j => max (j+1) (N (k+1)))
  have ha : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro k
    change a k < max (a k+1) (N (k+1))
    exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  have hbound (k : ℕ) : N k≤a k := by
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_max_right _ _
  choose V hV using fun k => hN k (a k) (hbound k)
  exact ⟨a,V,ha,hV⟩

end RegularPointCoordinates

end

end OAI
