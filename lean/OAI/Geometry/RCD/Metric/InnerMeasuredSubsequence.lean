import OAI.Geometry.RCD.Metric.InnerMeasuredApproximation

namespace OAI

/-! # One subsequence with prescribed errors on an interior ball -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

private theorem eventually_select_strictMono {P : ℕ → ℕ → Prop}
    (hP : ∀ j, ∀ᶠ k in atTop, P j k) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∀ j, P j (a j) := by
  choose N hN using fun j => eventually_atTop.mp (hP j)
  let a : ℕ → ℕ := Nat.rec (N 0) (fun j v => max (N (j+1)) (v+1))
  have hge : ∀ j, N j≤a j := by
    intro j
    cases j with
    | zero => exact le_rfl
    | succ j => exact le_max_left _ _
  refine ⟨a,strictMono_nat_of_lt_succ (fun j => ?_),fun j => hN j (a j) (hge j)⟩
  exact (Nat.lt_succ_self (a j)).trans_le (le_max_right _ _)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem inner_measured_subsequence {n : ℕ} {S R : ℝ}
    (hS : 0<S) (hR : 0<R) (hRS : R≤S)
    {μ : Measure X} {p : ℕ → X} {r ε η : ℕ → ℝ} {V : ℕ → X → Euclidean n}
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k)
    (hV : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (V k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hpos : ∀ k, 0<μ.real (ball (p k) (S*r k))) (hεlim : Tendsto ε atTop (𝓝 0))
    (hη : ∀ k, 0<η k) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∀ k,
      IsMeasuredEuclideanApproximation μ n (p (a k)) (r (a k)) R (η k) (V (a k)) := by
  apply eventually_select_strictMono (P:=fun j k =>
    IsMeasuredEuclideanApproximation μ n (p k) (r k) R (η j) (V k))
  intro j
  exact inner_measured_approximation hS hR hRS hr hε hV hfin hpos hεlim (η j) (hη j)

end RegularPointCoordinates

end

end OAI
