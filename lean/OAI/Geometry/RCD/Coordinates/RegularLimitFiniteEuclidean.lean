import OAI.Geometry.RCD.Coordinates.RegularLimitInnerProductBall
import OAI.Geometry.RCD.Metric.ConvexPackingFiniteDimensional
import OAI.Geometry.RCD.Metric.PointedLimitPacking

namespace OAI

/-! # Finite-dimensional Euclidean realization of the actual inner limit ball -/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [MetricSpace Y] [ProperSpace Y] {K : ℝ} {n : ℕ}
  (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]

include hX in
theorem regular_limit_finite_euclidean (hn : 2 ≤ n) (hK : K ≤ 0)
    {o : X} (ho : IsRegular n o) {q : Y}
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hp : Tendsto p atTop (𝓝 o)) (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -1 ≤ K * (4*r k)^2)
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (ε k) (V k)) :
    ∃ m : ℕ, m ≤ n ∧ ∃ f : closedBall q (1/4:ℝ) → Euclidean m,
      Isometry f ∧ Convex ℝ (range f) ∧ IsCompact (range f) ∧ f ⟨q,by simp⟩ = 0 := by
  classical
  obtain ⟨E,m,hE⟩ := hX.regular_limit_inner_product_ball hn hK ho p r ε V hp hr hr0 hε hcurv hV
  let := m
  obtain ⟨i,f,hiso,hconv,hcompact,hspan,hzero⟩ := hE
  let := i
  have hpack : ∀ {ι : Type} [Fintype ι] (v : ι → E) {d : ℝ}, 0<d → d≤1 →
      (∀ i, v i ∈ range f) → Pairwise (fun i j => d≤dist (v i) (v j)) →
      (Fintype.card ι:ℝ)*(d/2)^n ≤ Real.cosh 1^(n-1)*8^n := by
    intro ι _ v d hd hd1 hv hsep
    choose x hx using hv
    apply hX.pointed_limit_packing hn p r ε V hr hε hcurv hV (fun i => (x i:Y)) hd hd1
    · intro j
      exact (x j).property.trans (by norm_num)
    · intro a b hab
      have hh := hsep hab
      change d ≤ dist (v a) (v b) at hh
      rw [← hx a,← hx b,hiso.dist_eq] at hh
      exact hh
  obtain ⟨hfin,hdim⟩ := finite_dimensional_of_convex_packing hconv
    (show (0:E) ∈ range f from ⟨⟨q,by simp⟩,hzero⟩) hspan n _ hpack
  let := hfin
  let e := (stdOrthonormalBasis ℝ E).repr
  have hcrange : range (fun x => e (f x)) = e '' range f := by
    ext z
    simp only [mem_range,mem_image]
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨f x,⟨x,rfl⟩,rfl⟩
    · rintro ⟨y,⟨x,rfl⟩,rfl⟩
      exact ⟨x,rfl⟩
  refine ⟨Module.finrank ℝ E,hdim,(fun x => e (f x)),e.isometry.comp hiso,?_,?_,?_⟩
  · rw [hcrange]
    exact hconv.linear_image e.toLinearMap
  · rw [hcrange]
    exact hcompact.image e.continuous
  · change e (f ⟨q,by simp⟩) = 0
    rw [hzero,map_zero]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
