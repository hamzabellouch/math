import OAI.MeasureTheory.Falconer.Radial.CoarsePlateFilter

namespace OAI

/-! # The original coarse exclusions are symmetric in their two endpoints -/

namespace Falconer
open Set MeasureTheory

theorem heavyPlateCellPairs_swap {d : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (j : ℕ) (r m : ℝ) {x y : Space d}
    (h : (x,y) ∈ heavyPlateCellPairs ρ Q j r m) :
    (y,x) ∈ heavyPlateCellPairs ρ Q j r m := by
  obtain ⟨p,hp,q,hq,⟨w,hw,t,hm,hp',hq'⟩,hx,hy⟩ :=
    (mem_heavyPlateCellPairs_iff ρ Q j r m x y).mp h
  exact (mem_heavyPlateCellPairs_iff ρ Q j r m y x).mpr
    ⟨q,hq,p,hp,⟨w,hw,t,hm,hq',hp'⟩,hy,hx⟩

theorem coarsePlateFilter_swap {d : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (j₀ J : ℕ) (r m : ℕ → ℝ) {x y : Space d}
    (h : (x,y) ∈ coarsePlateFilter ρ Q j₀ J r m) :
    (y,x) ∈ coarsePlateFilter ρ Q j₀ J r m := by
  refine ⟨⟨h.1.2,h.1.1⟩,?_⟩
  intro hex
  obtain ⟨j,hj,hxy⟩ := mem_iUnion₂.mp hex
  exact h.2 (mem_iUnion₂.mpr ⟨j,hj,heavyPlateCellPairs_swap ρ Q j (r j) (m j) hxy⟩)

theorem coarsePlateFilter_swap_iff {d : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (j₀ J : ℕ) (r m : ℕ → ℝ) (x y : Space d) :
    (x,y) ∈ coarsePlateFilter ρ Q j₀ J r m ↔
      (y,x) ∈ coarsePlateFilter ρ Q j₀ J r m :=
  ⟨coarsePlateFilter_swap ρ Q j₀ J r m,coarsePlateFilter_swap ρ Q j₀ J r m⟩

end Falconer

end OAI
