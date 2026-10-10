import OAI.MeasureTheory.Falconer.Estimates.ProductTransformPartition

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphProductWeight_nonneg (s : Bool) (m j k : ℕ) (p : UnitCircle × UnitCircle) :
    0 ≤ (graphProductWeight s m j k p).re := by
  have hb := mul_nonneg (circleAngularBin_bounds m j p.1).1 (circleAngularBin_bounds m k p.2).1
  have hs := graphSignPartition_bounds ((p.1:Plane),(p.2:Plane))
  cases s
  · exact mul_nonneg hb hs.2.2.1
  · exact mul_nonneg hb hs.1

theorem graphProductWeight_norm (s : Bool) (m j k : ℕ) (p : UnitCircle × UnitCircle) :
    ‖graphProductWeight s m j k p‖ = (graphProductWeight s m j k p).re := by
  have hp := graphProductWeight_nonneg s m j k p
  unfold graphProductWeight at hp ⊢
  simpa only [Complex.norm_real,Real.norm_eq_abs,Complex.ofReal_re] using abs_of_nonneg hp

theorem graphProductWeight_norm_total {m : ℕ} (hm : 0 < m) (p : UnitCircle × UnitCircle) :
    (∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, ∑ s : Bool, ‖graphProductWeight s m j k p‖) = 1 := by
  have he := congrArg Complex.re (graphProductWeight_total hm p)
  simpa only [Complex.re_sum,Complex.one_re,graphProductWeight_norm] using he

end PlanarFalconer

end OAI
