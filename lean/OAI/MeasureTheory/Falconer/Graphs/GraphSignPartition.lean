import OAI.MeasureTheory.Falconer.Graphs.GraphSignChart
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

noncomputable def graphSignPlus (p : Plane × Plane) : ℝ :=
  Real.smoothTransition ((‖p.1+p.2‖^2-1)/2)

noncomputable def graphSignMinus (p : Plane × Plane) : ℝ := 1-graphSignPlus p

theorem graphSignPlus_contDiff : ContDiff ℝ ∞ graphSignPlus := by
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_fst.add contDiff_snd).norm_sq ℝ).sub contDiff_const |>.div_const 2)

theorem graphSignMinus_contDiff : ContDiff ℝ ∞ graphSignMinus :=
  contDiff_const.sub graphSignPlus_contDiff

theorem graphSignPartition_bounds (p : Plane × Plane) :
    0 ≤ graphSignPlus p ∧ graphSignPlus p ≤ 1 ∧
    0 ≤ graphSignMinus p ∧ graphSignMinus p ≤ 1 ∧
    graphSignPlus p+graphSignMinus p = 1 := by
  have h₀ := Real.smoothTransition.nonneg ((‖p.1+p.2‖^2-1)/2)
  have h₁ := Real.smoothTransition.le_one ((‖p.1+p.2‖^2-1)/2)
  dsimp [graphSignPlus, graphSignMinus]
  exact ⟨h₀, h₁, sub_nonneg.mpr h₁, sub_le_self _ h₀, by ring⟩

noncomputable def circleGraphSignPlus (p : UnitCircle × UnitCircle) : ℝ :=
  graphSignPlus (p.1, p.2)

noncomputable def circleGraphSignMinus (p : UnitCircle × UnitCircle) : ℝ :=
  graphSignMinus (p.1, p.2)

theorem circleGraphSignPlus_tsupport :
    tsupport circleGraphSignPlus ⊆ {p | 1 ≤ ‖(p.1:Plane)+(p.2:Plane)‖} := by
  apply closure_minimal
  · intro p hp
    have h : 0 < (‖(p.1:Plane)+(p.2:Plane)‖^2-1)/2 :=
      not_le.mp (fun hn => hp (Real.smoothTransition.zero_of_nonpos hn))
    change 1 ≤ ‖(p.1:Plane)+(p.2:Plane)‖
    nlinarith [norm_nonneg ((p.1:Plane)+(p.2:Plane))]
  · exact isClosed_le continuous_const (by fun_prop)

theorem circleGraphSignMinus_tsupport :
    tsupport circleGraphSignMinus ⊆ {p | 1 ≤ ‖(p.1:Plane)-(p.2:Plane)‖} := by
  apply closure_minimal
  · intro p hp
    have h : (‖(p.1:Plane)+(p.2:Plane)‖^2-1)/2 < 1 := by
      apply not_le.mp
      intro hn
      apply hp
      change 1-Real.smoothTransition _ = 0
      rw [Real.smoothTransition.one_of_one_le hn, sub_self]
    have he : ‖(p.1:Plane)+(p.2:Plane)‖^2+‖(p.1:Plane)-(p.2:Plane)‖^2 = 4 := by
      rw [norm_add_sq_real, norm_sub_sq_real, p.1.property, p.2.property]
      ring
    change 1 ≤ ‖(p.1:Plane)-(p.2:Plane)‖
    nlinarith [norm_nonneg ((p.1:Plane)-(p.2:Plane))]
  · exact isClosed_le continuous_const (by fun_prop)

theorem circleGraphSignPartition (p : UnitCircle × UnitCircle) :
    0 ≤ circleGraphSignPlus p ∧ 0 ≤ circleGraphSignMinus p ∧
      circleGraphSignPlus p+circleGraphSignMinus p = 1 :=
  ⟨(graphSignPartition_bounds (p.1,p.2)).1,
    (graphSignPartition_bounds (p.1,p.2)).2.2.1,
    (graphSignPartition_bounds (p.1,p.2)).2.2.2.2⟩

end PlanarFalconer

end OAI
