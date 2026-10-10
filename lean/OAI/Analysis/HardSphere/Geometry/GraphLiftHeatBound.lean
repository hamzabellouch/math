import Mathlib
import OAI.Analysis.HardSphere.Geometry.AllowedProjection
import OAI.Analysis.HardSphere.Cutoffs.RegularizationWeight

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open ContinuousLinearMap Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F] [Nontrivial F]
local instance graphLiftHeatBoundRealAlgebra : Algebra ℝ (F →L[ℂ] F) :=
  Algebra.restrictScalars ℝ ℂ _

lemma exists_graph_lift_of_heat_bound (A : E →L[ℂ] F) (hA : ‖A‖≤1)
    (hdense : DenseRange (A.comp A.adjoint)) (u : F) (C : ℝ)
    (hb : ∀ n : ℕ, (1 / ((n:ℝ)+1))⁻¹ *
      (‖u‖^2-(inner ℂ u ((cfc (p := IsSelfAdjoint) (heatScalar (1/((n:ℝ)+1)))
        (A.comp A.adjoint)) u)).re) ≤ C) :
    ∃ v : E, A v=u ∧ ‖v‖^2≤‖u‖^2+C := by
  let d : ℕ→ℝ := fun n ↦ 1/((n:ℝ)+1)
  have hd (n : ℕ) : 0<d n := by dsimp [d]; positivity
  let R := A.comp A.adjoint
  let v : ℕ→E := fun n ↦ A.adjoint ((cfc (p := IsSelfAdjoint) (regularizationWeight (d n)) R) u)
  have hv (n : ℕ) : ‖v n‖^2≤‖u‖^2+C :=
    (regularized_lift_norm_sq A hA (hd n) u).trans (add_le_add_right (hb n) _)
  have hB : 0≤‖u‖^2+C := (sq_nonneg ‖v 0‖).trans (hv 0)
  have hRp : R.IsPositive := by simpa [R] using isPositive_adjoint_comp_self A.adjoint
  have hRn : ‖R‖≤1 := (opNorm_comp_le _ _).trans (by rw [adjoint.norm_map]; nlinarith [norm_nonneg A])
  have ht : Tendsto (fun n ↦ A (v n)) atTop (𝓝 u) := by
    have hh := regularizationOperator_tendsto hd tendsto_one_div_add_atTop_nhds_zero_nat hRp hRn hdense u
    convert hh using 1
    funext n
    rw [regularizationOperator_eq hRp hRn (hd n)]
    rfl
  obtain ⟨w,hw,hwu⟩ := exists_bounded_lift_of_tendsto A v
    (C := Real.sqrt (‖u‖^2+C)) (fun n ↦ (Real.le_sqrt (norm_nonneg _) hB).mpr (hv n)) ht
  refine ⟨w,hwu,?_⟩
  calc
    ‖w‖^2 ≤ (Real.sqrt (‖u‖^2+C))^2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    _ = _ := Real.sq_sqrt hB

end HardSphere

end

end OAI
