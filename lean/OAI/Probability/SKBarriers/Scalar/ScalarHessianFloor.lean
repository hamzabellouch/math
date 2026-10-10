import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarSuffixSusceptibility
import OAI.Probability.SKBarriers.Scalar.ScalarHierarchyCramer
import OAI.Probability.SKBarriers.Scalar.ScalarPositiveHessian

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarSusceptibilityFloor (T A : ℝ) : ℝ :=
  1/(2*(Real.cosh (1+2*A^2+4*T+8*T^2))^2)

theorem scalarSusceptibilityFloor_pos (T A : ℝ) : 0<scalarSusceptibilityFloor T A := by
  unfold scalarSusceptibilityFloor
  positivity

theorem scalarSpinTerminal_rootHessian (x : ℝ) :
    rootHessian 0 scalarSpinTerminal x=1-(scalarMagnetization x)^2 := by
  simpa [scalarHierarchy,Fin.sum_univ_succ,hierarchyAtom,
    scalarMomentSquare,one_mul] using scalarHierarchy_spin_hessian_overlap_sum 0
      (Fin.elim0) (Fin.elim0) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) x

theorem scalarSpinTerminal_spinConvex : ScalarSpinConvex scalarSpinTerminal := by
  intro x
  have H := (scalarHierarchy_spin_derivative_bounds 0 Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) x).2
  exact ⟨H.1.le,H.2⟩

theorem scalarHierarchyAverage_terminal_hessian_floor (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {T A : ℝ} (hT : 0≤T) (hA : 0≤A) (hv : ∑ i, (v i)^2 ≤ T)
    {x : ℝ} (hx : |x|≤A) :
    scalarSusceptibilityFloor T A≤ scalarHierarchyAverage n m v scalarSpinTerminal
      (rootHessian 0 scalarSpinTerminal) x := by
  have hg : BoundedScalar scalarMagnetization :=
    ⟨scalarMagnetization_lipschitz.continuous,1,zero_le_one,scalarMagnetization_abs_le_one⟩
  have he : rootHessian 0 scalarSpinTerminal=fun z => 1-(scalarMagnetization z)^2 :=
    funext scalarSpinTerminal_rootHessian
  rw [he,scalarHierarchyAverage_sub scalarSpinTerminal_regular (BoundedScalar.const 1) hg.sq,
    scalarHierarchyAverage_const scalarSpinTerminal_regular]
  have G := scalarHierarchyAverage_square_gap_compact n m v hm hmono hT hA hv hx
  change _≤1-scalarSusceptibilityFloor T A at G
  linarith

theorem scalarHierarchy_hessian_floor (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {T A : ℝ} (hT : 0≤T) (hA : 0≤A) (hv : ∑ i, (v i)^2 ≤ T)
    {x : ℝ} (hx : |x|≤A) :
    scalarSusceptibilityFloor T A≤rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) x := by
  have H := (scalarHierarchy_cramer_data scalarSpinTerminal_regular scalarSpinTerminal_spinConvex n m v hm x).2.1
  have hg : BoundedScalar scalarMagnetization :=
    ⟨scalarMagnetization_lipschitz.continuous,1,zero_le_one,scalarMagnetization_abs_le_one⟩
  have he : rootHessian 0 scalarSpinTerminal=fun z => 1-(scalarMagnetization z)^2 :=
    funext scalarSpinTerminal_rootHessian
  rw [he,scalarHierarchyAverage_sub scalarSpinTerminal_regular (BoundedScalar.const 1) hg.sq,
    scalarHierarchyAverage_const scalarSpinTerminal_regular] at H
  have G := scalarHierarchyAverage_square_gap_compact n m v hm hmono hT hA hv hx
  change _≤1-scalarSusceptibilityFloor T A at G
  linarith

end SK.Analytic

end
end

end OAI
