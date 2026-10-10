import OAI.Analysis.Mahler.ExteriorDirectional
import OAI.Analysis.Mahler.ContinuousWedgeDerivative
import OAI.Analysis.Mahler.WedgeTwoDifferentialAlgebra

namespace OAI

open scoped BigOperators

namespace Mahler
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype J]

noncomputable def continuousWedgeFin (basis : Module.Basis J ℝ E) {p q : ℕ}
    (A : E [⋀^Fin p]→L[ℝ] ℂ) (B : E [⋀^Fin q]→L[ℝ] ℂ) :
    E [⋀^Fin (p+q)]→L[ℝ] ℂ :=
  continuousReindex finSumFinEquiv (basisContinuousWedge basis A B)

@[simp] lemma continuousWedgeFin_toAlternatingMap (basis : Module.Basis J ℝ E) {p q : ℕ}
    (A : E [⋀^Fin p]→L[ℝ] ℂ) (B : E [⋀^Fin q]→L[ℝ] ℂ) :
    (continuousWedgeFin basis A B).toAlternatingMap =
      (wedge A.toAlternatingMap B.toAlternatingMap).domDomCongr finSumFinEquiv := by
  rw [continuousWedgeFin, continuousReindex_toAlternatingMap, basisContinuousWedge_toAlternatingMap]

lemma differentiableAt_continuousWedgeFin (basis : Module.Basis J ℝ E) {p q : ℕ}
    {A : E → E [⋀^Fin p]→L[ℝ] ℂ} {B : E → E [⋀^Fin q]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    DifferentiableAt ℝ (fun y => continuousWedgeFin basis (A y) (B y)) x :=
  (continuousReindex finSumFinEquiv).differentiableAt.comp x
    (differentiableAt_basisContinuousWedge basis hA hB)

lemma contDiffAt_continuousWedgeFin (basis : Module.Basis J ℝ E) {p q : ℕ}
    {r : WithTop ℕ∞} {A : E → E [⋀^Fin p]→L[ℝ] ℂ}
    {B : E → E [⋀^Fin q]→L[ℝ] ℂ} {x : E}
    (hA : ContDiffAt ℝ r A x) (hB : ContDiffAt ℝ r B x) :
    ContDiffAt ℝ r (fun y => continuousWedgeFin basis (A y) (B y)) x :=
  (continuousReindex (E := E) (finSumFinEquiv (m := p) (n := q))).contDiff.contDiffAt.comp x
    (contDiffAt_basisContinuousWedge basis hA hB)

lemma fderiv_continuousWedgeFin (basis : Module.Basis J ℝ E) {p q : ℕ}
    {A : E → E [⋀^Fin p]→L[ℝ] ℂ} {B : E → E [⋀^Fin q]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (u : E) :
    fderiv ℝ (fun y => continuousWedgeFin basis (A y) (B y)) x u =
      continuousWedgeFin basis (fderiv ℝ A x u) (B x) +
      continuousWedgeFin basis (A x) (fderiv ℝ B x u) := by
  have h := (continuousReindex (E := E) (finSumFinEquiv (m := p) (n := q))).hasFDerivAt.comp x
    (differentiableAt_basisContinuousWedge basis hA hB).hasFDerivAt
  have he := congrArg (fun L => L u) h.fderiv
  change fderiv ℝ (fun y => continuousWedgeFin basis (A y) (B y)) x u =
    continuousReindex finSumFinEquiv
      (fderiv ℝ (fun y => basisContinuousWedge basis (A y) (B y)) x u) at he
  rw [he, fderiv_basisContinuousWedge basis hA hB, map_add]
  rfl

/-- Exterior Leibniz rule for an actual two-form times an arbitrary-degree
form. The sign is positive because the left degree is two. -/
theorem extDeriv_continuousWedge_two (basis : Module.Basis J ℝ E) {n : ℕ}
    {A : E → E [⋀^Fin 2]→L[ℝ] ℂ} {B : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    (extDeriv (fun y => continuousWedgeFin basis (A y) (B y)) x).toAlternatingMap =
      (wedge (extDeriv A x).toAlternatingMap (B x).toAlternatingMap).domDomCongr
        (derivativeLeftEquiv n) +
      (wedge (A x).toAlternatingMap (extDeriv B x).toAlternatingMap).domDomCongr
        (derivativeRightEquiv n) := by
  rw [extDeriv_directional basis (differentiableAt_continuousWedgeFin basis hA hB),
    extDeriv_directional basis hA, extDeriv_directional basis hB]
  simp only [fderiv_continuousWedgeFin basis hA hB,
    ContinuousAlternatingMap.toAlternatingMap_add, continuousWedgeFin_toAlternatingMap,
    wedge_add_right, AlternatingMap.domDomCongr_add, Finset.sum_add_distrib,
    wedge_sum_left, wedge_sum_right, domDomCongr_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    exact wedge_derivative_assoc basis _ _ _
  · apply Finset.sum_congr rfl
    intro j hj
    exact wedge_derivative_move_two basis _ _ _

end Mahler

end OAI
