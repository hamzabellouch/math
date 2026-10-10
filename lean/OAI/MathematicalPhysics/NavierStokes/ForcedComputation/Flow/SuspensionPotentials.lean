import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ForceMean

namespace OAI

/-! Derivative potentials for the autonomous spatial clock. The horizontal
Hamiltonian and the vertical clock have zero spatial average separately. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set MeasureTheory Filter
open scoped ContDiff Topology

def scalarD (j : Fin 3) (H : Space → ℝ) (x : Space) : ℝ :=
  fderiv ℝ H x (basis j)

theorem scalarD_smooth (j : Fin 3) {H : Space → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (scalarD j H) :=
  (hH.fderiv_right (by simp)).clm_apply contDiff_const

theorem scalarD_comm (i j : Fin 3) {H : Space → ℝ} (hH : ContDiff ℝ ∞ H) :
    scalarD i (scalarD j H) = scalarD j (scalarD i H) := by
  funext x
  unfold scalarD
  rw [fderiv_eval_direction hH, fderiv_eval_direction hH]
  exact hH.contDiffAt.isSymmSndFDerivAt (by simp) _ _

def potentialSuspension (H G : Space → ℝ) (x : Space) : Space :=
  letI := ShearFlows.neZeroThree
  ![scalarD 1 H x, -scalarD 0 H x, scalarD 0 G x]

theorem potentialSuspension_smooth {H G : Space → ℝ}
    (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (potentialSuspension H G) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact scalarD_smooth 1 hH
  · exact (scalarD_smooth 0 hH).neg
  · exact scalarD_smooth 0 hG

theorem potentialSuspension_divergence {H G : Space → ℝ}
    (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (hGz : scalarD 2 G = 0) (x : Space) :
    divergence (potentialSuspension H G) x = 0 := by
  have hs := (potentialSuspension_smooth hH hG).differentiable (by simp)
  have hc (j : Fin 3) : derivative (potentialSuspension H G) j x j =
      fderiv ℝ (fun y => potentialSuspension H G y j) x (basis j) :=
    (fderiv_coordinate hs x (basis j) j).symm
  simp only [divergence, Fin.sum_univ_three, hc, potentialSuspension,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  change scalarD 0 (scalarD 1 H) x +
    fderiv ℝ (-scalarD 0 H) x (basis 1) +
    scalarD 2 (scalarD 0 G) x = 0
  rw [fderiv_neg]
  change scalarD 0 (scalarD 1 H) x - scalarD 1 (scalarD 0 H) x +
    scalarD 2 (scalarD 0 G) x = 0
  rw [scalarD_comm 0 1 hH, scalarD_comm 2 0 hG, hGz]
  simp [scalarD]

theorem potentialSuspension_periodic {L : ℝ} {H G : Space → ℝ}
    (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (hpH : CubePeriodic L H) (hpG : CubePeriodic L G) :
    CubePeriodic L (potentialSuspension H G) := by
  have hh := hpH.fderiv (hH.differentiable (by simp))
  have hg := hpG.fderiv (hG.differentiable (by simp))
  intro x n
  simp only [potentialSuspension, scalarD, hh x n, hg x n]

theorem potentialSuspension_mean_zero {L : ℝ} (hL : 0 ≤ L) {H G : Space → ℝ}
    (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (hpH : CubePeriodic L H) (hpG : CubePeriodic L G) :
    (∫ x in fundamentalCube L, potentialSuspension H G x) = 0 := by
  have hi : IntegrableOn (potentialSuspension H G) (fundamentalCube L) :=
    (potentialSuspension_smooth hH hG).continuous.integrableOn_Icc
  ext j
  change (ContinuousLinearMap.proj j : Space →L[ℝ] ℝ)
    (∫ x in fundamentalCube L, potentialSuspension H G x) = 0
  rw [← (ContinuousLinearMap.proj j : Space →L[ℝ] ℝ).integral_comp_comm hi]
  change (∫ x in fundamentalCube L, potentialSuspension H G x j) = 0
  fin_cases j
  · exact integral_periodic_derivative hL hH hpH 1
  · change (∫ x in fundamentalCube L, -fderiv ℝ H x (basis 0)) = 0
    rw [integral_neg, integral_periodic_derivative hL hH hpH, neg_zero]
  · exact integral_periodic_derivative hL hG hpG 0

theorem scalarD_clock_one {G : Space → ℝ} {x : Space}
    (hG : G =ᶠ[𝓝 x] fun y => y 0) : scalarD 0 G x = 1 := by
  unfold scalarD
  rw [hG.fderiv_eq]
  rw [(hasFDerivAt_apply (𝕜 := ℝ) 0 x).fderiv]
  simp [basis]

end ForcedComputation

end

end OAI
