import OAI.GroupTheory.PolycyclicRecognition.Algebra.FixedChartTranslation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SuspendedVectorFieldBracket

namespace OAI

/-! # The right exponential flow in an identity chart -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Function
open scoped Manifold ContDiff Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- Right multiplication is the flow of the left-invariant field. -/
def chartExponentialFlow (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (v : E)
    (q : ℝ × E) : ℝ × E :=
  (q.1, extChartAt (𝓘(ℝ, E)) (1 : G)
    ((extChartAt (𝓘(ℝ, E)) (1 : G)).symm q.2 * Exp (q.1 • v)))

theorem contDiffAt_chartExponentialFlow
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) (v : E) :
    ContDiffAt ℝ ∞ (chartExponentialFlow Exp v)
      (0, extChartAt (𝓘(ℝ, E)) (1 : G) 1) := by
  let φ := extChartAt (𝓘(ℝ, E)) (1 : G)
  have hi : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ.symm (φ 1) := by
    simpa only [φ, mfld_simps, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℝ, E)) (n := ∞) (1 : G))
  have hmul : ContMDiffAt (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, E)) ∞
      (fun q : ℝ × E => φ.symm q.2 * Exp (q.1 • v)) ((0 : ℝ), φ 1) := by
    have hs : ContMDiffAt (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, E)) ∞ Prod.snd ((0 : ℝ), φ 1) :=
      contDiffAt_snd.contMDiffAt
    have ht : ContMDiffAt (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, ℝ)) ∞ Prod.fst ((0 : ℝ), φ 1) :=
      contDiffAt_fst.contMDiffAt
    have hc : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) ∞ (fun s : ℝ => Exp (s • v)) 0 :=
      (hExp.contMDiff_curve v) 0
    have hct : ContMDiffAt (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, E)) ∞
        (fun q : ℝ × E => Exp (q.1 • v)) ((0 : ℝ), φ 1) :=
      hc.comp ((0 : ℝ), φ 1) (f := fun q : ℝ × E => q.1) ht
    exact (hi.comp ((0 : ℝ), φ 1) hs).mul hct
  have hbase : φ.symm (φ 1) * Exp ((0 : ℝ) • v) = 1 := by
    simp only [φ, extChartAt_to_inv, zero_smul, one_mul]
    exact hExp.map_zero
  have hφ := (contMDiffAt_extChartAt (I := 𝓘(ℝ, E)) (x := (1 : G))).comp_of_eq hmul hbase
  exact contDiffAt_fst.prodMk hφ.contDiffAt

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
@[simp] theorem chartExponentialFlow_zero
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) (v : E)
    {z : E} (hz : z ∈ (extChartAt (𝓘(ℝ, E)) (1 : G)).target) :
    chartExponentialFlow Exp v (0, z) = (0, z) := by
  unfold chartExponentialFlow
  simp only [zero_smul]
  change ((0 : ℝ), extChartAt (𝓘(ℝ, E)) (1 : G)
    ((extChartAt (𝓘(ℝ, E)) (1 : G)).symm z * Exp (0 : GroupLieAlgebra (𝓘(ℝ, E)) G))) = _
  rw [hExp.map_zero, mul_one, (extChartAt (𝓘(ℝ, E)) (1 : G)).right_inv hz]

theorem fderiv_chartExponentialFlow_vertical_zero
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) (v w : E) :
    fderiv ℝ (chartExponentialFlow Exp v)
      (0, extChartAt (𝓘(ℝ, E)) (1 : G) 1) (0, w) = (0, w) := by
  let z₀ := extChartAt (𝓘(ℝ, E)) (1 : G) 1
  have hd := (contDiffAt_chartExponentialFlow hExp v).differentiableAt (by simp)
  rw [fderiv_prod_apply_snd hd]
  have heq : (fun z => chartExponentialFlow Exp v (0, z)) =ᶠ[𝓝 z₀]
      (fun z : E => ((0 : ℝ), z)) := by
    have ht : (extChartAt (𝓘(ℝ, E)) (1 : G)).target ∈ 𝓝 z₀ := by
      simpa only [z₀, mfld_simps, nhdsWithin_univ] using
        extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ, E)) (1 : G)
    exact eventually_of_mem ht fun z hz => chartExponentialFlow_zero hExp v hz
  rw [heq.fderiv_eq]
  have hh := (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) z₀).prodMk
    (hasFDerivAt_id (𝕜 := ℝ) z₀)
  dsimp only [id_eq] at hh
  rw [hh.fderiv]
  rfl

theorem hasDerivAt_chartExponentialFlow_time
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v : E) (t : ℝ) (z : E)
    (ht : (extChartAt (𝓘(ℝ, E)) (1 : G)).symm z * Exp (t • v) ∈
      (extChartAt (𝓘(ℝ, E)) (1 : G)).source) :
    HasDerivAt (fun s => (chartExponentialFlow Exp v (s, z)).2)
      (chartInvariantFrame (1 : G) (chartExponentialFlow Exp v (t, z)).2 v) t := by
  let φ := extChartAt (𝓘(ℝ, E)) (1 : G)
  have hc := invariant_integralCurve_mul_left (hExp.isMIntegralCurve v) (φ.symm z) t
  have hφ : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (φ.symm z * Exp (t • v)) :=
    mdifferentiableAt_extChartAt (by simpa only [φ, mfld_simps] using ht)
  let D : ℝ →L[ℝ] E :=
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (φ.symm z * Exp (t • v)) : E →L[ℝ] E).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (mulInvariantVectorField v (φ.symm z * Exp (t • v)) : E))
  have hfd : HasFDerivAt (fun s => φ (φ.symm z * Exp (s • v))) D t := by
    apply (hasMFDerivAt_iff_hasFDerivAt).mp
    exact hφ.hasMFDerivAt.comp t hc
  have hd := hfd.hasDerivAt
  have he : chartInvariantFrame (1 : G) (φ (φ.symm z * Exp (t • v))) v =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (φ.symm z * Exp (t • v)))
        (mulInvariantVectorField v (φ.symm z * Exp (t • v))) :=
    chartVectorField_apply_chart (1 : G) (mulInvariantVectorField v) ht
  dsimp only [chartExponentialFlow] at ⊢
  rw [he]
  change HasDerivAt (fun s => φ (φ.symm z * Exp (s • v)))
    ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (φ.symm z * Exp (t • v)) : E →L[ℝ] E)
      ((1 : ℝ) • (mulInvariantVectorField v (φ.symm z * Exp (t • v)) : E))) t at hd
  rw [one_smul] at hd
  exact hd

theorem fderiv_chartExponentialFlow_time
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v : E) {q : ℝ × E} (hq : DifferentiableAt ℝ (chartExponentialFlow Exp v) q)
    (ht : (extChartAt (𝓘(ℝ, E)) (1 : G)).symm q.2 * Exp (q.1 • v) ∈
      (extChartAt (𝓘(ℝ, E)) (1 : G)).source) :
    fderiv ℝ (chartExponentialFlow Exp v) q (1, 0) =
      (1, chartInvariantFrame (1 : G) (chartExponentialFlow Exp v q).2 v) := by
  rw [fderiv_prod_apply_fst hq]
  have hd := (hasFDerivAt_id (𝕜 := ℝ) q.1).prodMk
    (hasDerivAt_chartExponentialFlow_time hExp v q.1 q.2 ht).hasFDerivAt
  dsimp only [chartExponentialFlow, id_eq] at hd ⊢
  rw [hd.fderiv]
  simp

theorem fderiv_chartExponentialFlow_field
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (v w : E) {q : ℝ × E}
    (hq : DifferentiableAt ℝ (chartExponentialFlow Exp v) q)
    (hz : q.2 ∈ (extChartAt (𝓘(ℝ, E)) (1 : G)).target)
    (ht : (extChartAt (𝓘(ℝ, E)) (1 : G)).symm q.2 * Exp (q.1 • v) ∈
      (extChartAt (𝓘(ℝ, E)) (1 : G)).source) :
    fderiv ℝ (chartExponentialFlow Exp v) q
      (0, chartInvariantFrame (1 : G) q.2
        (conjugationDifferentialHom (E := E) (Exp (q.1 • v)) w)) =
      (0, chartInvariantFrame (1 : G) (chartExponentialFlow Exp v q).2 w) := by
  rw [fderiv_prod_apply_snd hq]
  have hp : DifferentiableAt ℝ (fun z : E => chartExponentialFlow Exp v (q.1, z)) q.2 :=
    hq.comp q.2 (f := fun z : E => (q.1, z))
      ((differentiableAt_const q.1).prodMk differentiableAt_id)
  have hsp : DifferentiableAt ℝ (fun z : E => (chartExponentialFlow Exp v (q.1, z)).2) q.2 := hp.snd
  have hd := (hasFDerivAt_const (𝕜 := ℝ) q.1 q.2).prodMk hsp.hasFDerivAt
  dsimp only [Function.comp_def, chartExponentialFlow] at hd ⊢
  rw [hd.fderiv]
  change (0, fderiv ℝ (fun y => extChartAt (𝓘(ℝ, E)) (1 : G)
    ((extChartAt (𝓘(ℝ, E)) (1 : G)).symm y * Exp (q.1 • v))) q.2
    (chartInvariantFrame (1 : G) q.2
      (conjugationDifferentialHom (E := E) (Exp (q.1 • v)) w))) = _
  rw [chart_rightTranslation_related (Exp (q.1 • v)) w hz ht]

end PolycyclicRecognition

end

end OAI
