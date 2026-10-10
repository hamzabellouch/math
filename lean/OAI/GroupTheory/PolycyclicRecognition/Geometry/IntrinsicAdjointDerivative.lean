import OAI.GroupTheory.PolycyclicRecognition.Geometry.ChartedExponentialFlow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieAdjointSmoothness

namespace OAI

/-! # The infinitesimal adjoint action

Right exponential flow transports a left-invariant field by conjugation.
Naturality of brackets on time times a chart identifies its derivative
with the intrinsic Lie bracket, without a linear representation.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Function
open scoped Manifold ContDiff Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem hasDerivAt_adjoint_exponential_zero
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v w : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    HasDerivAt (fun t : ℝ => adjointLinearMap (E := E) (Exp (t • v)) w)
      (⁅v, w⁆ : GroupLieAlgebra (𝓘(ℝ, E)) G) 0 := by
  let φ := extChartAt (𝓘(ℝ, E)) (1 : G)
  let z₀ : E := φ 1
  let X : E → E := fun z => chartInvariantFrame (1 : G) z v
  let Y : E → E := fun z => chartInvariantFrame (1 : G) z w
  let A : ℝ → E := fun t => adjointLinearMap (E := E) (Exp (t • v)) w
  let Z : ℝ × E → E := fun q => chartInvariantFrame (1 : G) q.2 (A q.1)
  let F := chartExponentialFlow Exp v
  have hAC : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun t : ℝ => adjointLinearMap (E := E) (Exp (t • v))) :=
    contMDiff_conjugationDifferentialHom.comp (hExp.contMDiff_curve v)
  have hA : DifferentiableAt ℝ A 0 :=
    (hAC.contDiff.differentiable (by simp) 0).clm_apply (differentiableAt_const w)
  have hZ : DifferentiableAt ℝ Z (0, z₀) :=
    differentiableAt_chartInvariantFrame_parameter hA (1 : G)
  have hX : DifferentiableAt ℝ X z₀ := differentiableAt_chartInvariantFrame_apply (E := E) (1 : G) v
  have hY : DifferentiableAt ℝ Y z₀ := differentiableAt_chartInvariantFrame_apply (E := E) (1 : G) w
  have hFsmooth : ContDiffAt ℝ ∞ F (0, z₀) := contDiffAt_chartExponentialFlow (E := E) hExp v
  have hF : ContDiffAt ℝ 2 F (0, z₀) := hFsmooth.of_le (by simp)
  have hbase : F (0, z₀) = (0, z₀) :=
    chartExponentialFlow_zero hExp v (mem_extChartAt_target (I := 𝓘(ℝ, E)) (1 : G))
  have hvertical : ∀ u, fderiv ℝ F (0, z₀) (0, u) = (0, u) :=
    fderiv_chartExponentialFlow_vertical_zero (E := E) hExp v
  have hdiff : ∀ᶠ q in 𝓝 (0, z₀), DifferentiableAt ℝ F q :=
    ((hFsmooth.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by norm_num)).mono
      fun _ hq => hq.differentiableAt (by norm_num)
  have htarget : ∀ᶠ q : ℝ × E in 𝓝 (0, z₀), q.2 ∈ φ.target := by
    have ht : φ.target ∈ 𝓝 z₀ := by
      simpa only [φ, z₀, mfld_simps, nhdsWithin_univ] using
        extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ, E)) (1 : G)
    exact continuous_snd.continuousAt.preimage_mem_nhds ht
  have hi : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ.symm z₀ := by
    simpa only [φ, z₀, mfld_simps, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℝ, E)) (n := ∞) (1 : G))
  have hs : ContMDiffAt (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, E)) ∞ Prod.snd ((0 : ℝ), z₀) :=
    contDiffAt_snd.contMDiffAt
  have ht : ContMDiffAt (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, ℝ)) ∞ Prod.fst ((0 : ℝ), z₀) :=
    contDiffAt_fst.contMDiffAt
  have hc : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) ∞ (fun t : ℝ => Exp (t • v)) 0 :=
    (hExp.contMDiff_curve v) 0
  have hct : ContMDiffAt (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, E)) ∞
      (fun q : ℝ × E => Exp (q.1 • v)) ((0 : ℝ), z₀) :=
    hc.comp ((0 : ℝ), z₀) (f := fun q : ℝ × E => q.1) ht
  have hmul := (hi.comp ((0 : ℝ), z₀) hs).mul hct
  have hsource : ∀ᶠ q : ℝ × E in 𝓝 (0, z₀), φ.symm q.2 * Exp (q.1 • v) ∈ φ.source := by
    have hb : φ.symm z₀ * Exp ((0 : ℝ) • v) = 1 := by
      simp only [z₀, φ, extChartAt_to_inv, zero_smul, hExp.map_zero, one_mul]
    have hn : φ.source ∈ 𝓝 (φ.symm z₀ * Exp ((0 : ℝ) • v)) := by
      rw [hb]
      exact extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) (1 : G)
    exact hmul.continuousAt.preimage_mem_nhds hn
  have htime : ∀ᶠ q in 𝓝 (0, z₀), fderiv ℝ F q (1, 0) = (1, X (F q).2) := by
    filter_upwards [hdiff, hsource] with q hq hsrc
    exact fderiv_chartExponentialFlow_time (E := E) hExp v hq hsrc
  have hfield : ∀ᶠ q in 𝓝 (0, z₀), fderiv ℝ F q (0, Z q) = (0, Y (F q).2) := by
    filter_upwards [hdiff, htarget, hsource] with q hq htar hsrc
    exact fderiv_chartExponentialFlow_field (E := E) v w hq htar hsrc
  have hb := transportedField_time_derivative hF hZ hX hY hbase hvertical htime hfield
  have hbr : VectorField.lieBracket ℝ X Y z₀ =
      (⁅v, w⁆ : GroupLieAlgebra (𝓘(ℝ, E)) G) :=
    (mlieBracket_eq_chartBracket (mulInvariantVectorField v) (mulInvariantVectorField w)
      (1 : G)).symm
  rw [hbr] at hb
  have hj := (hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).prodMk
    (hasFDerivAt_const (𝕜 := ℝ) z₀ (0 : ℝ))
  have hd := (hZ.hasFDerivAt.comp (0 : ℝ) hj).hasDerivAt
  change HasDerivAt (fun t : ℝ => Z (t, z₀)) (fderiv ℝ Z (0, z₀) (1, 0)) 0 at hd
  rw [hb] at hd
  have heq : (fun t : ℝ => Z (t, z₀)) = A := by
    funext t
    dsimp only [Z, z₀]
    rw [chartInvariantFrame_one]
    rfl
  rw [heq] at hd
  exact hd

end PolycyclicRecognition

end

end OAI
