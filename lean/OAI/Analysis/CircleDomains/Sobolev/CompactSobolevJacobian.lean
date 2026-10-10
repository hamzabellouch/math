import OAI.Analysis.CircleDomains.Sobolev.PositiveSobolevApproximation
import OAI.Analysis.CircleDomains.Sobolev.MollificationEnergy
import OAI.Analysis.CircleDomains.Sobolev.L2ProductConvergence
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

namespace OAI

/-! The integral of the Jacobian of two compact Sobolev scalars is zero.
Only one scalar is mollified. Its two differentiated test functions have
commuting mixed derivatives, and strong L2 convergence passes the pairing
to the original gradients. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem tendsto_integral_mul_of_L2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : ℕ → X → ℝ} {G φ : X → ℝ}
    (hg : ∀ n, MemLp (g n) 2 μ) (hG : MemLp G 2 μ) (hφ : MemLp φ 2 μ)
    (hl : Tendsto (fun n => eLpNorm (fun x => g n x-G x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, g n x * φ x ∂μ) atTop (𝓝 (∫ x, G x * φ x ∂μ)) := by
  have ht := tendsto_integral_bounded_mul_L2 hg hG hφ hl
    (h := fun _ _ => (1 : ℝ)) (H := fun _ => (1 : ℝ))
    (fun _ => aestronglyMeasurable_const) (by norm_num : (0 : ℝ) ≤ 1)
    (fun _ => Eventually.of_forall (fun _ => by norm_num))
    (Eventually.of_forall (fun _ => tendsto_const_nhds))
  simpa only [one_mul] using ht

 theorem smooth_partial_commute {v : EuclideanPlane → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (x : EuclideanPlane) (i j : Fin 2) :
    fderiv ℝ (fun y => fderiv ℝ v y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) =
    fderiv ℝ (fun y => fderiv ℝ v y (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) x :=
    ((hv.contDiffAt.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num))
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
  exact hv.contDiffAt.isSymmSndFDerivAt (by simp) _ _

 theorem integral_compact_sobolev_jacobian_zero {u v : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (hv : DeGiorgi.MemW1pWitness 2 v univ)
    (hsv : HasCompactSupport v) :
    (∫ x, hu.weakGrad x 0 * hv.weakGrad x 1 - hu.weakGrad x 1 * hv.weakGrad x 0) = 0 := by
  have hvL : MemLp v 2 volume := by simpa only [Measure.restrict_univ] using hv.memLp
  let vₙ := planarMollification v
  have hsm (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (vₙ n) :=
    planarMollification_smooth (hvL.locallyIntegrable (by norm_num)) n
  have hs (n : ℕ) : HasCompactSupport (vₙ n) := planarMollification_hasCompactSupport hsv n
  have htest (n : ℕ) (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ (vₙ n) x (EuclideanSpace.single i 1)) :=
    (((hsm n).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const)
  have hidentity (n : ℕ) :
      (∫ x, hu.weakGrad x 0 * fderiv ℝ (vₙ n) x (EuclideanSpace.single 1 1)) =
      ∫ x, hu.weakGrad x 1 * fderiv ℝ (vₙ n) x (EuclideanSpace.single 0 1) := by
    have h0 := hu.isWeakGrad 0 _ (htest n 1) ((hs n).fderiv_apply (𝕜 := ℝ) _) (subset_univ _)
    have h1 := hu.isWeakGrad 1 _ (htest n 0) ((hs n).fderiv_apply (𝕜 := ℝ) _) (subset_univ _)
    simp only [Measure.restrict_univ] at h0 h1
    have he (x : EuclideanPlane) :
        fderiv ℝ (fun y => fderiv ℝ (vₙ n) y (EuclideanSpace.single 1 1)) x (EuclideanSpace.single 0 1) =
        fderiv ℝ (fun y => fderiv ℝ (vₙ n) y (EuclideanSpace.single 0 1)) x (EuclideanSpace.single 1 1) :=
      smooth_partial_commute (hsm n) x 0 1
    simp_rw [he] at h0
    linarith [h0, h1]
  have huG (i : Fin 2) : MemLp (fun x => hu.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hu.weakGrad_component_memLp i
  have hvG (i : Fin 2) : MemLp (fun x => hv.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hv.weakGrad_component_memLp i
  have ht (i j : Fin 2) := tendsto_integral_mul_of_L2
    (fun n => planarMollification_partial_memLp hv hsv n j) (hvG j) (huG i)
    (planarMollification_tendsto_gradient_L2 hv j)
  have ht' (i j : Fin 2) : Tendsto
      (fun n => ∫ x, hu.weakGrad x i * fderiv ℝ (vₙ n) x (EuclideanSpace.single j 1))
      atTop (𝓝 (∫ x, hu.weakGrad x i * hv.weakGrad x j)) := by
    simpa only [mul_comm] using ht i j
  have heq : (∫ x, hu.weakGrad x 0 * hv.weakGrad x 1) =
      ∫ x, hu.weakGrad x 1 * hv.weakGrad x 0 := by
    apply tendsto_nhds_unique (ht' 0 1)
    convert ht' 1 0 using 1
    funext n
    exact hidentity n
  have h01 : Integrable (fun x => hu.weakGrad x 0 * hv.weakGrad x 1) :=
    (huG 0).integrable_mul (hvG 1)
  have h10 : Integrable (fun x => hu.weakGrad x 1 * hv.weakGrad x 0) :=
    (huG 1).integrable_mul (hvG 0)
  rw [integral_sub h01 h10, heq, sub_self]

end CircleDomainRigidity

end

end OAI
