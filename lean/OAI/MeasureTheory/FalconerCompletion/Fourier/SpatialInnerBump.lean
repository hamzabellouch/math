import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAmbient2

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell.SpatialFourierND
open Set Metric Filter
open scoped ContDiff Topology SchwartzMap

noncomputable def spatialInnerBump (d : ℕ) (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : (EuclideanSpace ℝ (Fin d))) :=
  ⟨δ/2, δ, half_pos hδ, half_lt_self hδ⟩

noncomputable def spatialOuterBump (d : ℕ) (L : ℝ) (hL : 0 < L) : ContDiffBump (0 : (EuclideanSpace ℝ (Fin d))) :=
  ⟨L, L+1, hL, by linarith⟩

noncomputable def spatialAnnulusKernel (d : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (z : (EuclideanSpace ℝ (Fin d))) : ℂ :=
  ↑(spatialOuterBump d L hL z * (1-spatialInnerBump d δ hδ z) * (‖z‖^j)⁻¹)

theorem spatialAnnulusKernel_smooth (d : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : ContDiff ℝ ∞ (spatialAnnulusKernel d δ L hδ hL j) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have he : spatialAnnulusKernel d δ L hδ hL j =ᶠ[𝓝 0] (fun _ => 0) := by
      filter_upwards [(spatialInnerBump d δ hδ).eventuallyEq_one] with z hz
      simp [spatialAnnulusKernel, hz]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hn : ContDiffAt ℝ ∞ (fun z : (EuclideanSpace ℝ (Fin d)) => (‖z‖^j)⁻¹) z :=
      ((contDiffAt_norm ℝ hz).pow j).inv (pow_ne_zero _ (norm_ne_zero_iff.mpr hz))
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (((spatialOuterBump d L hL).contDiffAt.mul
        (contDiffAt_const.sub (spatialInnerBump d δ hδ).contDiffAt)).mul hn)

theorem spatialAnnulusKernel_compact (d : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : HasCompactSupport (spatialAnnulusKernel d δ L hδ hL j) := by
  exact (((spatialOuterBump d L hL).hasCompactSupport.mul_right).mul_right).comp_left
    (map_zero Complex.ofRealCLM)

theorem spatialAnnulusKernel_eq (d : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) {z : (EuclideanSpace ℝ (Fin d))} (hz₁ : δ ≤ ‖z‖) (hz₂ : ‖z‖ ≤ L) :
    spatialAnnulusKernel d δ L hδ hL j z = ↑((‖z‖^j)⁻¹) := by
  have hi : spatialInnerBump d δ hδ z = 0 :=
    (spatialInnerBump d δ hδ).zero_of_le_dist (by simpa [spatialInnerBump] using hz₁)
  have ho : spatialOuterBump d L hL z = 1 :=
    (spatialOuterBump d L hL).one_of_mem_closedBall (by simpa [spatialOuterBump] using hz₂)
  simp [spatialAnnulusKernel, hi, ho]

noncomputable def spatialAnnulusSchwartz (d : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : 𝓢((EuclideanSpace ℝ (Fin d)), ℂ) :=
  (spatialAnnulusKernel_compact d δ L hδ hL j).toSchwartzMap
    (spatialAnnulusKernel_smooth d δ L hδ hL j)

end Attempt4PrefixShell.SpatialFourierND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell.SpatialFourierND
open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

noncomputable def spatialFourierCoeff (d : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : 𝓢((EuclideanSpace ℝ (Fin d)), ℂ) := 𝓕 (spatialAnnulusSchwartz d δ L hδ hL j)

noncomputable def spatialFourierCost (d : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : ℝ := ∫ ξ, ‖spatialFourierCoeff d δ L hδ hL j ξ‖

noncomputable def spatialFourierPhase (d : ℕ) (s : ℝ) (ξ x : (EuclideanSpace ℝ (Fin d))) : ℂ :=
  Complex.exp (↑(2*Real.pi*inner ℝ ξ (s⁻¹ • x))*Complex.I)

theorem spatialFourierCost_nonneg (d : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : 0 ≤ spatialFourierCost d δ L hδ hL j :=
  integral_nonneg (fun _ => norm_nonneg _)

@[fun_prop] theorem spatialFourierPhase_continuous (d : ℕ) (s : ℝ) :
    Continuous (fun z : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d)) => spatialFourierPhase d s z.1 z.2) := by
  unfold spatialFourierPhase
  fun_prop

theorem spatialFourierPhase_norm (d : ℕ) (s : ℝ) (ξ x : (EuclideanSpace ℝ (Fin d))) :
    ‖spatialFourierPhase d s ξ x‖ = 1 := by
  simp [spatialFourierPhase, Complex.norm_exp, Complex.mul_re]

theorem spatialFourierPhase_sub (d : ℕ) (s : ℝ) (ξ x y : (EuclideanSpace ℝ (Fin d))) :
    spatialFourierPhase d s ξ x * conj (spatialFourierPhase d s ξ y) =
      Complex.exp (↑(2*Real.pi*inner ℝ ξ (s⁻¹ • (x-y)))*Complex.I) := by
  simp only [spatialFourierPhase, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add, smul_sub,
    inner_sub_right, mul_sub, Complex.ofReal_sub]
  congr 1
  ring

theorem spatialFourierCoeff_integrable (d : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : Integrable (spatialFourierCoeff d δ L hδ hL j) :=
  (spatialFourierCoeff d δ L hδ hL j).integrable

theorem spatialFourierSeparation_integrable (d : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (x y : (EuclideanSpace ℝ (Fin d))) :
    Integrable (fun ξ => spatialFourierCoeff d δ L hδ hL j ξ *
      (spatialFourierPhase d s ξ x * conj (spatialFourierPhase d s ξ y))) := by
  have hx : Continuous (fun ξ => spatialFourierPhase d s ξ x) := by
    unfold spatialFourierPhase
    fun_prop
  have hy : Continuous (fun ξ => spatialFourierPhase d s ξ y) := by
    unfold spatialFourierPhase
    fun_prop
  apply (spatialFourierCoeff_integrable d δ L hδ hL j).norm.mono'
    ((spatialFourierCoeff d δ L hδ hL j).continuous.mul
      (hx.mul (Complex.continuous_conj.comp hy))).aestronglyMeasurable
  filter_upwards with ξ
  simp [spatialFourierPhase_norm]

theorem spatialFourierSeparation (d : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (x y : (EuclideanSpace ℝ (Fin d))) :
    (∫ ξ, spatialFourierCoeff d δ L hδ hL j ξ *
      (spatialFourierPhase d s ξ x * conj (spatialFourierPhase d s ξ y))) =
      spatialAnnulusKernel d δ L hδ hL j (s⁻¹ • (x-y)) := by
  have he := congrArg (fun f : 𝓢((EuclideanSpace ℝ (Fin d)), ℂ) => f (s⁻¹ • (x-y)))
    (show (𝓕⁻ (𝓕 (spatialAnnulusSchwartz d δ L hδ hL j) : 𝓢((EuclideanSpace ℝ (Fin d)), ℂ)) :
      𝓢((EuclideanSpace ℝ (Fin d)), ℂ)) = spatialAnnulusSchwartz d δ L hδ hL j from
      FourierTransform.fourierInv_fourier_eq _)
  simp only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq', smul_eq_mul] at he
  refine Eq.trans ?_ he
  apply integral_congr_ae
  filter_upwards with ξ
  rw [spatialFourierPhase_sub]
  exact mul_comm _ _

theorem spatialInverseDistance_separation (d : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) {s : ℝ} (hs : 0 < s) {x y : (EuclideanSpace ℝ (Fin d))}
    (hd₁ : δ ≤ dist x y / s) (hd₂ : dist x y / s ≤ L) :
    (↑((dist x y / s)^j)⁻¹ : ℂ) =
      ∫ ξ, spatialFourierCoeff d δ L hδ hL j ξ *
        (spatialFourierPhase d s ξ x * conj (spatialFourierPhase d s ξ y)) := by
  have hn : ‖s⁻¹ • (x-y)‖ = dist x y / s := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, dist_eq_norm, div_eq_inv_mul]
  rw [spatialFourierSeparation, spatialAnnulusKernel_eq d δ L hδ hL j
    (by rwa [hn]) (by rwa [hn]), hn, Complex.ofReal_inv]

end Attempt4PrefixShell.SpatialFourierND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell.SpatialFourierND
open MeasureTheory Filter
open scoped ComplexConjugate

noncomputable def spatialPairPhase (d : ℕ) (s : ℝ) (ξ : (EuclideanSpace ℝ (Fin d))) (z : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d))) : ℂ :=
  spatialFourierPhase d s ξ z.1 * conj (spatialFourierPhase d s ξ z.2)

@[fun_prop] theorem spatialPairPhase_continuous (d : ℕ) (s : ℝ) :
    Continuous (fun p : (EuclideanSpace ℝ (Fin d)) × ((EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d))) => spatialPairPhase d s p.1 p.2) := by
  unfold spatialPairPhase spatialFourierPhase
  fun_prop

theorem spatialPairPhase_norm (d : ℕ) (s : ℝ) (ξ : (EuclideanSpace ℝ (Fin d))) (z : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d))) :
    ‖spatialPairPhase d s ξ z‖ = 1 := by
  simp [spatialPairPhase, spatialFourierPhase_norm]

theorem spatialFourier_joint_integrable (d : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (μ : Measure ((EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d)))) [IsFiniteMeasure μ]
    (A : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d)) → ℂ) (hA : Measurable A) {C : ℝ}
    (hb : ∀ z, ‖A z‖ ≤ C) :
    Integrable (fun p : (EuclideanSpace ℝ (Fin d)) × ((EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d))) =>
      spatialFourierCoeff d δ L hδ hL j p.1 * (spatialPairPhase d s p.1 p.2 * A p.2))
      (volume.prod μ) := by
  have hm : AEStronglyMeasurable (fun p : (EuclideanSpace ℝ (Fin d)) × ((EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d))) =>
      spatialFourierCoeff d δ L hδ hL j p.1 * (spatialPairPhase d s p.1 p.2 * A p.2))
      (volume.prod μ) :=
    (spatialFourierCoeff d δ L hδ hL j).continuous.aestronglyMeasurable.comp_fst.mul
      ((spatialPairPhase_continuous d s).aestronglyMeasurable.mul
        hA.aestronglyMeasurable.comp_snd)
  apply (((spatialFourierCoeff_integrable d δ L hδ hL j).norm.comp_fst μ).mul_const C).mono' hm
  filter_upwards with p
  simp only [norm_mul, spatialPairPhase_norm, one_mul]
  exact mul_le_mul_of_nonneg_left (hb p.2) (norm_nonneg _)

theorem spatialFourier_integral_swap (d : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (μ : Measure ((EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d)))) [IsFiniteMeasure μ]
    (A : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d)) → ℂ) (hA : Measurable A) {C : ℝ}
    (hb : ∀ z, ‖A z‖ ≤ C) :
    (∫ z, spatialAnnulusKernel d δ L hδ hL j (s⁻¹ • (z.1-z.2)) * A z ∂μ) =
      ∫ ξ, spatialFourierCoeff d δ L hδ hL j ξ *
        ∫ z, spatialPairPhase d s ξ z * A z ∂μ := by
  have he (z : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d))) :
      spatialAnnulusKernel d δ L hδ hL j (s⁻¹ • (z.1-z.2)) * A z =
        ∫ ξ, spatialFourierCoeff d δ L hδ hL j ξ * (spatialPairPhase d s ξ z * A z) := by
    rw [← spatialFourierSeparation, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with ξ
    dsimp [spatialPairPhase]
    ring
  simp_rw [he]
  simpa only [integral_const_mul] using
    (integral_integral_swap (f := fun ξ z => spatialFourierCoeff d δ L hδ hL j ξ *
      (spatialPairPhase d s ξ z * A z))
      (spatialFourier_joint_integrable d δ L hδ hL j s μ A hA hb)).symm

end Attempt4PrefixShell.SpatialFourierND
end GraphLiteralSupport
end
end

end OAI
