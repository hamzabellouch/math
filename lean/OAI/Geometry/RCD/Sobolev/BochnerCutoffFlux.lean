import OAI.Geometry.RCD.Harmonic.UnboundedCaccioppoli
import OAI.Geometry.RCD.Sobolev.GammaL2Bound
import OAI.Geometry.RCD.Sobolev.GoodLaplacianCutoff

namespace OAI

/-! # Integrating the full Bochner source against an actual Laplacian cutoff

The source is only Sobolev and L². Multiplication by the compact Lipschitz
cutoff gives an admissible test without a bounded-source assumption.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

theorem weakLaplacian_cutoff_source_flux (u d η : SobolevSpace μ Q)
    (hd : IsWeakLaplacian μ Q u (SobolevSpace.toLp μ Q d))
    {v : X → ℝ} {L B : ℝ≥0} (hv : LipschitzWith L v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (hη : SobolevSpace.toLp μ Q η =ᵐ[μ] v) :
    weightedGamma μ Q v u d =
      -(∫ x, v x*(SobolevSpace.toLp μ Q d x)^2 ∂μ)-
        weightedGamma μ Q (SobolevSpace.toLp μ Q d) u η := by
  let T := SobolevSpace.cutoffCLM μ Q hv hs hb hn d
  have hΓ := localGamma_memLp_of_bounded_gradient μ Q η u L
    (SobolevSpace.minimalSlope_le_lipschitz μ Q η hv hη)
  have hi₁ := (localGamma_memL1 μ Q u d).bdd_mul hv.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hi₂ : Integrable (fun x => SobolevSpace.toLp μ Q d x*localGamma μ Q u η x) μ := by
    apply ((Lp.memLp (SobolevSpace.toLp μ Q d)).integrable_mul hΓ).congr
    filter_upwards [localGamma_comm μ Q η u] with x hx
    change SobolevSpace.toLp μ Q d x*localGamma μ Q η u x = _
    rw [hx]
  have hleft : energyForm μ Q u T = weightedGamma μ Q v u d+
      weightedGamma μ Q (SobolevSpace.toLp μ Q d) u η := by
    rw [← integral_localGamma_eq_energyForm]
    change _ = (∫ x, v x*localGamma μ Q u d x ∂μ)+
      ∫ x, SobolevSpace.toLp μ Q d x*localGamma μ Q u η x ∂μ
    rw [← integral_add hi₁ hi₂]
    exact integral_congr_ae (localGamma_cutoffCLM_right μ Q d η u hv hs hb hn hη)
  have hright : inner ℝ (SobolevSpace.toLp μ Q d) (SobolevSpace.toLp μ Q T)=
      ∫ x, v x*(SobolevSpace.toLp μ Q d x)^2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [SobolevSpace.cutoffCLM_coe μ Q hv hs hb hn d] with x hx
    change SobolevSpace.toLp μ Q T x = _ at hx
    simp only [Real.inner_apply,hx]
    ring
  have hh := hd T
  rw [hleft,hright] at hh
  linarith only [hh]

theorem GoodLaplacianCutoff.bochner_source_identity
    {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (u d G : SobolevSpace μ Q)
    (hd : IsWeakLaplacian μ Q u (SobolevSpace.toLp μ Q d))
    (hG : SobolevSpace.toLp μ Q G =ᵐ[μ] localGamma μ Q u u) :
    -(1/2:ℝ)*energyForm μ Q G χ.sobolev-
        weightedGamma μ Q (SobolevSpace.toLp μ Q χ.sobolev) u d =
      (1/2:ℝ)*weightedGamma μ Q χ.laplacian u u+
        (∫ x, χ.weight x*(SobolevSpace.toLp μ Q d x)^2 ∂μ)+
        weightedGamma μ Q (SobolevSpace.toLp μ Q d) u χ.sobolev := by
  have hE : energyForm μ Q G χ.sobolev =
      -weightedGamma μ Q χ.laplacian u u := by
    rw [energyForm_comm,χ.weak_laplacian,L2.inner_def]
    congr 1
    apply integral_congr_ae
    filter_upwards [hG] with x hx
    simp only [Real.inner_apply,hx]
  have hχ : weightedGamma μ Q (SobolevSpace.toLp μ Q χ.sobolev) u d =
      weightedGamma μ Q χ.weight u d := by
    apply integral_congr_ae
    filter_upwards [χ.representative] with x hx
    rw [hx]
  have hf := weakLaplacian_cutoff_source_flux μ Q u d χ.sobolev hd (B := 1) χ.lipschitz
    (χ.hasCompactSupport μ Q) (fun x => by
      rw [abs_of_nonneg (χ.bounds x).1]; exact (χ.bounds x).2)
    (fun x => (χ.bounds x).1) χ.representative
  rw [hE,hχ,hf]
  ring

end RegularPointCoordinates

end

end OAI
