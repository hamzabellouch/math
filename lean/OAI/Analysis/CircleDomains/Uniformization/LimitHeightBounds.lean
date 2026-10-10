import OAI.Analysis.CircleDomains.Sobolev.HeightEnergyModulus
import OAI.Analysis.CircleDomains.Topology.HomeomorphicHeightBounds
import OAI.Analysis.CircleDomains.Selection.ExteriorDecay
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

namespace OAI

/-! The quantitative local and exterior bounds survive in the actual
locally uniform height limit. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem limit_height_exterior_bound
    (harea : ExteriorCoefficientAreaTheorem)
    (φ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ}
    (hv : TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop)
    {R : ℝ} (hR : 0 < R)
    (hh : ∀ n, DifferentiableOn ℂ (φ n) {z | R < ‖z‖})
    (hnorm : ∀ n, (fun z => φ n z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z : ℂ, 2*R ≤ ‖z‖ → |v z-z.im| ≤ 2*R^2/‖z‖ := by
  intro z hz
  have hp : Tendsto (fun n => (φ n z).im) atTop (𝓝 (v z)) :=
    hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  apply le_of_tendsto ((hp.sub_const z.im).abs)
  apply Eventually.of_forall
  intro n
  calc
    |(φ n z).im-z.im| = |(φ n z-z).im| := by rw [Complex.sub_im]
    _ ≤ ‖φ n z-z‖ := Complex.abs_im_le_norm _
    _ ≤ _ := harea.scaled_exterior_decay hR (hh n) (φ n).injective.injOn (hnorm n) z hz

 theorem limit_height_local_bound
    (harea : ExteriorCoefficientAreaTheorem)
    (φ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ}
    (hv : TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop)
    {R S : ℝ} (hR : 0 < R) (hS : 2*R ≤ S)
    (hh : ∀ n, DifferentiableOn ℂ (φ n) {z | R < ‖z‖})
    (hnorm : ∀ n, (fun z => φ n z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z ∈ closedBall (0 : ℂ) S, |v z| ≤ S+R := by
  intro z hz
  have hp : Tendsto (fun n => (φ n z).im) atTop (𝓝 (v z)) :=
    hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  apply le_of_tendsto hp.abs
  exact Eventually.of_forall (fun n =>
    normalized_homeomorphic_height_bound harea hR hS (hh n) (hnorm n) z hz)

 theorem limit_height_log_bound
    (φ : ℕ → ℂ ≃ₜ ℂ)
    (D : ∀ n, PlaneLocalWeakComplex (fun p => φ n (complexPlaneCoordinates p)))
    {v : ℂ → ℝ} (hv : TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop)
    {B : ℝ}
    (hI : ∀ n, Integrable (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2))
    (hB : ∀ n, (∫ p, (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2) ≤ B)
    (c : ℂ) {r R T : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hT : ‖c‖+R < T)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    |v x-v y|^2*Real.log (R/r) ≤
      16*Real.pi*(2*B+2*(volume (ball (0 : EuclideanPlane) T)).toReal) := by
  have hp (z : ℂ) : Tendsto (fun n => (φ n z).im) atTop (𝓝 (v z)) :=
    hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  apply le_of_tendsto ((((hp x).sub (hp y)).abs.pow 2).mul_const _)
  exact Eventually.of_forall (fun n =>
    height_log_bound_from_error (φ n) c (D n) hr hrR hT (hI n) (hB n) hx hy)

end CircleDomainRigidity

end

end OAI
