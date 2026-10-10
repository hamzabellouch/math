import OAI.MeasureTheory.Falconer.Radial.AllDimensionalRadialTestBound
import OAI.MeasureTheory.Falconer.Radial.RadialAtomless
import OAI.MeasureTheory.Falconer.Radial.AllDimensionalMollifiedRadialBound

namespace OAI

/-! Passing the uniform smooth radial estimate to arbitrary finite-energy measures. -/
namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution

theorem surfaceTestNorm_rpow_le_liminf {d : ℕ} (γ : Measure (Space (d+1))) (γn : ℕ → Measure (Space (d+1)))
    {p q : ℝ} (hp : 0 < p) (A : ℕ → ℝ≥0∞)
    (hγ : ∀ F : BoundedContinuousFunction (Space (d+1)) ℝ,
      Tendsto (fun n => ∫ ω, F ω ∂γn n) atTop (𝓝 (∫ ω, F ω ∂γ)))
    (hA : ∀ n, (surfaceTestNorm q (γn n))^p ≤ A n) :
    (surfaceTestNorm q γ)^p ≤ liminf A atTop := by
  have he : (surfaceTestNorm q γ)^p =
      ⨆ (F : BoundedContinuousFunction (Space (d+1)) ℝ)
        (_ : eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1)) ≤ 1),
          (ENNReal.ofReal ‖∫ ω, F ω ∂γ‖)^p := by
    change (ENNReal.orderIsoRpow p hp) (⨆ (F : BoundedContinuousFunction (Space (d+1)) ℝ), ⨆ _ : eLpNorm F (ENNReal.ofReal q) (surfaceMeasure (d+1)) ≤ 1,
      ENNReal.ofReal ‖∫ ω, F ω ∂γ‖) = _
    rw [OrderIso.map_iSup]
    congr 1
    funext F
    exact (ENNReal.orderIsoRpow p hp).map_iSup _
  rw [he]
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have ht := ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp
    ((ENNReal.continuous_ofReal.tendsto _).comp (hγ F).norm)
  have hle (n : ℕ) : ENNReal.ofReal ‖∫ ω, F ω ∂γn n‖ ≤ surfaceTestNorm q (γn n) :=
    le_iSup_of_le F (le_iSup_of_le hF le_rfl)
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall (fun n =>
    (ENNReal.rpow_le_rpow (hle n) hp.le).trans (hA n)))

theorem euclidean_radial_testNorm_fatou {d : ℕ}
    (α β : Measure (Space (d+1))) [IsFiniteMeasure α] [IsFiniteMeasure β]
    [NullSingletonClass α] {ε : ℕ → ℝ} (hε : ∀ k, 0 < ε k)
    (hlim : Tendsto ε atTop (𝓝 0)) {p q : ℝ} (hpq : p.HolderConjugate q) :
    (∫⁻ x, (surfaceTestNorm q (α.map (radialDirection x)))^p ∂β) ≤
      liminf (fun k => ∫⁻ x, ∫⁻ w : Sphere (d+1),
        (euclideanRadialDensity (fun y => ENNReal.ofReal
          (euclideanSmoothDensity α (euclideanMollifier (ε k) (hε k)) y)) x w)^p
          ∂sphereMeasure (d+1) ∂β) atTop := by
  let a := fun k => euclideanSmoothDensity α (euclideanMollifier (ε k) (hε k))
  let A := fun k (x : Space (d+1)) => ∫⁻ w : Sphere (d+1),
    (euclideanRadialDensity (fun y => ENNReal.ofReal (a k y)) x w)^p ∂sphereMeasure (d+1)
  have ha (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (a k) := euclideanSmoothDensity_smooth α _
    (euclideanMollifier_compact _ _) (euclideanMollifier_smooth _ _)
  have hm (k : ℕ) : Measurable (A k) :=
    ((euclideanRadialDensity_joint_measurable _
      (ha k).continuous.measurable.ennreal_ofReal).pow_const p).lintegral_prod_right'
  have hpoint : ∀ᵐ x ∂β, (surfaceTestNorm q (α.map (radialDirection x)))^p ≤
      liminf (fun k => A k x) atTop := by
    filter_upwards with x
    apply surfaceTestNorm_rpow_le_liminf _ _ hpq.pos (fun k => A k x)
      (euclideanMollification_radial_test_tendsto α hε hlim x (by rw [ae_iff]; simp))
    intro k
    rw [euclideanSmoothDensity_measure α _ (euclideanMollifier_compact _ _)
      (euclideanMollifier_smooth _ _).continuous (euclideanMollifier_nonneg _ _)]
    exact surfaceTestNorm_radial_density_rpow_le _ (ha k).continuous.measurable.ennreal_ofReal hpq x
  exact (lintegral_mono_ae hpoint).trans (lintegral_liminf_le (u := (atTop : Filter ℕ)) hm)

end Falconer

end OAI
