import OAI.MeasureTheory.Falconer.Radial.RadialTestBound
import OAI.MeasureTheory.Falconer.Radial.MollifiedRadialBound

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceTestNorm_rpow_le_liminf (γ : Measure UnitCircle) (γn : ℕ → Measure UnitCircle)
    {p q : ℝ} (hp : 0 < p) (A : ℕ → ℝ≥0∞)
    (hγ : ∀ F : BoundedContinuousFunction UnitCircle ℝ,
      Tendsto (fun n => ∫ ω, F ω ∂γn n) atTop (𝓝 (∫ ω, F ω ∂γ)))
    (hA : ∀ n, (sourceTestNorm q (γn n))^p ≤ A n) :
    (sourceTestNorm q γ)^p ≤ liminf A atTop := by
  have he : (sourceTestNorm q γ)^p =
      ⨆ (F : BoundedContinuousFunction UnitCircle ℝ)
        (_ : eLpNorm F (ENNReal.ofReal q) sourceArcLength ≤ 1),
          (ENNReal.ofReal ‖∫ ω, F ω ∂γ‖)^p := by
    change (ENNReal.orderIsoRpow p hp) (⨆ (F : BoundedContinuousFunction UnitCircle ℝ), ⨆ _ : eLpNorm F (ENNReal.ofReal q) sourceArcLength ≤ 1,
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
  have hle (n : ℕ) : ENNReal.ofReal ‖∫ ω, F ω ∂γn n‖ ≤ sourceTestNorm q (γn n) :=
    le_iSup_of_le F (le_iSup_of_le hF le_rfl)
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall (fun n =>
    (ENNReal.rpow_le_rpow (hle n) hp.le).trans (hA n)))

theorem radial_testNorm_fatou (α β : Measure Plane) [IsFiniteMeasure α] [IsFiniteMeasure β]
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hx : ∀ᵐ x ∂β, ∀ᵐ y ∂α, y ≠ x) :
    (∫⁻ x, (sourceTestNorm q (α.map (sourceRadialUnit x)))^p ∂β) ≤
      liminf (fun n => ∫⁻ x, (∫⁻ θ in Ioc 0 (2*Real.pi),
        (sourceRadialDensity (fun y => ENNReal.ofReal
          (sourceSmoothDensity α (sourceMollifier (ε n) (hε n)) y)) x θ)^p) ∂β) atTop := by
  let a := fun n => sourceSmoothDensity α (sourceMollifier (ε n) (hε n))
  let A := fun n (x : Plane) => ∫⁻ θ in Ioc 0 (2*Real.pi),
    (sourceRadialDensity (fun y => ENNReal.ofReal (a n y)) x θ)^p
  have ha (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (a n) := sourceSmoothDensity_smooth α _
    (sourceMollifier_compact _ _) (sourceMollifier_smooth _ _)
  have hm (n : ℕ) : Measurable (A n) :=
    ((measurable_sourceRadialDensity_joint _ (ha n).continuous.measurable.ennreal_ofReal).pow_const p).lintegral_prod_right'
  have hpoint : ∀ᵐ x ∂β, (sourceTestNorm q (α.map (sourceRadialUnit x)))^p ≤
      liminf (fun n => A n x) atTop := by
    filter_upwards [hx] with x hx
    apply sourceTestNorm_rpow_le_liminf _ _ hpq.pos (fun n => A n x)
      (sourceMollification_radial_test_tendsto α hε hlim x hx)
    intro n
    have he := sourceSmoothDensity_measure α (sourceMollifier (ε n) (hε n))
      (sourceMollifier_compact (ε n) (hε n))
      (sourceMollifier_smooth (ε n) (hε n)).continuous (sourceMollifier_nonneg (ε n) (hε n))
    rw [he]
    exact sourceTestNorm_radial_density_rpow_le _ (ha n).continuous.measurable.ennreal_ofReal hpq x
  exact (lintegral_mono_ae hpoint).trans (lintegral_liminf_le hm)

end PlanarFalconer

end OAI
