import OAI.Geometry.RCD.Sobolev.RecoveredTestEnergy
import OAI.Geometry.RCD.Sobolev.InteriorSmoothTestBounds
import OAI.Geometry.RCD.Coordinates.NormalizedUniformL2
import OAI.Geometry.RCD.Sobolev.PoissonLocality

namespace OAI

/-! # Actual Dirichlet tests along a measured blow-up sequence

The tests lie in the original zero-boundary Sobolev spaces, converge in
normalized L2 to the prescribed Euclidean test and have uniformly bounded
rescaled energy. No Sobolev convergence input is assumed.
-/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.compact_test_recovery_sequence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S ρ a b : ℝ}
    (hρ : 0≤ρ) (hρa : ρ<a) (hab : a<b) (hbS : b<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεpos : ∀ k, 0≤ε k) (hε : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    {ψ : Euclidean n → ℝ} {M B : ℝ≥0} (hψ : LipschitzWith M ψ)
    (hψb : ∀ z, |ψ z|≤B) (hψ0 : ∀ z, ρ≤‖z‖ → ψ z=0) :
    ∃ N : ℕ, ∃ C : ℝ, 0≤C ∧ ∃ w : ∀ k : ℕ,
      SobolevSpace.dirichlet (hausdorff n X) hX.quadratic
        (ball (p (k+N)) (S*r (k+N))),
      (∀ k, r (k+N)^2*((hausdorff n X).real (ball (p (k+N)) (S*r (k+N))))⁻¹*
        (∫ x in ball (p (k+N)) (S*r (k+N)),
          localGamma (hausdorff n X) hX.quadratic (w k).val (w k).val x ∂hausdorff n X)≤C^2) ∧
      Tendsto (fun k => ((hausdorff n X).real (ball (p (k+N)) (S*r (k+N))))⁻¹*
        ∫ x in ball (p (k+N)) (S*r (k+N)),
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k).val x-ψ (v (k+N) x))^2
            ∂hausdorff n X) atTop (𝓝 0) := by
  have hS : 0<S := by linarith
  have hevent : ∀ᶠ k in atTop, ε k<1 ∧ ε k<(a-ρ)/3 :=
    (hε.eventually (Iio_mem_nhds zero_lt_one)).and
      (hε.eventually (Iio_mem_nhds (show 0<(a-ρ)/3 by linarith)))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  have hNk (k : ℕ) : ε (k+N)<1 ∧ 2*ε (k+N)<a-ρ := by
    have ht := hN (k+N) (Nat.le_add_left N k)
    exact ⟨ht.1,by linarith [ht.2]⟩
  have hrec (k : ℕ) := hX.compact_sobolev_test_recovery (hr (k+N)) hρ hρa hab hbS
    (hεpos (k+N)) (hNk k).2 B.coe_nonneg (hv (k+N)).metric hψ hψb hψ0
  choose w L hL hb hg he using hrec
  let C : ℝ := M+((B:ℝ)+M)/(b-a)
  have hC : 0≤C := add_nonneg M.coe_nonneg
    (div_nonneg (add_nonneg B.coe_nonneg M.coe_nonneg) (sub_pos.mpr hab).le)
  refine ⟨N,C,hC,w,?_,?_⟩
  · intro k
    apply hX.rescaled_test_energy_le (hr (k+N)) hS (w k).val (L k) _ (hg k)
    apply (hL k).trans
    dsimp only [C]
    exact add_le_add le_rfl (div_le_div_of_nonneg_right
      (add_le_add le_rfl (mul_le_of_le_one_right M.coe_nonneg (hNk k).1.le))
      (sub_pos.mpr hab).le)
  · let μ := hausdorff n X
    let ν := fun k => μ.restrict (ball (p (k+N)) (S*r (k+N)))
    let : ∀ k, IsFiniteMeasure (ν k) := fun k =>
      ⟨by simpa only [ν,Measure.restrict_apply_univ] using (hX.finiteOnBounded _ isBounded_ball)⟩
    have hmass (k : ℕ) : 0<(ν k).real univ := by
      change 0<(μ.restrict (ball (p (k+N)) (S*r (k+N)))).real univ
      rw [Measure.real,Measure.restrict_apply_univ]
      exact ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr (k+N)))).ne'
        (hX.finiteOnBounded _ isBounded_ball).ne
    let F := fun k x => SobolevSpace.toLp μ hX.quadratic (w k).val x-ψ (v (k+N) x)
    have hFm (k : ℕ) : AEStronglyMeasurable (F k) (ν k) :=
      ((Lp.aestronglyMeasurable (SobolevSpace.toLp μ hX.quadratic (w k).val)).sub
        (hψ.continuous.measurable.comp (hv (k+N)).measurable).aestronglyMeasurable).mono_measure
          Measure.restrict_le_self
    have hlim : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ᵐ x ∂ν k, |F k x|≤η := by
      intro η hη
      have ht := (hε.comp (tendsto_add_atTop_nat N)).const_mul (M:ℝ)
      simp only [mul_zero] at ht
      filter_upwards [ht.eventually (Iio_mem_nhds hη)] with k hk
      exact (he k).mono fun x hx => hx.trans hk.le
    simpa only [ν,Measure.real,Measure.restrict_apply_univ,F] using
      normalized_sq_mean_tendsto_zero ν hmass F hFm hlim

theorem NoncollapsedRCD.smooth_test_recovery_sequence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S : ℝ} (hS : 0<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεpos : ∀ k, 0≤ε k) (hε : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    {ψ : Euclidean n → ℝ} (hψ : InteriorSmoothTest n S ψ) :
    ∃ N : ℕ, ∃ C : ℝ, 0≤C ∧ ∃ w : ∀ k : ℕ,
      SobolevSpace.dirichlet (hausdorff n X) hX.quadratic
        (ball (p (k+N)) (S*r (k+N))),
      (∀ k, r (k+N)^2*((hausdorff n X).real (ball (p (k+N)) (S*r (k+N))))⁻¹*
        (∫ x in ball (p (k+N)) (S*r (k+N)),
          localGamma (hausdorff n X) hX.quadratic (w k).val (w k).val x ∂hausdorff n X)≤C^2) ∧
      Tendsto (fun k => ((hausdorff n X).real (ball (p (k+N)) (S*r (k+N))))⁻¹*
        ∫ x in ball (p (k+N)) (S*r (k+N)),
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k).val x-ψ (v (k+N) x))^2
            ∂hausdorff n X) atTop (𝓝 0) := by
  obtain ⟨ρ,hρ,hρS,M,B,hψL,hψB,hψ0⟩ := hψ.metric_bounds hS
  let a := (2*ρ+S)/3
  let b := (ρ+2*S)/3
  have hρa : ρ<a := by dsimp only [a]; linarith
  have hab : a<b := by dsimp only [a,b]; linarith
  have hbS : b<S := by dsimp only [b]; linarith
  exact hX.compact_test_recovery_sequence hρ.le hρa hab hbS p r ε v hr hεpos hε hv
    hψL hψB hψ0

theorem recovered_dirichlet_harmonic_pairing_zero (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {Ω : Set X} (hΩ : MeasurableSet Ω) {u : SobolevSpace μ hQ}
    (hu : IsSobolevHarmonicOn μ hQ Ω u) (w : SobolevSpace.dirichlet μ hQ Ω) :
    (∫ x in Ω, localGamma μ hQ u w.val x ∂μ)=0 := by
  rw [integral_localGamma_dirichlet μ hQ Ω hΩ u w]
  exact hu w.val w.property

end RegularPointCoordinates

end

end OAI
