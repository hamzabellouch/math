import OAI.Geometry.RCD.Heat.HeatLocalBochnerMass
import OAI.Geometry.RCD.Sobolev.CanonicalHessianMassBound
import OAI.Geometry.RCD.Sobolev.BochnerMeasureFromSource
import OAI.Geometry.RCD.Heat.HeatGeneratorAmplitude
import OAI.Geometry.RCD.Harmonic.WeightedDirectionalVanishing

namespace OAI

/-! # Uniformly vanishing canonical Hessians of the actual harmonic heat approximations -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {n : ℕ} (hX : NoncollapsedRCD 0 n X) (hn : 2 ≤ n) (p : X)
  [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem heat_canonical_hessian_vanishes
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (d : Lp ℝ 2 (hausdorff n X))
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (U : X → ℝ) (L A : ℝ≥0) (hU : LipschitzWith L U) (hUc : HasCompactSupport U)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] U)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x| ≤ A)
    {R b : ℝ} (hR : 0 < R) (hb : 4*R < b)
    (hd0 : d =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => 0) (c : ℝ)
    (hc : localGamma (hausdorff n X) hX.quadratic u u
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => c)
    (t : ℕ → ℝ) (ht : ∀ k, 0 < t k) (ht0 : Tendsto t atTop (𝓝 0))
    (v : Y → SobolevSpace (hausdorff n X) hX.quadratic) (V : Y → X → ℝ)
    (Lv : ℝ≥0) (Av : Y → ℝ≥0) (hV : ∀ y, LipschitzWith Lv (V y))
    (hVc : ∀ y, HasCompactSupport (V y))
    (hv : ∀ y, SobolevSpace.toLp (hausdorff n X) hX.quadratic (v y) =ᵐ[hausdorff n X] V y)
    (hAv : ∀ y, ∀ᵐ x ∂hausdorff n X,
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic (v y) x| ≤ Av y)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ (hausdorff n X)) (Dφ : ℝ≥0)
    (hDφ : ∀ᵐ x ∂hausdorff n X, |φ x| ≤ Dφ)
    (J : ℕ → Y → Lp ℝ 1 ((hausdorff n X).restrict (closedBall p R)))
    (hJ : ∀ k y, IsCanonicalHeatHessian (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic (t k) (ht k)
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic u)) (v y) p R φ (J k y)) :
    TendstoUniformly (fun k y => ∫ x in closedBall p R, |J k y x| ∂hausdorff n X)
      (fun _ => 0) atTop := by
  let m := hausdorff n X
  let q := hX.quadratic
  let f := SobolevSpace.toLp m q u
  let w k := heatSobolev m q (t k) (ht k) f
  let D k := heatSobolevMap m q (t k/2) (half_pos (ht k))
    (-heatGeneratorAt m q (t k-t k/2) f)
  obtain ⟨G,σ,hσ,hG,hrep,hmass⟩ :=
    hX.heat_local_bochner_mass hn p u d hd U L A hU hUc hu hA hR hb hd0 c hc t ht ht0
  let (k : ℕ) : IsFiniteMeasure (σ k) := hσ k
  have hE : TendstoUniformly (fun k (_ : Y) => (σ k).real (closedBall p R)) (fun _ => 0) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro e he
    filter_upwards [Metric.tendsto_nhds.mp hmass e he] with k hk y
    simpa only [dist_comm] using hk
  apply tendstoUniformly_of_directional_bound
    (C := m.real (closedBall p R)) (M := ((Dφ:ℝ)*(Lv:ℝ)^2)^2)
    measureReal_nonneg (sq_nonneg _)
    (fun k y => integral_nonneg fun x => abs_nonneg _) hE
  intro k y a ha
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨hLip,-⟩ := hX.kernelHeat_bounded_regularity hn p hk f A hA (t k) (ht k)
  have hwr : SobolevSpace.toLp m q (w k) =ᵐ[m] kernelHeat m q hk (t k) f := by
    simpa only [w,heatSobolev_toLp] using (kernelHeat_represents_L2 m q hk (ht k) f).symm
  have hD : SobolevSpace.toLp m q (D k) = -heatGeneratorAt m q (t k) f :=
    heatTail_deriv_toLp m q (t k/2) (half_pos (ht k)) f (t k) (by linarith [ht k])
  let B : ℝ≥0 := ⟨(2*(n:ℝ)*(|0|+1/t k))*(A:ℝ),by have := ht k; positivity⟩
  have hdB : ∀ᵐ x ∂m, |SobolevSpace.toLp m q (D k) x| ≤ B := by
    rw [hD]
    filter_upwards [hX.heatGeneratorAt_amplitude hn p le_rfl f A hA (ht k),
      Lp.coeFn_neg (heatGeneratorAt m q (t k) f)] with x hx he
    rw [he]
    change |-(heatGeneratorAt m q (t k) f x)| ≤ (2*(n:ℝ)*(|0|+1/t k))*(A:ℝ)
    simpa only [abs_neg] using hx
  have hlap := bochner_measure_laplacian_of_source m q 0 (w k) (D k) (G k) (hG k) (σ k)
    (by
      intro ψ z hz hzc hzs hψ
      simpa only [zero_mul,sub_zero] using hrep k ψ z hz hzc hzs hψ)
  have hlap' : IsMeasureLaplacianOn m q (ball p (2*R)) (G k)
      (bochnerGramSource m q 0 (w k) (w k) (D k) (D k) (σ k).toSignedMeasure) := by
    intro ψ z hz hzc hzs hψ
    exact hlap ψ z hz hzc (hzs.trans (ball_subset_ball (by linarith))) hψ
  exact hX.canonical_hessian_young_bound hn p (w k) (D k) (G k)
    (heatTail_weak_laplacian m q (t k) (ht k) f) (kernelHeat m q hk (t k) f) _ A B
    hLip hwr (hX.bounded_heat_sobolev_data hn p f A hA (ht k)).1 hdB (hG k) hR (σ k) hlap'
    (v y) (V y) Lv (Av y) (hV y) (hVc y) (hv y) (hAv y) φ hφ Dφ hDφ (J k y) (hJ k y) ha

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
