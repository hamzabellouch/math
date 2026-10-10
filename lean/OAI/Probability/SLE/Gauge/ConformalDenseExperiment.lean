import OAI.Probability.SLE.Gauge.SerpentineCenteredMass
import OAI.Probability.SLE.Gauge.SerpentineConformalGeometry

namespace OAI

/-! The actual dense experiment transported through an arbitrary inverse
chart. Its lower bound is uniform over normalized marked states and its
cutoff is proportional to the physical conformal radius. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates FirstFrontPassage FrontSuccessMeasurability

lemma segmentSausageCharge_le_stoppedWhole
    (κ : ℝ) (f : C(ℝ≥0, ℂ)) (T : ℝ≥0) (ρ : WithTop ℝ≥0)
    (hT : (T : WithTop ℝ≥0) ≤ ρ) (v : ℝ) (D : Set ℂ) :
    segmentSausageCharge κ f 0 T v D ≤ stoppedWholeSausageCharge κ f ρ v D := by
  cases hρ : ρ with
  | top =>
    simp only [stoppedWholeSausageCharge, stoppedAtPath, ite_true]
    apply mul_le_mul' le_rfl
    apply measure_mono
    rintro z ⟨hz, u, _hu, hdu⟩
    exact ⟨hz, u, by simpa only [dist_comm] using hdu⟩
  | coe t =>
    rw [stoppedWholeSausageCharge_finite]
    exact segmentSausageCharge_mono κ f le_rfl (WithTop.coe_le_coe.mp (hρ ▸ hT)) v Subset.rfl

namespace Serpentine
open Target

lemma dense_conformal_mass_threshold
    (κ A c h a : ℝ) (hκ : 0 < κ) (hA : 0 < A) (hc : 0 < c)
    (hh : 0 < h) (ha : 0 < a) (w : ℂ) (hwy : 0 < w.im) (hwn : ‖w‖ ≤ 1)
    (m : ℕ) :
    (A * c * (h / 20000) ^ dimension κ / 2 ^ dimension κ) *
        (2 * w.im * a) ^ dimension κ * (m : ℝ) ^ codimension κ ≤
      (A * a ^ dimension κ) * (c * (h / 20000) ^ dimension κ * (m : ℝ) ^ codimension κ) := by
  have hwi := (Complex.im_le_norm w).trans hwn
  have hr : (2 * w.im * a) ^ dimension κ ≤ 2 ^ dimension κ * a ^ dimension κ := by
    calc
      _ ≤ (2 * a) ^ dimension κ := Real.rpow_le_rpow (by positivity)
        (by nlinarith) (by dsimp [dimension]; positivity)
      _ = _ := Real.mul_rpow (by norm_num) ha.le
  have hbase : 0 ≤ A * c * (h / 20000) ^ dimension κ / 2 ^ dimension κ := by positivity
  have hm : 0 ≤ (m : ℝ) ^ codimension κ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    _ ≤ (A * c * (h / 20000) ^ dimension κ / 2 ^ dimension κ) *
        (2 ^ dimension κ * a ^ dimension κ) * (m : ℝ) ^ codimension κ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hbase) hm
    _ = _ := by field_simp

theorem uniform_conformal_dense_stopped_mass
    {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B μ)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport μ γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (hstraight : PublishedHalfPlaneCrosscutStraightening)
    (hexit : PublishedHalfPlaneConformalExitLaw)
    (hwiener : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ h b C : ℝ, 0 < h ∧ h ≤ s ∧ 0 < b ∧ 0 < C ∧
      ∃ δ : ℕ → ℝ, (∀ m, 0 < m → 0 < δ m) ∧
      ∀ (f : ℂ → ℂ) (w : ℂ), DifferentiableOn ℂ f upperHalfPlane →
        InjOn f upperHalfPlane → ‖w‖ = 1 → s ≤ w.im → deriv f w ≠ 0 →
        ∀ (η : Ω → ℝ≥0 → ℂ) (hη : ∀ ω, Continuous (η ω)),
        (∀ ω t, γ ω t ∈ closedBall w h → η ω t = f (γ ω t)) →
        ∀ ρ : Ω → WithTop ℝ≥0,
        (∀ᵐ ω ∂μ, ρ ω = radiusLevelTime (γ ω) (G ω) w (experimentRadiusLevel h)) →
        ∀ m : ℕ, 0 < m → ∀ v : ℝ, 0 < v →
        v < δ m * (2 * w.im * ‖deriv f w‖) →
        ENNReal.ofReal (Real.exp (-C * (m : ℝ) ^ 2)) ≤
          finiteCenteredLaw μ κ B γ G w (experimentRadiusLevel h)
            {ω | ENNReal.ofReal (b * (2 * w.im * ‖deriv f w‖) ^ dimension κ *
                (m : ℝ) ^ codimension κ) ≤
              stoppedWholeSausageCharge κ (sourceTracePath η hη ω) (ρ ω) v
                (closedBall (f w) (2 * w.im * ‖deriv f w‖))} := by
  obtain ⟨c, v₀, hcm, hv₀, hmass⟩ := uniform_serpentine_centered_stopped_mass μ κ hκ hκ8
    B hB hBm hc hB0 γ G F hw hcompact hboundary hsupport hplanar hstraight hexit hwiener W hW ε hε hεsmall
  obtain ⟨h, A, L, δ₀, hh, hhs, hA, hL, hδ₀, htransfer⟩ :=
    uniform_conformal_experiment_restricted_transfer κ hcompact hs hs1
  have hh1 := hhs.trans hs1
  obtain ⟨C, hC, hmass⟩ := hmass h hh hh1
  let b := A * c * (h / 20000) ^ dimension κ / 2 ^ dimension κ
  let δ := fun m => min δ₀ (L * (ribbonWidth (halfHeight h) m * v₀) / 2)
  refine ⟨h, b, C, hh, hhs, by dsimp [b]; positivity, hC, δ, ?_, ?_⟩
  · intro m hm
    have hwidth := fit_width_pos hh hm
    exact lt_min hδ₀ (by positivity)
  intro f w hf hfi hwn hwy hne η hη heq ρ hρ m hm v hv hvcut
  have hwh : h ≤ w.im := hhs.trans hwy
  have hwpos : 0 < w.im := hs.trans_le hwy
  have hnorm : 0 < ‖deriv f w‖ := norm_pos_iff.mpr hne
  have hwi : w.im ≤ 1 := (Complex.im_le_norm w).trans hwn.le
  have hvsource : 0 < v / (L * ‖deriv f w‖) := div_pos hv (mul_pos hL hnorm)
  have hvcut' : v / (L * ‖deriv f w‖) < ribbonWidth (halfHeight h) m * v₀ := by
    apply conformal_experiment_mesh_cutoff hL hnorm (mul_pos (fit_width_pos hh hm) hv₀) w hwi
    exact hvcut.trans_le (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  obtain ⟨g, hg⟩ := exists_global_ribbon_progress _ (physicalExperimentChart_closedEmbedding hh w hwh hm)
  let τ := ribbonFrontStop g γ (fitCompletion h w m)
  let E := RibbonStepSuccess γ (fun _ => 0) τ (physicalExperimentChart h w m) ε κ
    (v / (L * ‖deriv f w‖)) (c * (h / 20000) ^ dimension κ * (m : ℝ) ^ codimension κ)
    (closedBall (center h w) (h / 20))
  have hp : ENNReal.ofReal (Real.exp (-C * (m : ℝ) ^ 2)) ≤
      finiteCenteredLaw μ κ B γ G w (experimentRadiusLevel h) E :=
    hmass w hwn.le hwh m hm (v / (L * ‖deriv f w‖)) hvsource hvcut' g hg
  apply hp.trans
  apply measure_mono_ae
  apply (withDensity_absolutelyContinuous μ _).ae_le
  filter_upwards [hρ] with ω hρω hω
  have hpref : () ∈ GoodRibbonPrefix (fun _ : Unit => γ ω) (fun _ => τ ω)
      (physicalExperimentChart h w m) ε := hω.1
  have hbefore := (good_physicalExperiment_before_radius ((hc ω).const_mul _) (hw ω)
    hh w hwn.le hwh hm (τ ω) ε hpref).1
  have hTρ : (((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) ≤ ρ ω := by
    cases ht : τ ω with
    | top => exact (hpref.1 ht).elim
    | coe T =>
      simp only [ht, WithTop.untopD_coe] at hbefore ⊢
      rw [hρω]
      exact_mod_cast hbefore.le
  have htrans := htransfer f w hf hfi hwn hwy hne (γ ω) (η ω) 0 ((τ ω).untopD 0)
    (fun t _ ht => heq ω t ht) v hv
    (hvcut.trans_le (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)))
  have hthresh := dense_conformal_mass_threshold κ A c h ‖deriv f w‖ hκ hA hcm hh hnorm w
    (lt_of_lt_of_le hs hwy) hwn.le m
  calc
    _ ≤ ENNReal.ofReal (A * ‖deriv f w‖ ^ dimension κ) *
        ENNReal.ofReal (c * (h / 20000) ^ dimension κ * (m : ℝ) ^ codimension κ) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ A * ‖deriv f w‖ ^ dimension κ)]
      exact ENNReal.ofReal_le_ofReal hthresh
    _ ≤ ENNReal.ofReal (A * ‖deriv f w‖ ^ dimension κ) *
        segmentSausageCharge κ (γ ω) 0 ((τ ω).untopD 0) (v / (L * ‖deriv f w‖))
          (closedBall (center h w) (h / 20)) := mul_le_mul' le_rfl hω.2
    _ ≤ segmentSausageCharge κ (η ω) 0 ((τ ω).untopD 0) v
        (closedBall (f w) (2 * w.im * ‖deriv f w‖)) := htrans
    _ ≤ _ := segmentSausageCharge_le_stoppedWhole κ (sourceTracePath η hη ω) _ _ hTρ _ _

end Serpentine
end SLEExactGauge

end

end OAI
