import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.DyadicSourceTails
import OAI.Analysis.RieszRectifiability.Kernel.CommonHeightEquation
import OAI.Analysis.RieszRectifiability.Flatness.PlaneMeanCorrectionBump
import OAI.Analysis.RieszRectifiability.Kernel.InheritedDyadicTail
import OAI.Analysis.RieszRectifiability.Nets.HeightBallRadiusIndependence
import OAI.Analysis.RieszRectifiability.Flatness.IntrinsicDirectionalEquation

namespace OAI

/-!
# Intrinsic equations for a common limiting height

Dyadic source moment bounds supply the integrable tails needed to pass from
renormalized height equations to radius-independent pairings on the limiting plane.
The resulting common height retains local square integrability and fractional
energy bounds, represents a tempered distribution in intrinsic coordinates, and
annihilates directional derivatives of compactly supported smooth tests.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology SchwartzMap
open scoped NNReal ENNReal ContDiff

theorem exists_common_height_with_intrinsic_equation {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (a : Ambient d) (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (hplane : e = affinePlaneSection a L)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)] [∀ j, SFinite (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e))
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (σ j))
    (hlower : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (σ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support)
    (u : ℕ → Ambient d → ℝ) (Ku : ℝ≥0) (hu : ∀ j, LipschitzWith Ku (u j))
    (z : ℕ → Ambient d) (hz : ∀ j, ‖z j‖ ≤ 1)
    (hdiff : ∀ j x y, u j x - u j y = inner ℝ (z j) (x - y))
    (δ A v : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (σ j) (e 0) (A j) (v j))
    (hratio : Tendsto (fun j => v j / δ j) atTop (𝓝 0))
    (W : ℝ) (hW : ∀ j, |u j (e 0)| ≤ W)
    (hw : ∀ H j, MemLp (fun x => u j x / δ j) 2
      ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B₀ E₀ : ℕ → ℝ)
    (hB₀ : ∀ H j, (∫ x, (u j x / δ j) ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B₀ H)
    (henergy : ∀ H j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2)
      (((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H))))
    (hE₀ : ∀ H j, (∫ q : Ambient d × Ambient d,
      fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2
      ∂(((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball (e 0) ((2 : ℝ) ^ l), u j x ^ 2 ∂σ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
      (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
      (∀ H, Tendsto (fun j => ∫ x, (u (ρ j) x / δ (ρ j)) ^ 2
        ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H (ψ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport ψ →
        LipschitzWith J ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
        Tendsto (fun j => ∫ x, (u (ρ j) x / δ (ρ j)) * ψ x
          ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
          (𝓝 (∫ x, f x * ψ x
            ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
        (((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
          ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
        (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) f q.1 q.2
          ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
            ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H) ∧
      (∀ R : ℝ, 0 < R → IntegrableOn
        (fun x => |f x| * inverseDistancePow (p + 1 + 2) (e 0) x)
        (closedExterior (e 0) R) (coordinatePlaneMeasure e)) ∧
      (∀ (φ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport φ → LipschitzWith J φ →
        (∀ x, |φ x| ≤ (B : ℝ)) → (∫ x, φ x ∂coordinatePlaneMeasure e) = 0 →
        ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
          heightPairingOn (p + 1) (coordinatePlaneMeasure e) (e 0) (ball (e 0) R) f φ = 0) ∧
      ∃ T : 𝓢'(Ambient (p + 1), ℂ),
        (∀ ψ : 𝓢(Ambient (p + 1), ℂ),
          Integrable (fun x : Ambient (p + 1) => f (a + L x) • ψ x)
            (volume : Measure (Ambient (p + 1))) ∧
          T ψ = ∫ x : Ambient (p + 1), f (a + L x) • ψ x) ∧
        ∀ g : Ambient (p + 1) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
          ∀ v : Ambient (p + 1), ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
            heightPairingOn (p + 1) volume (0 : Ambient (p + 1)) (ball 0 R)
              (fun x => f (a + L x)) (fun x => fderiv ℝ g x v) = 0 := by
  obtain ⟨ρ, hρ, f, hfm, hf, hsecond, hmoment, hfenergy, hEq⟩ :=
    exists_common_height_with_renormalized_equations p e π K Q he hπ hleft σ hlocal C G hC hg
      hlower hdiam u Ku hu z hz hdiff δ A v hδ hA hosc hratio W hW hw B₀ E₀ hB₀ henergy hE₀
  have huL2 : ∀ l j, MemLp (u j) 2 ((σ j).restrict (ball (e 0) ((2 : ℝ) ^ l))) :=
    fun l j => lipschitz_height_memLp_on_ball (p + 1) G (σ j) (hg j)
      (u j) Ku (hu j) (e 0) ((2 : ℝ) ^ l) (by positivity)
  have hwL2 : ∀ l j, MemLp (fun x => u j x / δ j) 2 ((σ j).restrict (ball (e 0) ((2 : ℝ) ^ l))) := by
    intro l j
    obtain ⟨H, hH⟩ := (eventually_ball_subset_boundedProjectionRegion e π K Q hπ hleft ((2 : ℝ) ^ l)).exists
    exact MemLp.mono_measure (Measure.restrict_mono hH le_rfl) (hw H j)
  have hnorm : ∀ j l, l ≤ N j → (∫ x in ball (e 0) ((2 : ℝ) ^ l), (u j x / δ j) ^ 2 ∂σ j) ≤
      D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2 := by
    intro j l hl
    apply normalized_second_moment_bound ((σ j).restrict (ball (e 0) ((2 : ℝ) ^ l)))
      (u j) (δ j) _ (hδ j)
    convert! hsource j l hl using 1
    ring
  have hνg : GlobalUpperGrowth (p + 1) ((2 * (Q : ℝ)) ^ (p + 1)) (coordinatePlaneMeasure e) := by
    simpa only [Fintype.card_fin] using! coordinatePlaneMeasure_upper_growth e π
      he.continuous.measurable Q hπ hleft
  let := hνg.finite_on_compacts
  have hTail : ∀ R : ℝ, 0 < R → IntegrableOn
      (fun x => |f x| * inverseDistancePow (p + 1 + 2) (e 0) x)
      (closedExterior (e 0) R) (coordinatePlaneMeasure e) := by
    intro R hR
    exact limiting_height_tail_from_dyadic_source (p + 1) e π K Q hπ hleft
      (fun j => σ (ρ j)) (coordinatePlaneMeasure e) ((2 * (Q : ℝ)) ^ (p + 1)) hνg
      (fun j x => u (ρ j) x / δ (ρ j)) f hfm hf hsecond (fun j => N (ρ j))
      (hN.comp hρ.tendsto_atTop) D b hb0 hb2 (fun l j => hwL2 l (ρ j))
      (fun j l hl => hnorm (ρ j) l hl) R hR
  have hdata := local_height_data_on_balls (p + 1) e π K Q hπ hleft (coordinatePlaneMeasure e)
    f hf (fun H => (hfenergy H).1)
  have hCompact : ∀ (φ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport φ → LipschitzWith J φ →
      (∀ x, |φ x| ≤ (B : ℝ)) → (∫ x, φ x ∂coordinatePlaneMeasure e) = 0 →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        heightPairingOn (p + 1) (coordinatePlaneMeasure e) (e 0) (ball (e 0) R) f φ = 0 := by
    intro φ Jφ Bφ hcφ hφ hBφ hmean
    obtain ⟨H₀, hH₀two, hsupport⟩ := hcφ.isBounded.subset_closedBall_lt 2 (e 0)
    obtain ⟨q₀, hq₀⟩ := pow_unbounded_of_one_lt (2 * H₀) (by norm_num : (1 : ℝ) < 2)
    have hH₀ : 0 ≤ H₀ := by linarith
    let η := radialUnitCutoff (e 0) 1
    have hη := radialUnitCutoff_lipschitz (e 0) 1
    have hBη : ∀ x, |η x| ≤ (1 : ℝ≥0) := by
      intro x
      rw [abs_of_nonneg (radialUnitCutoff_bounds (e 0) 1 x).1]
      exact (radialUnitCutoff_bounds (e 0) 1 x).2
    have hsη : ∀ x, η x ≠ 0 → dist x (e 0) ≤ H₀ := by
      intro x hx
      exact (radialUnitCutoff_support_bound (e 0) 1 x hx).trans (by linarith)
    have he0 : e 0 = a := by rw [hplane]; simp [affinePlaneSection]
    have hbump : (∫ x, η x ∂coordinatePlaneMeasure e) ≠ 0 := by
      change (∫ x, radialUnitCutoff (e 0) 1 x ∂coordinatePlaneMeasure e) ≠ 0
      rw [he0, hplane]
      exact ne_of_gt (radialUnitCutoff_plane_integral_pos a L)
    have hDyadic : ∀ q : ℕ, q₀ ≤ q → heightPairingOn (p + 1) (coordinatePlaneMeasure e)
        (e 0) (ball (e 0) ((2 : ℝ) ^ q)) f φ = 0 := by
      intro q hq
      have hR : 0 < (2 : ℝ) ^ q := by positivity
      have hHR : 2 * H₀ ≤ (2 : ℝ) ^ q := hq₀.le.trans (pow_le_pow_right₀ (by norm_num) hq)
      obtain ⟨B, hGB, hshell⟩ := controlled_shell_moments_from_dyadic_balls (p + 1) σ (e 0) u δ N D b
        (G * 2 ^ (p + 1)) huL2 hsource q
      obtain ⟨hN', hlast'⟩ := dyadic_shifted_last_error_tendsto q N δ hN hlast
      obtain ⟨J, hJ⟩ := exists_nat_ge (2 * (2 : ℝ) ^ q * ((Q : ℝ) + 1))
      obtain ⟨Bfar, hBfar, _, hball⟩ := comparable_ball_moments_from_dyadic_control (p + 1) σ (e 0)
        (fun j x => u j x / δ j) N hN D b hwL2 hnorm (((K : ℝ) + 1) * ((J : ℝ) + 1))
        ((2 : ℝ) ^ q) ((2 * (Q : ℝ)) ^ (p + 1) * 2 ^ (p + 1)) hR
      exact (hEq H₀ ((2 : ℝ) ^ q) hH₀ hR hHR B b (fun j => N j - (q + 1))
        hGB hb0 hb2 hN' hlast' hshell φ η Jφ 1 Bφ 1 hφ hη hcφ
        (radialUnitCutoff_hasCompactSupport (e 0) 1) hBφ hBη
        (fun x hx => hsupport (subset_tsupport φ hx)) hsη hmean hbump).2 J Bfar hJ hBfar hball
    refine ⟨(2 : ℝ) ^ q₀, by positivity, ?_⟩
    intro R hR
    have hRp : 0 < R := (by positivity : 0 < (2 : ℝ) ^ q₀).trans_le hR
    have hsame := heightPairingOn_ball_independent_from_local_energy p ((2 * (Q : ℝ)) ^ (p + 1))
      (coordinatePlaneMeasure e) hνg (e 0) f φ hfm (fun T _ => (hdata T).1)
      (fun T _ => (hdata T).2) Jφ Bφ hφ hcφ hBφ hmean H₀ R ((2 : ℝ) ^ q₀)
      hH₀ hRp (by positivity) (hq₀.le.trans hR) hq₀.le
      (fun x hx => hsupport (subset_tsupport φ hx)) (hTail R hRp) (hTail _ (by positivity))
    exact hsame.trans (hDyadic q₀ le_rfl)

  have he0 : e 0 = a := by rw [hplane]; simp [affinePlaneSection]
  let : IsFiniteMeasure ((coordinatePlaneMeasure e).restrict (ball (e 0) 1)) :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) ((2 * (Q : ℝ)) ^ (p + 1))
      (coordinatePlaneMeasure e) hνg (e 0) 1 (by norm_num)
  have hnearOne : IntegrableOn f (ball a 1) (coordinatePlaneMeasure (affinePlaneSection a L)) := by
    have hi : IntegrableOn f (ball (e 0) 1) (coordinatePlaneMeasure e) :=
      (hdata 1).1.integrable (by norm_num)
    rw [he0, hplane] at hi
    exact hi
  have htailOne : IntegrableOn (fun x => |f x| * inverseDistancePow (p + 1 + 2) a x)
      (closedExterior a 1) (coordinatePlaneMeasure (affinePlaneSection a L)) := by
    have hi := hTail 1 (by norm_num)
    rw [he0, hplane] at hi
    exact hi
  obtain ⟨T, hT⟩ := exists_intrinsic_height_distribution_from_tail (p + 1 + 2) a L f hfm
    1 (by norm_num) hnearOne htailOne
  refine ⟨ρ, hρ, f, hfm, hf, hsecond, hmoment, hfenergy, hTail, hCompact, T, hT, ?_⟩
  intro g hc hg v
  apply intrinsic_directional_equation_of_ambient a L f _ g hc hg v
  intro φ J B hcφ hφ hB _ hmean
  have hm : (∫ x, φ x ∂coordinatePlaneMeasure e) = 0 := by
    simpa only [hplane] using! hmean
  have hi := hCompact φ J B hcφ hφ hB hm
  rw [he0, hplane] at hi
  exact hi

end

end RieszRectifiability

end OAI
