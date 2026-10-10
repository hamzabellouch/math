import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorTiming
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarCharacteristics
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PullbackMass
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorBumpMass

namespace OAI

/-! One smooth formula for the inviscid injection-and-stirring reference.
Its equation is proved for the prescribed block drift and source. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff

def detectorInjectionFraction (C L n : ℕ) (t : ℝ) : ℝ :=
  smoothRamp 0 1 ((t - 2 * ((n : ℝ) + 1)) / (duration C L n : ℝ))

def detectorInjectionRate (C L n : ℕ) (t : ℝ) : ℝ :=
  (duration C L n : ℝ)⁻¹ *
    smoothPulse 0 1 ((t - 2 * ((n : ℝ) + 1)) / (duration C L n : ℝ))

def detectorReference (Ψ : ℝ → ℝ → Plane → Plane) (C L n : ℕ)
    (t : ℝ) (x : Plane) : ℝ :=
  detectorInjectionFraction C L n t *
    pullbackScalar Ψ (detectorBump (width L n : ℝ)) (detectorPhase C L n t) x

theorem detectorInjectionFraction_smooth (C L n : ℕ) :
    ContDiff ℝ ∞ (detectorInjectionFraction C L n) :=
  (smoothRamp_smooth 0 1).comp ((contDiff_id.sub contDiff_const).div_const _)

theorem detectorInjectionFraction_hasDerivAt (C L n : ℕ) (t : ℝ) :
    HasDerivAt (detectorInjectionFraction C L n) (detectorInjectionRate C L n t) t := by
  change HasDerivAt (fun r => smoothRamp 0 1
    ((r - 2 * ((n : ℝ) + 1)) / (duration C L n : ℝ))) _ t
  have hr := ((smoothRamp_smooth 0 1).differentiable (by simp)
    ((t - 2 * ((n : ℝ) + 1)) / (duration C L n : ℝ))).hasDerivAt
  have ha := ((hasDerivAt_id t).sub_const (2 * ((n : ℝ) + 1))).div_const
    (duration C L n : ℝ)
  convert hr.comp t ha using 1 <;>
    simp only [detectorInjectionRate, smoothPulse, Function.comp_def, id_eq,
      div_eq_mul_inv, one_mul, mul_comm]

theorem detectorInjectionFraction_after (C L n : ℕ) {t : ℝ}
    (ht : 2 * ((n : ℝ) + 1) + (duration C L n : ℝ) ≤ t) :
    detectorInjectionFraction C L n t = 1 := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  apply smoothRamp_after (by norm_num : (0 : ℝ) < 1)
  apply (le_div_iff₀ hd).mpr
  linarith

theorem detectorReference_range (Ψ : ℝ → ℝ → Plane → Plane)
    (C L n : ℕ) (t : ℝ) (x : Plane) :
    detectorReference Ψ C L n t x ∈ Set.Icc (0 : ℝ) 1 := by
  have hθ := smoothRamp_range 0 1
    ((t - 2 * ((n : ℝ) + 1)) / (duration C L n : ℝ))
  have hg := detectorBump_range (by exact_mod_cast width_pos L n)
    (detector_width_small L n) (Ψ (detectorPhase C L n t) (-(detectorPhase C L n t)) x)
  exact ⟨mul_nonneg hθ.1 hg.1,
    (mul_le_mul hθ.2 hg.2 hg.1 (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (mul_one 1)⟩

theorem detectorReference_at_characteristic {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (C L n : ℕ) {t : ℝ}
    (ht : 2 * ((n : ℝ) + 1) + (duration C L n : ℝ) ≤ t) :
    detectorReference Ψ C L n t
      (Ψ 0 (detectorPhase C L n t) ![1 / 4, 1 / 4]) = 1 := by
  have hi : Ψ (detectorPhase C L n t) (-(detectorPhase C L n t))
      (Ψ 0 (detectorPhase C L n t) ![1 / 4, 1 / 4]) = ![1 / 4, 1 / 4] := by
    simpa only [zero_add] using hΨ.inverse_left 0 (detectorPhase C L n t) ![1 / 4, 1 / 4]
  rw [detectorReference, detectorInjectionFraction_after C L n ht, one_mul,
    pullbackScalar, hi]
  exact detectorBump_center (by exact_mod_cast width_pos L n) (detector_width_small L n)

theorem detectorRate_or_phase_zero (C L n : ℕ) (t : ℝ) :
    detectorInjectionRate C L n t = 0 ∨ detectorPhase C L n t = 0 := by
  by_cases ht : t ≤ 2 * ((n : ℝ) + 1) + (duration C L n : ℝ)
  · exact Or.inr (detectorPhase_before C L n ht)
  · left
    have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
    have ha : 1 ≤ (t - 2 * ((n : ℝ) + 1)) / (duration C L n : ℝ) := by
      apply (le_div_iff₀ hd).mpr
      linarith
    simp only [detectorInjectionRate,
      smoothPulse_after (by norm_num : (0 : ℝ) < 1) ha, mul_zero]

theorem detectorReference_smooth {Ψ : ℝ → ℝ → Plane → Plane}
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2))
    (C L n : ℕ) : ContDiff ℝ ∞ (Function.uncurry (detectorReference Ψ C L n)) := by
  have hg : ContDiff ℝ ∞ (detectorBump (width L n : ℝ)) :=
    detectorBump_smooth (by exact_mod_cast width_pos L n)
  have hθ : ContDiff ℝ ∞ (fun y : ℝ × Plane => detectorInjectionFraction C L n y.1) :=
    (detectorInjectionFraction_smooth C L n).comp contDiff_fst
  have hclock : ContDiff ℝ ∞ (fun y : ℝ × Plane => (detectorPhase C L n y.1, y.2)) :=
    ((detectorPhase_smooth C L n).comp contDiff_fst).prodMk contDiff_snd
  have hflow : ContDiff ℝ ∞ (fun y : ℝ × Plane =>
      Ψ (detectorPhase C L n y.1) (-(detectorPhase C L n y.1)) y.2) :=
    hback.comp hclock
  have hbump : ContDiff ℝ ∞ (fun y : ℝ × Plane =>
      detectorBump (width L n : ℝ)
        (Ψ (detectorPhase C L n y.1) (-(detectorPhase C L n y.1)) y.2)) :=
    hg.comp hflow
  exact hθ.mul hbump

theorem detectorReference_equation {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2))
    (C L n : ℕ) (t : ℝ) (x : Plane) :
    HasDerivAt (fun s => detectorReference Ψ C L n s x)
      (-fderiv ℝ (detectorReference Ψ C L n t) x
          (detectorDriftTerm V C L n (t, x)) + detectorSourceTerm C L n (t, x)) t := by
  let g := detectorBump (width L n : ℝ)
  let σ := detectorPhase C L n t
  let θ := detectorInjectionFraction C L n t
  have hg : ContDiff ℝ ∞ g := detectorBump_smooth (by exact_mod_cast width_pos L n)
  have hflow : ContDiff ℝ ∞ (fun y : Plane => Ψ σ (-σ) y) :=
    hback.comp (contDiff_const.prodMk contDiff_id)
  have hgs : ContDiff ℝ ∞ (pullbackScalar Ψ g σ) := hg.comp hflow
  have htrans : HasDerivAt (fun s => pullbackScalar Ψ g (detectorPhase C L n s) x)
      ((-fderiv ℝ (pullbackScalar Ψ g σ) x (V σ x)) * detectorSpeed C L n t) t := by
    have hd := pullbackScalar_transport hΨ hback hg (detectorPhase C L n t) x
    simpa only [Function.comp_def, σ] using
      HasDerivAt.comp (h := detectorPhase C L n) t hd (detectorPhase_hasDerivAt C L n t)
  have href := (detectorInjectionFraction_hasDerivAt C L n t).mul htrans
  have hspace := (hgs.differentiable (by simp) x).hasFDerivAt.const_mul θ
  have hD : fderiv ℝ (detectorReference Ψ C L n t) x
      (detectorDriftTerm V C L n (t, x)) =
      θ * (detectorSpeed C L n t * fderiv ℝ (pullbackScalar Ψ g σ) x (V σ x)) := by
    change fderiv ℝ (fun y => θ * pullbackScalar Ψ g σ y) x
      (detectorSpeed C L n t • V σ x) = _
    rw [hspace.fderiv]
    simp only [smul_apply, map_smul, smul_eq_mul]
    ring
  have hsource : detectorInjectionRate C L n t * pullbackScalar Ψ g σ x =
      detectorSourceTerm C L n (t, x) := by
    rcases detectorRate_or_phase_zero C L n t with hr | hp
    · simp only [hr, zero_mul]
      change 0 = detectorInjectionRate C L n t * g x
      rw [hr, zero_mul]
    · have he : pullbackScalar Ψ g σ x = g x := by
        simp only [σ, hp, pullbackScalar, neg_zero, hΨ.initial]
      rw [he]
      rfl
  convert href using 1
  · rfl
  · rw [hD, ← hsource]
    dsimp only [θ, σ]
    ring

theorem detectorReference_mass {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    (hV : ContDiff ℝ ∞ (Function.uncurry V))
    (hp : ∀ s, PlanePeriodic (V s))
    (hdiv : ∀ s x, PlanarHamiltonian.divergence (V s) x = 0)
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2))
    (C L n : ℕ) (t : ℝ) :
    0 ≤ (∫ x in Set.Icc (0 : Plane) (fun _ => 1), detectorReference Ψ C L n t x) ∧
    (∫ x in Set.Icc (0 : Plane) (fun _ => 1), detectorReference Ψ C L n t x) ≤
      4 * (width L n : ℝ) ^ 2 := by
  have hb : (0 : ℝ) < width L n := by exact_mod_cast width_pos L n
  have hmass := detectorBump_mass hb (detector_width_small L n)
  have he : (∫ x in Set.Icc (0 : Plane) (fun _ => 1), detectorReference Ψ C L n t x) =
      detectorInjectionFraction C L n t *
        ∫ x in Set.Icc (0 : Plane) (fun _ => 1), detectorBump (width L n : ℝ) x := by
    unfold detectorReference
    rw [MeasureTheory.integral_const_mul]
    rw [pullbackScalar_mass hΨ hV hp hdiv hback (detectorBump_smooth hb)
      (detectorBump_periodic (width L n : ℝ))]
  rw [he]
  have hθ := smoothRamp_range 0 1
    ((t - 2 * ((n : ℝ) + 1)) / (duration C L n : ℝ))
  exact ⟨mul_nonneg hθ.1 hmass.1,
    (mul_le_mul_of_nonneg_right hθ.2 hmass.1).trans (by simpa using hmass.2)⟩

end ForcedComputation.VelocityDetector

end

end OAI
