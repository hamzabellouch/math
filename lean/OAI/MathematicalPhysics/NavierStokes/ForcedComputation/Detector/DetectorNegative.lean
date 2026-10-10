import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorPositive
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorSeparation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorOldMass
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.HeatComparison

namespace OAI

/-! The full-orbit clearance excludes detection on both the stirring
interval and the heat-only interval, hence at every nonnegative time. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

attribute [local irreducible] detectorReference

theorem scalar_slice_smooth {f : ℝ → Plane → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (S : ℝ) : ContDiff ℝ ∞ (f S) := by
  exact hf.comp (show ContDiff ℝ ∞ (fun y : Plane => (S, y)) from
    contDiff_const.prodMk contDiff_id)

theorem scalar_heat_wait_comparison (hK : TorusHeatInput)
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hs : GlobalTorusScalarSolution 1 a h w (fun _ => 0))
    (hw : ContDiff ℝ ∞ (Function.uncurry w))
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hz : ∀ r ∈ Icc (0 : ℝ) T, ∀ y, a (S + r) y = 0 ∧ h (S + r) y = 0)
    {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (hgp : PlanePeriodic g)
    {E : ℝ} (he : ∀ y, |w S y - g y| ≤ E)
    {t : ℝ} (ht : t - S ∈ Icc (0 : ℝ) T) (x : Plane) :
    |w t x - torusHeatEvolution g (t - S) x| ≤ E := by
  have hheat := hs.heat_window hK hw hS hT
    (fun r hr => funext (fun y => (hz r hr y).1))
    (fun r hr => funext (fun y => (hz r hr y).2)) (t - S) ht
  rw [show S + (t - S) = t by ring] at hheat
  have hws : ContDiff ℝ ∞ (w S) := hw.comp (contDiff_const.prodMk contDiff_id)
  have hc := torusHeatEvolution_stability hK hws hg
    ((hs S hS).periodic S ⟨hS, le_rfl⟩) hgp he ht.1 x
  rw [congrFun hheat x]
  exact hc

section Observation
variable {V : ℝ → Plane → Plane} {Ψ : ℝ → ℝ → Plane → Plane}
  (hK : TorusHeatInput) (hΨ : IsPlanarTransition V Ψ) (hv : PlanarVariations V Ψ)
  (hV : ContDiff ℝ ∞ (Function.uncurry V)) (hp : ∀ s, PlanePeriodic (V s))
  (hdiv : ∀ s x, PlanarHamiltonian.divergence (V s) x = 0)
  (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ψ y.1 (-y.1) y.2))
  (C L : ℕ) (h₁ : ∀ s x, ‖fderiv ℝ (euclideanMap (V s)) x‖ ≤ (L : ℝ))
  {w : ℝ → Plane → ℝ}
  (hs : GlobalTorusScalarSolution 1 (detectorDrift V C L) (detectorSource C L)
    w (fun _ => 0)) (hw : ContDiff ℝ ∞ (Function.uncurry w))
  (hlap : ∀ n t, t ∈ Icc (0 : ℝ) (2 * (duration C L n : ℝ)) → ∀ x,
    |scalarLaplacian (detectorReference Ψ C L n (2 * ((n : ℝ) + 1) + t)) x| ≤
      (laplacianBound C L n : ℝ))
  {E : Set Plane}
  (hfar : ∀ s, 0 ≤ s → ∀ x ∈ E,
    1 / 16 ≤ torusNorm (Ψ 0 s ![1 / 4, 1 / 4] - x))

include hK hΨ hv hV hp hdiv hback h₁ hs hw hlap hfar

theorem detector_negative_burst (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (2 * ((n : ℝ) + 1))
      (2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ))) {x : Plane} (hx : x ∈ E) :
    w t x < 1 / 2 := by
  have hi := detector_scalar_at_start_bound hK hV hp hdiv C L hs hw n
  have hτ : t - 2 * ((n : ℝ) + 1) ∈ Icc (0 : ℝ) (2 * (duration C L n : ℝ)) :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have he := detectorBurst_comparison hΨ hp hback C L n hs hw (hlap n) hi
    (t - 2 * ((n : ℝ) + 1)) hτ x
  rw [show 2 * ((n : ℝ) + 1) + (t - 2 * ((n : ℝ) + 1)) = t by ring] at he
  have hz := detectorReference_zero_on_target hΨ hv
    (fun s => hV.comp (contDiff_const.prodMk contDiff_id)) hp C L n h₁ hfar t hx
  rw [hz, sub_zero] at he
  have hm := detector_old_mass_margin L
  have hu := (abs_lt.mp he).2
  linarith

omit hv h₁ hfar in
theorem detector_error_at_burst_end (n : ℕ) (y : Plane) :
    |w (2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ)) y -
      detectorReference Ψ C L n (2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ)) y| ≤
      16 * (massBound L : ℝ) + 1 / 16 := by
  have hi := detector_scalar_at_start_bound hK hV hp hdiv C L hs hw n
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  exact (detectorBurst_comparison hΨ hp hback C L n hs hw (hlap n) hi
    (2 * (duration C L n : ℝ)) ⟨by positivity, le_rfl⟩ y).le

omit hv h₁ hfar in
theorem detector_wait_error (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ))
      (2 * ((n : ℝ) + 2))) (x : Plane) :
    |w t x - torusHeatEvolution
      (detectorReference Ψ C L n (2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ)))
      (t - (2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ))) x| ≤
        16 * (massBound L : ℝ) + 1 / 16 := by
  let S : ℝ := 2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ)
  let T : ℝ := 2 - 2 * (duration C L n : ℝ)
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  have hδ := detector_duration_real_le C L n
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hT : 0 ≤ T := by dsimp only [T]; linarith only [hδ]
  have hτ : t - S ∈ Icc (0 : ℝ) T := by
    constructor
    · dsimp only [S]; linarith only [ht.1]
    · dsimp only [S, T]; linarith only [ht.2]
  have hz (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) (y : Plane) :
      detectorDrift V C L (S + r) y = 0 ∧ detectorSource C L (S + r) y = 0 := by
    apply detector_wait_coefficients_zero V C L n
    constructor
    · dsimp only [S]; linarith only [hr.1]
    · dsimp only [S, T] at hr ⊢; linarith only [hr.2]
  have he (y : Plane) : |w S y - detectorReference Ψ C L n S y| ≤
      16 * (massBound L : ℝ) + 1 / 16 :=
    detector_error_at_burst_end hK hΨ hV hp hdiv hback C L hs hw hlap n y
  have hgs : ContDiff ℝ ∞ (detectorReference Ψ C L n S) :=
    scalar_slice_smooth (detectorReference_smooth hback C L n) S
  exact scalar_heat_wait_comparison hK
    (a := detectorDrift V C L) (h := detectorSource C L) (w := w)
    hs hw (S := S) (T := T) hS hT hz
    (g := detectorReference Ψ C L n S) hgs
    (detectorReference_periodic hΨ hp C L n S) he hτ x

omit hs hw hlap in
theorem detector_reference_heat_small (n : ℕ) (S : ℝ) {τ : ℝ} (hτ : 0 < τ)
    {x : Plane} (hx : x ∈ E) :
    torusHeatEvolution (detectorReference Ψ C L n S) τ x ≤
      1000000000 * (massBound L : ℝ) := by
  have hr := detectorReference_heat_bound hK hΨ hv hV hp hdiv hback C L n h₁ hfar S hτ hx
  have hm : 4 * (width L n : ℝ) ^ 2 ≤ (massBound L : ℝ) := by
    have hsum := (total_injected_mass L).summable.sum_le_tsum {n} (fun _ _ => by positivity)
    simp only [Finset.sum_singleton] at hsum
    exact hsum.trans_eq (total_injected_mass L).tsum_eq
  exact hr.trans (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 1000000000))

theorem detector_negative_wait (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ))
      (2 * ((n : ℝ) + 2))) {x : Plane} (hx : x ∈ E) : w t x < 1 / 2 := by
  let S : ℝ := 2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ)
  by_cases heq : t = S
  · subst t
    have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
    exact detector_negative_burst hK hΨ hv hV hp hdiv hback C L h₁ hs hw hlap hfar n
      ⟨by change 2 * ((n : ℝ) + 1) ≤ 2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ)
          linarith only [hd], le_rfl⟩ hx
  have hτ : 0 < t - S := sub_pos.mpr (lt_of_le_of_ne ht.1 (Ne.symm heq))
  have hc := detector_wait_error hK hΨ hV hp hdiv hback C L hs hw hlap n ht x
  have hr := detector_reference_heat_small hK hΨ hv hV hp hdiv hback C L h₁ hfar n S hτ hx
  have hu := (abs_le.mp hc).2
  have hmarg := detector_wait_margin L (H := (1000000000 : ℝ)) le_rfl
  change torusHeatEvolution (detectorReference Ψ C L n S) (t - S) x ≤ _ at hr
  change w t x - torusHeatEvolution (detectorReference Ψ C L n S) (t - S) x ≤ _ at hu
  linarith only [hu, hr, hmarg]

theorem detector_negative_all_time {t : ℝ} (ht : 0 ≤ t) {x : Plane} (hx : x ∈ E) :
    w t x < 1 / 2 := by
  by_cases hsmall : t ≤ 2
  · rw [detector_scalar_before_two C L hs ⟨ht, hsmall⟩ x]
    norm_num
  have htwo : 2 ≤ t := (lt_of_not_ge hsmall).le
  let k : ℕ := ⌊t / 2⌋₊
  have hk : 1 ≤ k := by
    apply Nat.le_floor
    norm_num only [Nat.cast_one]
    linarith
  let n := k - 1
  have hnk : n + 1 = k := Nat.sub_add_cancel hk
  have hncast : (n : ℝ) + 1 = (k : ℝ) := by exact_mod_cast hnk
  have hlo := Nat.floor_le (by positivity : 0 ≤ t / 2)
  have hhi := Nat.lt_floor_add_one (t / 2)
  have hblock : t ∈ Icc (2 * ((n : ℝ) + 1)) (2 * ((n : ℝ) + 2)) := by
    change (k : ℝ) ≤ t / 2 at hlo
    change t / 2 < (k : ℝ) + 1 at hhi
    constructor <;> linarith
  by_cases hb : t ≤ 2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ)
  · exact detector_negative_burst hK hΨ hv hV hp hdiv hback C L h₁ hs hw hlap hfar n
      ⟨hblock.1, hb⟩ hx
  · exact detector_negative_wait hK hΨ hv hV hp hdiv hback C L h₁ hs hw hlap hfar n
      ⟨(lt_of_not_ge hb).le, hblock.2⟩ hx

end Observation
end ForcedComputation.VelocityDetector

end

end OAI
