import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorReference
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorDivergence
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarMassSolution

namespace OAI

/-! The detector's actual scalar has the small total mass of the injected
bumps. Incompressible stirring and diffusion make no contribution. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory
open scoped ContDiff BigOperators

def detectorPartialMass (C L N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, detectorInjectionFraction C L n t *
    ∫ x in Icc (0 : Plane) (fun _ => 1), detectorBump (width L n : ℝ) x

theorem detectorPartialMass_continuous (C L N : ℕ) :
    Continuous (detectorPartialMass C L N) := by
  apply continuous_finsetSum
  intro n _
  exact (detectorInjectionFraction_smooth C L n).continuous.mul continuous_const

theorem detectorPartialMass_hasDerivAt (C L N : ℕ) (t : ℝ) :
    HasDerivAt (detectorPartialMass C L N)
      (∑ n ∈ Finset.range N, detectorInjectionRate C L n t *
        ∫ x in Icc (0 : Plane) (fun _ => 1), detectorBump (width L n : ℝ) x) t := by
  have hd := HasDerivAt.sum (u := Finset.range N) (fun n _ =>
    (detectorInjectionFraction_hasDerivAt C L n t).mul_const
      (∫ x in Icc (0 : Plane) (fun _ => 1), detectorBump (width L n : ℝ) x))
  convert hd using 1
  funext s
  simp only [Finset.sum_apply, detectorPartialMass]

theorem detectorPartialMass_zero (C L N : ℕ) : detectorPartialMass C L N 0 = 0 := by
  apply Finset.sum_eq_zero
  intro n _
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hh : (0 - 2 * ((n : ℝ) + 1)) / (duration C L n : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  simp only [detectorInjectionFraction,
    smoothRamp_before (by norm_num : (0 : ℝ) < 1) hh, zero_mul]

theorem detectorSource_mass (C L N : ℕ) {t : ℝ} (hN : t + 1 ≤ (N : ℝ)) :
    scalarMass (detectorSource C L) t =
      ∑ n ∈ Finset.range N, detectorInjectionRate C L n t *
        ∫ x in Icc (0 : Plane) (fun _ => 1), detectorBump (width L n : ℝ) x := by
  have he (x : Plane) : detectorSource C L t x =
      ∑ n ∈ Finset.range N, detectorSourceTerm C L n (t, x) :=
    (detectorBlockSum_local_of_time_bound _ (detectorSourceTerm_before C L)
      (t, x) N hN).eq_of_nhds
  unfold scalarMass
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n _
    change (∫ x in Icc (0 : Plane) (fun _ => 1),
      detectorInjectionRate C L n t * detectorBump (width L n : ℝ) x) = _
    exact integral_const_mul _ _
  · intro n _
    exact ((detectorSourceTerm_smooth C L n).continuous.comp
      (continuous_const.prodMk continuous_id)).integrableOn_Icc

theorem detectorPartialMass_bound (C L N : ℕ) (t : ℝ) :
    detectorPartialMass C L N t ≤ (massBound L : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, (4 : ℝ) * (width L n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n _
      have hm := detectorBump_mass (by exact_mod_cast width_pos L n)
        (detector_width_small L n)
      have hθ := smoothRamp_range 0 1
        ((t - 2 * ((n : ℝ) + 1)) / (duration C L n : ℝ))
      exact (mul_le_mul_of_nonneg_right hθ.2 hm.1).trans (by simpa using hm.2)
    _ ≤ ∑' n : ℕ, (4 : ℝ) * (width L n : ℝ) ^ 2 :=
      (total_injected_mass L).summable.sum_le_tsum _ (fun _ _ => by positivity)
    _ = (massBound L : ℝ) := (total_injected_mass L).tsum_eq

theorem detector_scalar_mass_bound
    {V : ℝ → Plane → Plane} (hV : ContDiff ℝ ∞ (Function.uncurry V))
    (hp : ∀ s, PlanePeriodic (V s))
    (hdiv : ∀ s x, PlanarHamiltonian.divergence (V s) x = 0)
    (C L : ℕ) {w : ℝ → Plane → ℝ}
    (hs : GlobalTorusScalarSolution 1 (detectorDrift V C L) (detectorSource C L)
      w (fun _ => 0)) (hw : ContDiff ℝ ∞ (Function.uncurry w))
    {t : ℝ} (ht : 0 ≤ t) : scalarMass w t ≤ (massBound L : ℝ) := by
  let N := ⌈t + 1⌉₊
  have hN : t + 1 ≤ (N : ℝ) := Nat.le_ceil _
  have hd (s : ℝ) (hs' : s ∈ Ico (0 : ℝ) t) :
      HasDerivAt (scalarMass w) (scalarMass (detectorSource C L) s) s :=
    hs.mass_hasDerivAt hw
      (fun s => (detectorDrift_smooth hV C L).comp (contDiff_const.prodMk contDiff_id))
      (detectorDrift_periodic hp C L) (detectorDrift_divergence hV hdiv C L)
      (fun s => (detectorSource_smooth C L).continuous.comp
        (continuous_const.prodMk continuous_id)) hs'.1
  have hg (s : ℝ) (hs' : s ∈ Ico (0 : ℝ) t) :
      HasDerivAt (detectorPartialMass C L N) (scalarMass (detectorSource C L) s) s := by
    rw [detectorSource_mass C L N (by linarith [hs'.2])]
    exact detectorPartialMass_hasDerivAt C L N s
  have hi : scalarMass w 0 = detectorPartialMass C L N 0 := by
    rw [detectorPartialMass_zero]
    simp only [scalarMass, (hs 0 le_rfl).initial, integral_zero]
  have he := eq_of_has_deriv_right_eq
    (fun s hs' => (hd s hs').hasDerivWithinAt)
    (fun s hs' => (hg s hs').hasDerivWithinAt)
    (scalarMass_continuous hw.continuous).continuousOn
    (detectorPartialMass_continuous C L N).continuousOn hi t ⟨ht, le_rfl⟩
  rw [he]
  exact detectorPartialMass_bound C L N t

end ForcedComputation.VelocityDetector

end

end OAI
