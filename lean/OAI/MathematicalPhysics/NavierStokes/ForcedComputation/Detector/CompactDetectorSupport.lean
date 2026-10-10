import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorGeneral
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorForceSupport
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorSupport

namespace OAI

/-! The arbitrary-center force is supported in the spatial support of
the input processor together with one fixed small torus neighborhood. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CompactCenter
open ShearFlows Set
open scoped ContDiff Topology

theorem torusNorm_lipschitz : LipschitzWith 2 torusNorm := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy : torusNorm x ≤ torusNorm (x - y) + torusNorm y := by
    simpa only [sub_add_cancel] using torusNorm_add_le (x - y) y
  have hyx : torusNorm y ≤ torusNorm (x - y) + torusNorm x := by
    have he : y - x = -(x - y) := by abel
    calc
      _ = torusNorm ((y - x) + x) := by rw [sub_add_cancel]
      _ ≤ torusNorm (y - x) + torusNorm x := torusNorm_add_le _ _
      _ = _ := by rw [he, torusNorm_neg]
  have ht : |torusNorm x - torusNorm y| ≤ torusNorm (x - y) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_ofNat] using
    ht.trans ((torusNorm_le_norm (x - y)).trans (planeCoordinates_symm_norm_le (x - y)))

def processorSupport (V : ℝ → Plane → Plane) : Set Plane :=
  closure {x | ∃ s, V s x ≠ 0}

def injectionNeighborhood (p : Plane) : Set Plane :=
  {x | torusNorm (x - p) ≤ 1 / 16}

theorem injectionNeighborhood_closed (p : Plane) : IsClosed (injectionNeighborhood p) :=
  isClosed_le (torusNorm_lipschitz.continuous.comp (continuous_id.sub continuous_const))
    continuous_const

theorem injectionNeighborhood_contains (p : Plane) : p ∈ injectionNeighborhood p := by
  change torusNorm (p - p) ≤ 1 / 16
  have hz : torusNorm (0 : Plane) = 0 := by
    apply le_antisymm
    · simpa only [map_zero, norm_zero] using torusNorm_le_norm (0 : Plane)
    · exact torusNorm_nonneg _
  rw [sub_self, hz]
  norm_num

theorem processor_zero_outside {V : ℝ → Plane → Plane} {x : Plane}
    (hx : x ∉ processorSupport V) (s : ℝ) : V s x = 0 := by
  by_contra hn
  exact hx (subset_closure (show x ∈ {y | ∃ s, V s y ≠ 0} from ⟨s, hn⟩))

theorem centered_bump_zero_outside (p : Plane) (L n : ℕ) {x : Plane}
    (hx : x ∉ injectionNeighborhood p) :
    detectorBump (width L n : ℝ) (x + -centerShift p) = 0 := by
  by_contra hn
  obtain ⟨k, hk⟩ := detectorBump_near_lift (by exact_mod_cast width_pos L n)
    (detector_width_small L n) hn
  have ht : torusNorm (x - p) ≤ 2 * (width L n : ℝ) := by
    have he : x - p = x + -centerShift p - ![1 / 4, 1 / 4] := by
      unfold centerShift
      abel
    rw [he]
    apply (torusNorm_le_lattice _ k).trans
    have hr : x + -centerShift p - ![1 / 4, 1 / 4] - (fun j => (k j : ℝ)) =
        x + -centerShift p - (fun j => (k j : ℝ)) - ![1 / 4, 1 / 4] := by abel
    rw [hr]
    exact hk
  apply hx
  change torusNorm (x - p) ≤ 1 / 16
  exact ht.trans (by
    have hq : width L n ≤ (1 / 1000000 : ℚ) :=
      (width_le L n).trans (mul_le_of_le_one_right (by norm_num)
        (pow_le_one₀ (by norm_num) (by norm_num)))
    have h : (width L n : ℝ) ≤ 1 / 1000000 := by
      have hh := (Rat.cast_le (K := ℝ)).mpr hq
      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
      exact hh
    linarith)

theorem centeredSource_zero_outside (p : Plane) (C L : ℕ) {x : Plane}
    (hx : x ∉ injectionNeighborhood p) (t : ℝ) : centeredSource p C L t x = 0 := by
  change (∑' n, detectorSourceTerm C L n (t, x + -centerShift p)) = 0
  trans ∑' _ : ℕ, (0 : ℝ)
  · apply tsum_congr
    intro n
    simp only [detectorSourceTerm, centered_bump_zero_outside p L n hx, mul_zero]
  · exact tsum_zero

theorem centeredForce_supported {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (p : Plane) (C L : ℕ)
    (ν t : ℝ) {x : Plane}
    (hx : x ∉ processorSupport V ∪ injectionNeighborhood p) (z : ℝ) :
    centeredForce V p C L ν (t, atHeight x z) = 0 := by
  let U : Set Plane := (processorSupport V ∪ injectionNeighborhood p)ᶜ
  have hU : IsOpen U := (isClosed_closure.union (injectionNeighborhood_closed p)).isOpen_compl
  have ha := viscosityDrift_smooth (detectorDrift_smooth hV C L) ν
  have hz (s : ℝ) (y : Plane) (hy : y ∈ U) :
      viscosityDrift ν (detectorDrift V C L) s y = 0 ∧
        viscositySource ν (centeredSource p C L) s y = 0 := by
    constructor
    · have hproc : ∀ τ, V τ y = 0 :=
        processor_zero_outside (fun h => hy (Or.inl h))
      have hd : detectorDrift V C L (ν * s) y = 0 := by
        change (∑' n, detectorDriftTerm V C L n (ν * s, y)) = 0
        trans ∑' _ : ℕ, (0 : Plane)
        · apply tsum_congr
          intro n
          simp only [detectorDriftTerm, hproc, smul_zero]
        · exact tsum_zero
      simp only [viscosityDrift, hd, smul_zero]
    · simp only [viscositySource,
        centeredSource_zero_outside p C L (fun h => hy (Or.inr h)), mul_zero]
  rw [centeredForce, centeredDrift_eq]
  apply triangularForce_zero_of_neighborhood ha hU hz ν t
  simpa only [horizontalLinear_eq, atHeight_horizontal, U, mem_compl_iff] using hx

end ForcedComputation.VelocityDetector.CompactCenter

end

end OAI
