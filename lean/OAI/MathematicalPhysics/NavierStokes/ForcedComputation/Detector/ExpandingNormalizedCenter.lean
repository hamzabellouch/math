import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingTimeJetBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateJetBounds

namespace OAI

/-! The rescaled moving coordinate has uniformly bounded positive jets.
No bound for its unbounded zeroth coordinate is needed by composition. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows
open scoped ContDiff

theorem spatial_projection_positive_jet (n : ℕ) (hn : 1 ≤ n) (y : ℝ × Plane) :
    ‖iteratedFDeriv ℝ n (fun p : ℝ × Plane => p.2) y‖ ≤ 1 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 i, ← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ (fun p : ℝ × Plane => p.2) =
      fun _ => ContinuousLinearMap.snd ℝ ℝ Plane := by
    funext p
    exact (ContinuousLinearMap.snd ℝ ℝ Plane).fderiv
  rw [he]
  cases i with
  | zero => simpa only [norm_iteratedFDeriv_zero] using
      (ContinuousLinearMap.norm_snd_le (𝕜 := ℝ) (E := ℝ) (F := Plane))
  | succ i => rw [iteratedFDeriv_succ_const]; simp

def normalizedCenter (R : ℝ) (c : ℝ → Plane) (p : ℝ × Plane) : Plane :=
  R⁻¹ • (p.2 - c p.1)

theorem normalizedCenter_smooth (R : ℝ) {c : ℝ → Plane} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (normalizedCenter R c) :=
  (contDiff_snd.sub (hc.comp contDiff_fst)).const_smul _

theorem normalizedCenter_positive_jet {R B : ℝ} (hR : 1 ≤ R) (hB : 0 ≤ B)
    {c : ℝ → Plane} (hc : ContDiff ℝ ∞ c) (n : ℕ) (hn : 1 ≤ n)
    (y : ℝ × Plane)
    (hb : ‖iteratedDeriv n c y.1‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (normalizedCenter R c) y‖ ≤ (1+B)^n := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hi : |R⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr hRp)]
    exact inv_le_one_of_one_le₀ hR
  have hs := spatial_projection_positive_jet n hn y
  have ht := (time_comp_jet_bound hc n y).trans hb
  have hp : ContDiff ℝ ∞ (fun p : ℝ × Plane => p.2) := contDiff_snd
  have hcp : ContDiff ℝ ∞ (fun p : ℝ × Plane => c p.1) := hc.comp contDiff_fst
  have he : iteratedFDeriv ℝ n (normalizedCenter R c) y =
      R⁻¹ • (iteratedFDeriv ℝ n (fun p : ℝ × Plane => p.2) y -
        iteratedFDeriv ℝ n (fun p : ℝ × Plane => c p.1) y) := by
    unfold normalizedCenter
    rw [iteratedFDeriv_const_smul_apply' ((hp.sub hcp).of_le (by simp)).contDiffAt]
    change R⁻¹ • iteratedFDeriv ℝ n
      ((fun p : ℝ × Plane => p.2) - fun p : ℝ × Plane => c p.1) y = _
    rw [iteratedFDeriv_sub_apply (hp.of_le (by simp)).contDiffAt
      (hcp.of_le (by simp)).contDiffAt]
  rw [he, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ 1 * (‖iteratedFDeriv ℝ n (fun p : ℝ × Plane => p.2) y‖ +
        ‖iteratedFDeriv ℝ n (fun p : ℝ × Plane => c p.1) y‖) :=
      mul_le_mul hi (norm_sub_le _ _) (norm_nonneg _) (by norm_num)
    _ ≤ 1+B := by linarith
    _ ≤ (1+B)^n := by
      obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, pow_one]
      exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))

theorem movingGate_eq_packet {R : ℝ} (hR : R ≠ 0) (c : ℝ → Plane) :
    Function.uncurry (movingGate R c) =
      gatePacket (fun p => deriv c p.1) (normalizedCenter R c) := by
  funext p
  exact translationGate_scaled_kernel hR (c p.1) (deriv c p.1) p.2

end ForcedComputation.ExpandingDetector

end

end OAI
