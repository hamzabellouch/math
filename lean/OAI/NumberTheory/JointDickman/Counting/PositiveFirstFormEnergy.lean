import OAI.NumberTheory.JointDickman.Amplification.ActiveVolumeBound
import OAI.NumberTheory.JointDickman.Amplification.AmplifiedProfile
import OAI.NumberTheory.JointDickman.Amplification.BinLabelAmplification
import OAI.NumberTheory.JointDickman.Amplification.DiagonalRemoval

namespace OAI

/-! # Positive quadratic energy from a surviving mixed correlation -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem firstFormEnergy_nonneg (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) (hu : ∀ c, 0 ≤ u c) :
    0 ≤ firstFormEnergy B L τ C u v J N := by
  apply div_nonneg _ (Nat.cast_nonneg N)
  exact sum_nonneg (fun i _ => mul_nonneg (firstFormWeight_nonneg B L τ C u hu i.1 i.2)
    (sq_nonneg _))

/-- The numerical Cauchy estimate with the normalization used for the graph. -/
theorem normalized_energy_lower {B T δ E V r : ℝ} (hB : 0 < B) (hT : 0 < T)
    (hδ : 0 ≤ δ) (hE : 0 ≤ E) (hr : B*δ ≤ r) (hr0 : 0 ≤ r)
    (hC : r^2 ≤ V*E) (hV : V ≤ 2*B/T) : δ^2/2 ≤ E/(B*T) := by
  have hs : (B*δ)^2 ≤ r^2 := (sq_le_sq₀ (mul_nonneg hB.le hδ) hr0).mpr hr
  have he := hs.trans (hC.trans (mul_le_mul_of_nonneg_right hV hE))
  have het := mul_le_mul_of_nonneg_right he hT.le
  have hid : (2*B/T*E)*T = B*(2*E) := by field_simp
  rw [hid] at het
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (mul_pos hB hT)).mpr
  apply (mul_le_mul_iff_right₀ hB).mp
  nlinarith only [het]

/-- No bound for the first label is lost in the active Cauchy step. -/
theorem firstFormEnergy_lower {B T : ℕ} (hB : 0 < B) (hT : 0 < T)
    (L : ℕ) (τ C : ℝ) (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (g J : ℕ → ℂ) (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : ∀ c, 0 ≤ u c) (hg : ∀ m, ‖g m‖ ≤ 1)
    (hv : ∀ a c, v a c ≠ 0 → T*c ≤ a)
    (hfirst : (B : ℝ)*δ ≤ ‖firstDivisorForm B L τ C u v g J N‖)
    (hvol : activeFirstFormVolume B L τ C u T N ≤ 2*(B : ℝ)/(T : ℝ)) :
    δ^2/2 ≤ firstFormEnergy B L τ C u v J N / ((B : ℝ)*T) := by
  exact normalized_energy_lower (by exact_mod_cast hB) (by exact_mod_cast hT) hδ
    (firstFormEnergy_nonneg B L τ C u v J N hu) hfirst (norm_nonneg _)
    (firstDivisorForm_active_cauchy B L τ C u v g J T N hu hg hv) hvol

/-- A nonzero limiting correlation gives an eventual lower bound with room
for the later Cauchy estimate. -/
theorem norm_eventually_lower {f : ℕ → ℂ} {w : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hw : 2*δ ≤ ‖w‖) (hf : Tendsto f atTop (nhds w)) :
    ∀ᶠ n : ℕ in atTop, δ ≤ ‖f n‖ := by
  exact hf.norm.eventually (eventually_ge_nhds (by linarith))

end JointDickman

end OAI
