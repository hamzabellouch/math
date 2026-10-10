import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! Uniformly bounded strong convergence can be applied to converging
vectors. Only the contractive case needed for spectral projections is used. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem contractive_strong_zero_apply
    (T : ℕ → H →L[ℂ] H) (hT : ∀ n, ‖T n‖ ≤ 1)
    (hzero : ∀ x : H, Tendsto (fun n => T n x) atTop (𝓝 0))
    (v : ℕ → H) (x : H) (hv : Tendsto v atTop (𝓝 x)) :
    Tendsto (fun n => T n (v n)) atTop (𝓝 0) := by
  have hb (n : ℕ) : ‖T n (v n)‖ ≤ ‖v n - x‖ + ‖T n x‖ := by
    calc
      _ = ‖T n (v n - x) + T n x‖ := by rw [map_sub, sub_add_cancel]
      _ ≤ ‖T n (v n - x)‖ + ‖T n x‖ := norm_add_le _ _
      _ ≤ ‖v n - x‖ + ‖T n x‖ := by
        have h := ((T n).le_opNorm (v n - x)).trans
          (mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _))
        linarith
  apply squeeze_zero_norm hb
  have hc : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
  simpa only [sub_self, norm_zero, zero_add] using
    ((hv.sub hc).norm.add (hzero x).norm)

theorem contractive_complement_apply
    (T : ℕ → H →L[ℂ] H) (hT : ∀ n, ‖T n‖ ≤ 1)
    (hzero : ∀ x : H, Tendsto (fun n => T n x) atTop (𝓝 0))
    (v : ℕ → H) (x : H) (hv : Tendsto v atTop (𝓝 x)) :
    Tendsto (fun n => (1 - T n) (v n)) atTop (𝓝 x) := by
  have h := hv.sub (contractive_strong_zero_apply T hT hzero v x hv)
  simpa only [_root_.sub_apply, one_apply_eq_self, sub_zero] using h

end KadisonSimilarity

end

end OAI
