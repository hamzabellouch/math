import OAI.Geometry.RCD.Metric.PointedLimitValueBound

namespace OAI

/-! # The center of a locally uniform pointed limit -/

open Set Metric Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_centered_limit {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 ≤ r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ᶠ k in atTop, IsPointedApproximation (p k) 0 (r k) R (ε k) (V k))
    (u : ℕ → X → ℝ) (hu : ∀ k, u k (p k) = 0)
    (f : Euclidean n → ℝ) (hf : ContinuousAt f 0)
    (hconv : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ x,
      dist x (p k) ≤ R*r k → |u k x-f (V k x)| < η) : f 0 = 0 := by
  have hb : |f 0| ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro η hη
    obtain ⟨δ,hδ,hfδ⟩ := Metric.continuousAt_iff.mp hf (η/2) (half_pos hη)
    obtain ⟨k,hVk,hk,hck⟩ :=
      (hV.and ((hεlim.eventually (Iio_mem_nhds hδ)).and
        (hconv (η/2) (half_pos hη)))).exists
    have hclose : |f (V k (p k))-f 0| < η/2 := by
      exact hfδ (hVk.1.trans_lt hk)
    have hc := hck (p k) (by simpa using mul_nonneg hR (hr k))
    rw [hu k,zero_sub,abs_neg] at hc
    have ht := abs_sub_le (f 0) (f (V k (p k))) 0
    rw [sub_zero,sub_zero,abs_sub_comm] at ht
    linarith
  exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))

end RegularPointCoordinates

end

end OAI
