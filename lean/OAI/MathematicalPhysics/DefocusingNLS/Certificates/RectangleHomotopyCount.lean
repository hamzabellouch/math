import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleRoucheInput
import Mathlib.Topology.LocallyConstant.Basic

namespace OAI

/-! # Root-count transport along the tail homotopy

Only the explicit published Rouché input is conditional. Compactness gives
local Rouché comparison and connectedness gives equality of endpoint counts.
-/

open Set Filter Topology

namespace DefocusingNLS

theorem rectangleZeroCount_homotopy (hR : RectangleRouche) (V : ℝ) (hV : 0 < V)
    (F : ℝ → ℂ → ℂ)
    (ha : ∀ a ∈ Icc (0 : ℝ) 1, AnalyticOnNhd ℂ (F a) (closedCountingRectangle V))
    (hc : ∀ a ∈ Icc (0 : ℝ) 1, ∀ z ∈ countingRectangleBoundary V,
      ContinuousAt (fun x : ℝ × ℂ => F x.1 x.2) (a, z))
    (hn : ∀ a ∈ Icc (0 : ℝ) 1, ∀ z ∈ countingRectangleBoundary V, F a z ≠ 0) :
    rectangleZeroCount V (F 0) = rectangleZeroCount V (F 1) := by
  let G : Icc (0 : ℝ) 1 → ℕ∞ := fun a => rectangleZeroCount V (F a.1)
  have hG : IsLocallyConstant G := by
    apply (IsLocallyConstant.iff_eventually_eq G).mpr
    intro a
    have he : ∀ᶠ b : Icc (0 : ℝ) 1 in 𝓝 a,
        ∀ z ∈ countingRectangleBoundary V, ‖F b.1 z - F a.1 z‖ < ‖F a.1 z‖ := by
      apply (isCompact_countingRectangleBoundary V).eventually_forall_of_forall_eventually
      intro z hz
      have hj : ContinuousAt
          (fun x : Icc (0 : ℝ) 1 × ℂ => F x.1.1 x.2) (a, z) :=
        ContinuousAt.comp
          (f := fun x : Icc (0 : ℝ) 1 × ℂ => (x.1.1, x.2))
          (g := fun x : ℝ × ℂ => F x.1 x.2) (hc a.1 a.2 z hz)
          ((continuous_subtype_val.comp continuous_fst).continuousAt.prodMk continuousAt_snd)
      have hf : ContinuousAt (F a.1) z := (ha a.1 a.2 z hz.1).continuousAt
      have hd : ContinuousAt
          (fun x : Icc (0 : ℝ) 1 × ℂ => ‖F x.1.1 x.2 - F a.1 x.2‖) (a, z) :=
        (hj.sub (hf.comp continuousAt_snd)).norm
      have hr : ContinuousAt
          (fun x : Icc (0 : ℝ) 1 × ℂ => ‖F a.1 x.2‖) (a, z) :=
        (hf.comp continuousAt_snd).norm
      have hneg : ‖F a.1 z - F a.1 z‖ - ‖F a.1 z‖ < 0 := by
        simpa using neg_lt_zero.mpr (norm_pos_iff.mpr (hn a.1 a.2 z hz))
      have hev := (hd.sub hr).eventually (eventually_lt_nhds hneg)
      exact hev.mono fun x hx => sub_lt_zero.mp hx
    filter_upwards [he] with b hb
    exact (hR V hV (F a.1) (F b.1) (ha a.1 a.2) (ha b.1 b.2) hb).symm
  exact hG.apply_eq_of_preconnectedSpace ⟨0, by constructor <;> norm_num⟩
    ⟨1, by constructor <;> norm_num⟩

end DefocusingNLS

end OAI
