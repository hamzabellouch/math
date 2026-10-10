import OAI.MeasureTheory.Falconer.Estimates.PlanarGainNumerics

namespace OAI

/-! # Absorbing the concrete slice-selection losses into the planar gain -/

namespace Falconer
open Real Filter
open scoped Topology

theorem gaussian_scale_power {δ κ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    (δ^(-κ))^j = δ^(-((j:ℝ)*κ)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
  congr 1
  ring

theorem eventually_gaussian_scale_losses {η : ℝ} (hη : 0 < η)
    (K₀ V A b : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 < δ ∧ K₀ ≤ δ^(-(η/100)) ∧
      4*V*(δ^(-(η/100)))^10 < δ^(-η) ∧
      A*(δ^(-(η/100)))^12*δ^(-b) ≤ δ^(-b-η) := by
  let κ := η/100
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hten : 0 < η-10*κ := by dsimp [κ]; linarith
  have htwelve : 0 < η-12*κ := by dsimp [κ]; linarith
  have hlarge := (tendsto_rpow_neg_nhdsGT_zero (show -κ < 0 by linarith)).eventually
    (eventually_ge_atTop K₀)
  have hnorm := (tendsto_rpow_neg_nhdsGT_zero (show -(η-10*κ) < 0 by linarith)).eventually
    (eventually_gt_atTop (4*V))
  have hcover := (tendsto_rpow_neg_nhdsGT_zero (show -(η-12*κ) < 0 by linarith)).eventually
    (eventually_ge_atTop A)
  filter_upwards [hlarge,hnorm,hcover,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)]
    with δ hlarge hnorm hcover hδone
  have hδ := hδone.1
  refine ⟨hδ,hlarge,?_,?_⟩
  · change 4*V*(δ^(-κ))^10 < δ^(-η)
    rw [gaussian_scale_power hδ]
    calc
      _ < δ^(-(η-10*κ))*δ^(-((10:ℝ)*κ)) :=
        mul_lt_mul_of_pos_right hnorm (Real.rpow_pos_of_pos hδ _)
      _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring
  · change A*(δ^(-κ))^12*δ^(-b) ≤ δ^(-b-η)
    rw [gaussian_scale_power hδ]
    calc
      _ = A*δ^(-(12*κ+b)) := by rw [mul_assoc,← Real.rpow_add hδ]; congr 2; ring
      _ ≤ δ^(-(b+η)) := rpow_absorb_constant hδ (by
        rw [show -((b+η)-(12*κ+b)) = -(η-12*κ) by ring]
        exact hcover)
      _ = _ := by congr 1; ring

end Falconer

end OAI
