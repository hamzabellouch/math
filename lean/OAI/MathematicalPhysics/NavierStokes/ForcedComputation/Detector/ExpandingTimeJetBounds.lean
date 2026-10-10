import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingCenterBounds

namespace OAI

/-! Translating the one-dimensional clock estimates to joint derivatives
in time and space does not lose a norm factor. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows
open scoped ContDiff BigOperators

theorem time_comp_jet_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) (y : ℝ × Plane) :
    ‖iteratedFDeriv ℝ n (fun p : ℝ × Plane => f p.1) y‖ ≤
      ‖iteratedDeriv n f y.1‖ := by
  let L := ContinuousLinearMap.fst ℝ ℝ Plane
  change ‖iteratedFDeriv ℝ n (f ∘ L) y‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hf y (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hp : (∏ _i : Fin n, ‖L‖) ≤ 1 := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (pow_le_one₀ (norm_nonneg L)
        (show ‖L‖ ≤ 1 from ContinuousLinearMap.norm_fst_le ℝ ℝ Plane) : ‖L‖ ^ n ≤ 1)
  change ‖iteratedDeriv n f y.1‖ * (∏ _i : Fin n, ‖L‖) ≤ ‖iteratedDeriv n f y.1‖
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg (iteratedDeriv n f y.1))

theorem iteratedDeriv_component {f : ℝ → Plane} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (j : Fin 2) (t : ℝ) :
    iteratedDeriv n (fun s => f s j) t = iteratedDeriv n f t j := by
  let L : Plane →L[ℝ] ℝ := ContinuousLinearMap.proj j
  change iteratedDeriv n (L ∘ f) t = L (iteratedDeriv n f t)
  unfold iteratedDeriv
  rw [L.iteratedFDeriv_comp_left hf.contDiffAt (by simp)]
  rfl

theorem iteratedDeriv_plane_bound {f : ℝ → Plane} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (t : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j : Fin 2, |iteratedDeriv n (fun s => f s j) t| ≤ B) :
    ‖iteratedDeriv n f t‖ ≤ B := by
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro j
  simpa only [iteratedDeriv_component hf, Real.norm_eq_abs] using hb j

theorem clock_inverse_power_bound {T : ℝ} (hT : 1 ≤ T) {n m : ℕ}
    (hn : 1 ≤ n) (hnm : n ≤ m) : |(T/6)⁻¹| ^ n ≤ 6 ^ m / T := by
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hpowT : T ≤ T ^ n := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, pow_one]
    exact le_mul_of_one_le_right hTp.le (one_le_pow₀ hT)
  have hpow6 : (6 : ℝ) ^ n ≤ 6 ^ m := pow_le_pow_right₀ (by norm_num) hnm
  rw [abs_of_pos (inv_pos.mpr (by positivity)), inv_div, div_pow]
  apply div_le_div₀ (by positivity) hpow6 hTp hpowT

end ForcedComputation.ExpandingDetector

end

end OAI
