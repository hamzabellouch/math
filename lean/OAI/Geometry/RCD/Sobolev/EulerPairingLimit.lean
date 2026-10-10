import OAI.Geometry.RCD.Sobolev.WeakEulerRigidity
import OAI.Geometry.RCD.Sobolev.FiniteMomentConvergence

namespace OAI

/-! # Passing the projected Euler equation through weak pairings -/

open Filter
open scoped InnerProductSpace Topology BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- A bounded test kills an error tending to zero in L2. The spaces may
vary with the rescaling index. -/
theorem inner_tendsto_zero_of_norm_tendsto_zero
    {H : ℕ → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    (p e : ∀ i, H i) {C : ℝ} (hp : ∀ i, ‖p i‖ ≤ C)
    (he : Tendsto (fun i => ‖e i‖) atTop (𝓝 0)) :
    Tendsto (fun i => ⟪p i, e i⟫_ℝ) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _) (fun i =>
    (norm_inner_le_norm (p i) (e i)).trans
      (mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _)))
  simpa only [mul_zero] using (tendsto_const_nhds.mul he)

/-- Every term in the exact projected equation has a separate weak or strong convergence input. This calculation identifies its limit
without assuming a limiting Euler equation. -/
theorem euler_pairing_limit {n : ℕ}
    {H : ℕ → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    (p d w one e : ∀ i, H i) (u : ∀ i, Fin n → H i)
    (ell : ℕ → Fin n → ℝ) (k : ℕ → ℝ)
    (hid : ∀ i, d i = w i + ∑ j, ell i j • u i j + k i • one i + e i)
    {C D W O K : ℝ} {L U : Fin n → ℝ}
    (hp : ∀ i, ‖p i‖ ≤ C) (he : Tendsto (fun i => ‖e i‖) atTop (𝓝 0))
    (hd : Tendsto (fun i => ⟪p i, d i⟫_ℝ) atTop (𝓝 D))
    (hw : Tendsto (fun i => ⟪p i, w i⟫_ℝ) atTop (𝓝 W))
    (ho : Tendsto (fun i => ⟪p i, one i⟫_ℝ) atTop (𝓝 O))
    (hu : ∀ j, Tendsto (fun i => ⟪p i, u i j⟫_ℝ) atTop (𝓝 (U j)))
    (hl : ∀ j, Tendsto (fun i => ell i j) atTop (𝓝 (L j)))
    (hk : Tendsto k atTop (𝓝 K)) :
    D = W + ∑ j, L j * U j + K * O := by
  have hs : Tendsto (fun i => ∑ j, ell i j * ⟪p i, u i j⟫_ℝ) atTop
      (𝓝 (∑ j, L j * U j)) :=
    tendsto_finsetSum _ (fun j _ => (hl j).mul (hu j))
  have herr := inner_tendsto_zero_of_norm_tendsto_zero p e hp he
  have hlim := ((hw.add hs).add (hk.mul ho)).add herr
  have hi (i : ℕ) : ⟪p i, d i⟫_ℝ =
      ⟪p i, w i⟫_ℝ + ∑ j, ell i j * ⟪p i, u i j⟫_ℝ +
        k i * ⟪p i, one i⟫_ℝ + ⟪p i, e i⟫_ℝ := by
    rw [hid i]
    simp only [inner_add_right, inner_sum, inner_smul_right]
  have hlim' : Tendsto (fun i => ⟪p i, d i⟫_ℝ) atTop
      (𝓝 (W + ∑ j, L j * U j + K * O)) := by
    simpa only [hi, add_zero] using hlim
  exact tendsto_nhds_unique hd hlim'

end RegularPointCoordinates

end

end OAI
