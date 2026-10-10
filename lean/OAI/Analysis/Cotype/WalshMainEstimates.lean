import OAI.Analysis.Cotype.WalshDuality
import OAI.Analysis.Cotype.Approximation

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem operatorWalsh_comp_left {n : ℕ} (B : Y →L[ℝ] G) (T : X →L[ℝ] Y)
    (f : Cube n → X) : operatorWalsh (B.comp T) f = fun v => B (operatorWalsh T f v) := by
  funext v
  simp [operatorWalsh, vectorWalsh, average]

theorem operatorWalsh_comp_right {n : ℕ} (T : Y →L[ℝ] G) (A : X →L[ℝ] Y)
    (f : Cube n → X) : operatorWalsh (T.comp A) f = operatorWalsh T (fun u => A (f u)) := rfl

theorem walshNorm_comp_left (n : ℕ) (B : Y →L[ℝ] G) (T : X →L[ℝ] Y) :
    walshNorm n (B.comp T) ≤ ‖B‖ * walshNorm n T := by
  apply walshNorm_le_of_bound _ (mul_nonneg (norm_nonneg _) (walshNorm_nonneg n T))
  intro f
  rw [operatorWalsh_comp_left]
  exact (cubeL2_clm B _).trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (operatorWalsh_le_walshNorm T f) (norm_nonneg B))

theorem walshNorm_comp_right (n : ℕ) (T : Y →L[ℝ] G) (A : X →L[ℝ] Y) :
    walshNorm n (T.comp A) ≤ walshNorm n T * ‖A‖ := by
  apply walshNorm_le_of_bound _ (mul_nonneg (walshNorm_nonneg n T) (norm_nonneg _))
  intro f
  rw [operatorWalsh_comp_right]
  exact (operatorWalsh_le_walshNorm T _).trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (cubeL2_clm A f) (walshNorm_nonneg n T))

theorem compactMap_walsh_bound (hAP : ApproximationProperty X)
    (J : G →L[ℝ] X) (hJ : IsCompactOperator J) (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hfin : ∀ T : G →L[ℝ] X, FiniteDimensional ℝ (LinearMap.range T.toLinearMap) →
      walshNorm n T ≤ ρ * ‖T‖) :
    walshNorm n J ≤ ρ * ‖J‖ := by
  by_contra hn
  have hp : 0 < walshNorm n J - ρ * ‖J‖ := sub_pos.mpr (lt_of_not_ge hn)
  let δ := (walshNorm n J - ρ * ‖J‖) / (2 * (ρ+1))
  have hδ : 0 < δ := div_pos hp (by positivity)
  obtain ⟨T, hT, herr⟩ := compactMap_finiteRank_approximation hAP J hJ hδ
  have hw := (abs_le.mp (walshNorm_lipschitz n J T)).2
  rw [norm_sub_rev] at hw
  have hnT : ‖T‖ ≤ ‖J‖ + ‖T-J‖ := by
    simpa only [sub_add_cancel] using (norm_add_le (T-J) J).trans_eq (add_comm _ _)
  have hTbound := hfin T hT
  have he : δ * (2 * (ρ+1)) = walshNorm n J - ρ * ‖J‖ := by
    dsimp [δ]
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hnT hρ,
    mul_lt_mul_of_pos_left herr (show 0 < ρ+1 by positivity)]

theorem walshNorm_identity_ge_of_l1_family {n : ℕ} {L : ℝ} (hL : 0 < L)
    (x : Cube n → X) (hx : ∀ u, ‖x u‖ ≤ 1)
    (hlower : ∀ a : Cube n → ℝ, L⁻¹ * ∑ u, |a u| ≤ ‖∑ u, a u • x u‖) :
    L⁻¹ ≤ walshNorm n (ContinuousLinearMap.id ℝ X) := by
  have hout (v : Cube n) : L⁻¹ ≤ ‖operatorWalsh (ContinuousLinearMap.id ℝ X) x v‖ := by
    have h := hlower (fun u => (Fintype.card (Cube n) : ℝ)⁻¹ * character v u)
    have hc : (Fintype.card (Cube n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simpa [operatorWalsh, vectorWalsh, average, abs_mul, abs_character,
      abs_of_nonneg (show 0 ≤ (Fintype.card (Cube n) : ℝ)⁻¹ by positivity),
      Finset.smul_sum, mul_smul, hc] using h
  have h := cubeL2_mono (f := fun _ : Cube n => L⁻¹)
    (g := operatorWalsh (ContinuousLinearMap.id ℝ X) x) (fun v => by
      simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] using hout v)
  have hin := cubeL2_bound (by positivity : (0:ℝ) ≤ 1) hx
  have hnorm : L⁻¹ ≤ cubeL2 X (operatorWalsh (ContinuousLinearMap.id ℝ X) x) := by
    simpa only [cubeL2_const, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] using h
  exact hnorm.trans (le_walshNorm _ hin)

theorem no_uniform_l1_of_walsh_decay
    (hdecay : Filter.Tendsto (fun n => walshNorm n (ContinuousLinearMap.id ℝ X)) Filter.atTop (nhds 0)) :
    ¬ ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ, ∃ x : Cube n → X,
      (∀ u, ‖x u‖ ≤ 1) ∧
      (∀ a : Cube n → ℝ, L⁻¹ * ∑ u, |a u| ≤ ‖∑ u, a u • x u‖) := by
  rintro ⟨L, hL, h⟩
  have hb : ∀ n, L⁻¹ ≤ walshNorm n (ContinuousLinearMap.id ℝ X) := by
    intro n
    obtain ⟨x, hx, hlower⟩ := h n
    exact walshNorm_identity_ge_of_l1_family hL x hx hlower
  have hzero : L⁻¹ ≤ (0 : ℝ) := ge_of_tendsto' hdecay hb
  exact (not_le_of_gt (inv_pos.mpr hL)) hzero

end Cotype

end

end OAI
