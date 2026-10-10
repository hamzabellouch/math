import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarModeDerivatives

namespace OAI

/-! Uniform derivatives through order four of the manufactured planar
orbital. Derivatives are transferred to its fixed compact forcing. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem forcing_jet_compact (k : ℕ) (v : Fin k → PlanarPosition) :
    HasCompactSupport (fun x => iteratedFDeriv ℝ k planarForcing x v) :=
  (planarForcing_hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) k).comp_left
    (g := fun T : ContinuousMultilinearMap ℝ (fun _ : Fin k => PlanarPosition) ℝ => T v)
    (by simp)

theorem planar_mode_jet_transfer : ∀ k : ℕ, k ≤ 4 → ∀ (v : Fin k → PlanarPosition) r,
    iteratedFDeriv ℝ k planarResolventMode r v =
      planarResolventOf (fun x => iteratedFDeriv ℝ k planarForcing x v) r := by
  intro k
  induction k with
  | zero =>
    intro _ v r
    simp only [iteratedFDeriv_zero_apply]
    rfl
  | succ k ih =>
    intro hk v r
    have hk7 : (k : WithTop ℕ∞) < 7 := by exact_mod_cast (show k < 7 by omega)
    have hm := planarResolventMode_C7.differentiable_iteratedFDeriv hk7
    have hf := planarForcing_C7.differentiable_iteratedFDeriv hk7
    have hr : ContDiff ℝ 1 (fun x => iteratedFDeriv ℝ k planarForcing x (Fin.tail v)) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => PlanarPosition) ℝ (Fin.tail v)).contDiff.comp
        (planarForcing_C7.iteratedFDeriv_right (by exact_mod_cast (show 1+k ≤ 7 by omega)))
    rw [(hm r).iteratedFDeriv_succ_apply_left']
    have he : (fun x => iteratedFDeriv ℝ k planarResolventMode x (Fin.tail v)) =
        planarResolventOf (fun x => iteratedFDeriv ℝ k planarForcing x (Fin.tail v)) :=
      funext (ih (by omega) (Fin.tail v))
    rw [he]
    change planarPartial _ (v 0) r = _
    rw [planarResolventOf_partial hr (forcing_jet_compact k (Fin.tail v))]
    congr 1
    funext x
    exact ((hf x).iteratedFDeriv_succ_apply_left').symm

theorem planar_mode_jets_bounded :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ, k ≤ 4 → ∀ r,
      ‖iteratedFDeriv ℝ k planarResolventMode r‖ ≤ B := by
  have he (k : Fin 5) : ∃ A : ℝ, ∀ r,
      ‖iteratedFDeriv ℝ k.val planarForcing r‖ ≤ A :=
    (planarForcing_C7.continuous_iteratedFDeriv (by exact_mod_cast (show k.val ≤ 7 by omega))).bounded_above_of_compact_support
      (planarForcing_hasCompactSupport.iteratedFDeriv k.val)
  choose A hA using he
  let B := ∑ k : Fin 5, max (A k) 0
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hb (k : ℕ) (hk : k ≤ 4) (r : PlanarPosition) :
      ‖iteratedFDeriv ℝ k planarForcing r‖ ≤ B := by
    let j : Fin 5 := ⟨k,by omega⟩
    exact (hA j r).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ j)))
  refine ⟨B+1,by linarith,fun k hk r => ?_⟩
  apply ContinuousMultilinearMap.opNorm_le_bound (by linarith)
  intro v
  rw [planar_mode_jet_transfer k hk]
  apply (planarResolventOf_bound (fun x => ?_) r).trans
  · exact mul_le_mul_of_nonneg_right (by linarith : B ≤ B+1)
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  · exact ((iteratedFDeriv ℝ k planarForcing x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hb k hk x) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

theorem normalized_planar_mode_jets_bounded :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ, k ≤ 4 → ∀ r,
      ‖iteratedFDeriv ℝ k normalizedPlanarMode r‖ ≤ B := by
  obtain ⟨B,hB,hb⟩ := planar_mode_jets_bounded
  let a : ℝ := (Real.sqrt (∫ x, planarResolventMode x^2))⁻¹
  have he : normalizedPlanarMode = fun x => a • planarResolventMode x := by
    funext x
    simp only [normalizedPlanarMode,a,smul_eq_mul,div_eq_mul_inv,mul_comm]
  refine ⟨‖a‖*B+1,by nlinarith [mul_nonneg (norm_nonneg a) (show 0 ≤ B by linarith)],fun k hk r => ?_⟩
  rw [he,iteratedFDeriv_const_smul_apply'
    (planarResolventMode_C7.of_le (show (k : WithTop ℕ∞) ≤ 7 by exact_mod_cast (show k ≤ 7 by omega))).contDiffAt,
    norm_smul]
  exact (mul_le_mul_of_nonneg_left (hb k hk r) (norm_nonneg a)).trans (by linarith)

end ContinuumCoulomb

end

end OAI
