import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingWindowControl

namespace OAI

/-!
# Convergence of the relative matrices at selected recurrence times

Any selection inside the logarithmic window preserves convergence to
the identity. This justifies applying the signed shearing compactness
argument after the recurrence time has been chosen.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootPairConjugate_selected_tendsto_one
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hnot : ∀ m, ¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g m)
    (hsmall : ∀ m, rootShearingKappa i j (g m) ≤ 1)
    (τ : ℕ → ℝ) (hτ : ∀ m, τ m ∈ Icc 0 (rootShearingLogTime i j (g m))) :
    Tendsto (fun m => rootPairConjugate i j (τ m) (g m)) atTop (𝓝 1) := by
  have hT := rootShearingLogTime_tendsto hij g hg hnot
  have hrate : Tendsto (fun m => Real.exp (-3 * rootShearingLogTime i j (g m)))
      atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3) hT)
    simpa only [Function.comp_def, neg_mul] using h
  have hbound (m : ℕ) := rootShearingKappa_window_bound hij (g m) (hnot m)
    (hsmall m) (τ m) (hτ m)
  have hk : Tendsto (fun m => rootShearingKappa i j (rootPairConjugate i j (τ m) (g m)))
      atTop (𝓝 0) :=
    squeeze_zero (fun m => rootShearingKappa_nonneg _ _ _) hbound hrate
  have hsmall' (m : ℕ) : rootShearingKappa i j (rootPairConjugate i j (τ m) (g m)) ≤ 1 :=
    (hbound m).trans (Real.exp_le_one_iff.mpr (by
      have hT0 := rootShearingLogTime_nonneg hij (g m) (hnot m) (hsmall m)
      linarith))
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro r
  apply tendsto_pi_nhds.mpr
  intro s
  have hentry : Tendsto (fun m => (g m).val r s) atTop (𝓝 ((1 : G n).val r s)) :=
    ((show Continuous (fun h : G n => h.val r s) from by fun_prop).tendsto 1).comp hg
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  apply squeeze_zero (fun m => abs_nonneg _)
    (fun m => rootPairConjugate_entry_difference_bound (g m) (τ m) (hτ m).1 (hsmall' m) r s)
  simpa only [sub_self, abs_zero, zero_add] using
    (hentry.sub_const ((1 : G n).val r s)).abs.add hk

end DukePrimeDegree

end

end OAI
