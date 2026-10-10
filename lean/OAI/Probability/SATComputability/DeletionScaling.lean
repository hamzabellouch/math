import OAI.Probability.SATComputability.UniformFreeMoment

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Filter
open scoped NNReal Topology

noncomputable def deletionSlope (q : ℕ) : ℝ :=
  6*uniformFreeConstant^(5/6 : ℝ)*((q : ℝ)⁻¹)^(1/6 : ℝ)

theorem deletionSlope_tendsto : Tendsto deletionSlope atTop (nhds 0) := by
  change Tendsto (fun q : ℕ => 6*uniformFreeConstant^(5/6 : ℝ)*
    ((q : ℝ)⁻¹)^(1/6 : ℝ)) atTop (nhds 0)
  have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).rpow_const_nhds_zero
    (by norm_num : (0 : ℝ) < 1/6)
  simpa only [Function.comp_apply, mul_zero] using h.const_mul (6*uniformFreeConstant^(5/6 : ℝ))

theorem deletionSlope_small {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℕ, 0 < q ∧ deletionSlope q < δ := by
  obtain ⟨q,hq,hs⟩ := ((eventually_gt_atTop 0).and
    (deletionSlope_tendsto.eventually (gt_mem_nhds hδ))).exists
  exact ⟨q,hq,hs⟩

theorem deletion_increment_linear (n q : ℕ) [NeZero n] (hq : 0 < q) :
    let P := FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)
    P.expect (maskLifetime (20*n) (deletionBudgetMask n (n/q))) -
      P.expect (maskLifetime (20*n) (deletionBudgetMask n 0)) ≤ deletionSlope q*n := by
  dsimp only
  apply (actual_deletion_mean n (n/q)).trans
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hd : ((n/q : ℕ) : ℝ) ≤ (n : ℝ)*(q : ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hqR]
    exact_mod_cast Nat.div_mul_le_self n q
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (n/q)) hd
    (by norm_num : (0 : ℝ) ≤ 1/6)
  calc
    _ ≤ 6*((n : ℝ)*uniformFreeConstant)^(5/6 : ℝ)*
        ((n : ℝ)*(q : ℝ)⁻¹)^(1/6 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (mul_nonneg hn.le uniformFreeConstant_nonneg) _))
    _ = deletionSlope q*n := by
      rw [Real.mul_rpow hn.le uniformFreeConstant_nonneg,
        Real.mul_rpow hn.le (inv_nonneg.mpr hqR.le)]
      calc
        _ = deletionSlope q*((n : ℝ)^(5/6 : ℝ)*(n : ℝ)^(1/6 : ℝ)) := by
          unfold deletionSlope
          ring
        _ = _ := by rw [← Real.rpow_add hn]; norm_num

end FixedClauseThreshold.Computability

end OAI
