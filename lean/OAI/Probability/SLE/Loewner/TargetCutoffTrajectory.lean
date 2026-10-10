import OAI.Probability.SLE.Loewner.TargetEulerConvergence

namespace OAI

/-! The Euler-defined cutoff agrees with every classical trajectory on a
compact time interval. Positive height makes the cutoff inactive. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Target

lemma cutoffFlow_eq_of_trajectory
    (κ : ℝ) (b : Driver) (j : ℕ) (hj : 1 ≤ j) (z : ℂ)
    (T : ℝ) (_hT : 0 ≤ T) (Y : ℝ → ℂ)
    (hY : ContinuousOn Y (Icc 0 T)) (hY0 : Y 0=z)
    (hYd : ∀ t ∈ Ico 0 T, HasDerivWithinAt Y
      (cutoffField κ b j t (Y t)) (Ici t) t) :
    ∀ t ∈ Icc 0 T, cutoffFlow κ b j z t=Y t := by
  obtain ⟨L,K,X,hL,hK,hX,hX0,hXd⟩ := exists_cutoff_solution κ b j hj z
  have he := dist_le_of_trajectories_ODE hK hX.continuous.continuousOn
    (fun t ht => (hXd t ht.1).mono (Ici_subset_Ici.mpr ht.1)) hY hYd
    (show dist (X 0) (Y 0) ≤ 0 by rw [hX0,hY0]; simp)
  intro t ht
  rw [cutoffFlow_eq_solution κ b j hj z L K hL hK X hX.continuous hX0 hXd t ht.1]
  exact dist_le_zero.mp (by simpa only [zero_mul] using he t ht)

lemma cutoffFlow_continuousOn (κ : ℝ) (b : Driver) (j : ℕ) (hj : 1 ≤ j) (z : ℂ) :
    ContinuousOn (cutoffFlow κ b j z) (Ici 0) := by
  obtain ⟨L,K,X,hL,hK,hX,hX0,hXd⟩ := exists_cutoff_solution κ b j hj z
  exact hX.continuous.continuousOn.congr (fun t ht =>
    cutoffFlow_eq_solution κ b j hj z L K hL hK X hX.continuous hX0 hXd t ht)

lemma cutoffFlow_hasDerivWithinAt (κ : ℝ) (b : Driver) (j : ℕ)
    (hj : 1 ≤ j) (z : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (cutoffFlow κ b j z)
      (cutoffField κ b j t (cutoffFlow κ b j z t)) (Ici 0) t := by
  obtain ⟨L,K,X,hL,hK,hX,hX0,hXd⟩ := exists_cutoff_solution κ b j hj z
  have he (s : ℝ) (hs : 0 ≤ s) :=
    cutoffFlow_eq_solution κ b j hj z L K hL hK X hX.continuous hX0 hXd s hs
  rw [he t ht]
  exact (hXd t ht).congr_of_eventuallyEq
    (by filter_upwards [self_mem_nhdsWithin] with s hs; exact he s hs) (he t ht)

lemma cutoffFlow_zero (κ : ℝ) (b : Driver) (j : ℕ) (hj : 1 ≤ j) (z : ℂ) :
    cutoffFlow κ b j z 0=z := by
  obtain ⟨L,K,X,hL,hK,hX,hX0,hXd⟩ := exists_cutoff_solution κ b j hj z
  rw [cutoffFlow_eq_solution κ b j hj z L K hL hK X hX.continuous hX0 hXd 0 le_rfl,hX0]

lemma cutoff_inactive_of_height (j : ℕ) (hj : 1 ≤ j) (x : ℝ) (z : ℂ)
    (hz : (j:ℝ)⁻¹ ≤ z.im) :
    (j:ℝ)^(-(4:ℤ)) ≤ ‖z-(x:ℂ)‖^2 := by
  have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0:ℝ) < j := zero_lt_one.trans_le hj1
  have hi0 : 0 < (j:ℝ)⁻¹ := inv_pos.mpr hj0
  have hi1 : (j:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hj0).2 hj1
  have hi2 : ((j:ℝ)⁻¹)^2 ≤ 1 := by nlinarith
  have hi4 : ((j:ℝ)⁻¹)^4 ≤ ((j:ℝ)⁻¹)^2 := by nlinarith [sq_nonneg (((j:ℝ)⁻¹)^2)]
  have hh : ((j:ℝ)⁻¹)^2 ≤ z.im^2 := by nlinarith
  have hn := Complex.sq_norm_sub_sq_im (z-(x:ℂ))
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hn
  calc
    (j:ℝ)^(-(4:ℤ)) = ((j:ℝ)⁻¹)^4 := by simp only [zpow_neg,zpow_ofNat,inv_pow]
    _ ≤ z.im^2 := hi4.trans hh
    _ ≤ ‖z-(x:ℂ)‖^2 := by nlinarith [sq_nonneg (z-(x:ℂ)).re]

lemma cutoffFlow_eq_of_positive_trajectory
    (κ : ℝ) (b : Driver) (j : ℕ) (hj : 1 ≤ j) (z : ℂ)
    (T : ℝ) (hT : 0 ≤ T) (Y : ℝ → ℂ)
    (hY : ContinuousOn Y (Icc 0 T)) (hY0 : Y 0=z)
    (hheight : ∀ t ∈ Icc 0 T, (j:ℝ)⁻¹ ≤ (Y t).im)
    (hYd : ∀ t ∈ Ico 0 T, HasDerivWithinAt Y
      ((a κ:ℂ)/(Y t-driverValue b t)) (Ici t) t) :
    ∀ t ∈ Icc 0 T, cutoffFlow κ b j z t=Y t := by
  apply cutoffFlow_eq_of_trajectory κ b j hj z T hT Y hY hY0
  intro t ht
  rw [cutoffField_eq_reciprocal κ b j t (Y t)
    (cutoff_inactive_of_height j hj _ _ (hheight t (Ico_subset_Icc_self ht)))]
  exact hYd t ht

lemma surviving_cutoff_height (κ : ℝ) (b : Driver) (z : ℂ)
    (T : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hmin : (j:ℝ)⁻¹ <
      sInf ((fun t : ℝ => (cutoffFlow κ b j z t).im) '' Icc 0 T)) :
    ∀ t ∈ Icc 0 T, (j:ℝ)⁻¹ < (cutoffFlow κ b j z t).im := by
  have hc : IsCompact ((fun t : ℝ => (cutoffFlow κ b j z t).im) '' Icc 0 T) :=
    isCompact_Icc.image_of_continuousOn (Complex.continuous_im.comp_continuousOn
      ((cutoffFlow_continuousOn κ b j hj z).mono Icc_subset_Ici_self))
  intro t ht
  exact hmin.trans_le (csInf_le hc.bddBelow ⟨t,ht,rfl⟩)

lemma surviving_of_positive_trajectory
    (κ : ℝ) (b : Driver) (z : ℂ) (T : ℝ) (hT : 0 ≤ T)
    (Y : ℝ → ℂ) (hY : ContinuousOn Y (Icc 0 T)) (hY0 : Y 0=z)
    (m : ℝ) (hm : 0 < m) (hheight : ∀ t ∈ Icc 0 T, m ≤ (Y t).im)
    (hYd : ∀ t ∈ Ico 0 T, HasDerivWithinAt Y
      ((a κ:ℂ)/(Y t-driverValue b t)) (Ici t) t) : Surviving κ b z T := by
  obtain ⟨j,hj0,hjm⟩ := Real.exists_nat_pos_inv_lt hm
  have hj : 1 ≤ j := hj0
  have he := cutoffFlow_eq_of_positive_trajectory κ b j hj z T hT Y hY hY0
    (fun t ht => hjm.le.trans (hheight t ht)) hYd
  refine ⟨j,hj,lt_of_lt_of_le hjm ?_⟩
  apply le_csInf (Set.Nonempty.image _ (nonempty_Icc.mpr hT))
  rintro y ⟨t,ht,rfl⟩
  change m ≤ (cutoffFlow κ b j z t).im
  rw [he t ht]
  exact hheight t ht

end SLEExactGauge.Target

end

end OAI
