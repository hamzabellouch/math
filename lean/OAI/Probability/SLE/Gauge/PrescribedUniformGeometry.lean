import OAI.Probability.SLE.Gauge.PrescribedBatchClock

namespace OAI

/-! One late-batch cutoff supplies all clock and visit geometry, uniformly
  over every center above the shrinking boundary strip. -/
noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge.Target

theorem eventually_prescribed_uniform_geometry {κ : ℝ} (hκ : 0<κ) (W : WienerLaw)
    (hm1 : 0 < moment κ W 1)
    (hJ : ∀ n, 1≤n → moment κ W 1^n ≤ moment κ W n) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, Real.exp (-(n:ℝ)) ≤ z.im →
      (∀ o, 0 ≤ entryPhysicalLevel κ W (n,o) (2048*Real.pi) z) ∧
      4*entryRadius κ W (n,none) ≤ z.im ∧
      ∀ (k : ℤ) (j : ℕ), j < multiplicity κ W n k →
        entryPhysicalLevel κ W (n,some (k,j)) (2048*Real.pi) z+
          2*a κ*(batchLevel κ W n:ℝ)+1 ≤
            entryPhysicalLevel κ W (n,none) (2048*Real.pi) z := by
  have ha : 0<2*a κ := mul_pos (by norm_num) (internal_a_pos hκ)
  have hlarge : ∀ᶠ n : ℕ in atTop, 1/(2*a κ) ≤ (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_entryPhysicalLevel_large hκ W (by positivity : 0<2048*Real.pi) 0,
    hlarge,eventually_ge_atTop 3] with n hl hn hn3
  intro z hz
  have hn1 : 1≤n := by omega
  have hnR : (3:ℝ) ≤ n := by exact_mod_cast hn3
  have hunit : 1 ≤ 2*a κ*(n:ℝ) := by
    have hh := (div_le_iff₀ ha).mp hn
    linarith
  refine ⟨fun o => (hl o z hz).le,?_,?_⟩
  · apply le_trans _ hz
    calc
      _ ≤ 4*Real.exp (-(n:ℝ)^2) :=
        mul_le_mul_of_nonneg_left (entryRadius_le_batch_exp hκ W (n,none)) (by norm_num)
      _ ≤ Real.exp (-(n:ℝ)) := by
        rw [show (4:ℝ)=Real.exp (Real.log 4) by rw [Real.exp_log (by norm_num)],← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hh : Real.log 4 ≤ 3 := by
          have hl4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
          linarith
        nlinarith
  · intro k j hj
    have hh := entryPhysicalLevel_cleanup_gap hκ W hn1 hm1 (hJ n hn1) hj (2048*Real.pi) z
    linarith

end SLEExactGauge.Target

end

end OAI
