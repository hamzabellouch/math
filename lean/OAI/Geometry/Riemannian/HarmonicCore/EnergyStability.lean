import OAI.Geometry.Riemannian.HarmonicCore.Energy

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise

namespace HarmonicCounterexample.Main.SmoothMetric3
lemma affine_energy_gradient_bound (R : ℝ) (A : E3 → E3 →L[ℝ] E3)
    (C c : ℝ) (hc : 0 < c) (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) (hpos : ∀ x v, c * ‖v‖^2 ≤ ⟪A x v,v⟫_ℝ)
    (D : DerivativeL2) (u : ZeroSobolev R)
    (hu : ∀ v : ZeroSobolev R,
      ⟪coefficientCLM A C hA hbound (D + sobolevDerivative R u),sobolevDerivative R v⟫_ℝ = 0) :
    ‖sobolevDerivative R u‖ ≤ (C/c)*‖D‖ := by
  have hC : 0 ≤ C := (norm_nonneg (A 0)).trans (hbound 0)
  have hh := hu u
  rw [map_add,inner_add_left] at hh
  have hp := coefficientCLM_coercive A C c hA hbound hpos (sobolevDerivative R u)
  have hn := real_inner_le_norm (-(coefficientCLM A C hA hbound D)) (sobolevDerivative R u)
  rw [inner_neg_left,norm_neg] at hn
  have hnorm : ‖coefficientCLM A C hA hbound D‖ ≤ C * ‖D‖ :=
    coefficientLinear_norm A C hA hbound D
  have hle : c * ‖sobolevDerivative R u‖^2 ≤
      (C * ‖D‖) * ‖sobolevDerivative R u‖ := by
    have := mul_le_mul_of_nonneg_right hnorm (norm_nonneg (sobolevDerivative R u))
    linarith
  by_cases hz : ‖sobolevDerivative R u‖ = 0
  · rw [hz]; positivity
  · have hnpos : 0 < ‖sobolevDerivative R u‖ := (norm_nonneg _).lt_of_ne' hz
    have hle' : c * ‖sobolevDerivative R u‖ ≤ C * ‖D‖ := by
      apply (mul_le_mul_iff_left₀ hnpos).mp
      nlinarith [hle]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hle')

lemma coefficientCLM_difference_bound (A B : E3 → E3 →L[ℝ] E3) (C D ε : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hB : AEStronglyMeasurable B (volume : Measure E3))
    (hboundA : ∀ x, ‖A x‖ ≤ C) (hboundB : ∀ x, ‖B x‖ ≤ D)
    (hε : ∀ x, ‖A x - B x‖ ≤ ε) (u : DerivativeL2) :
    ‖coefficientCLM A C hA hboundA u - coefficientCLM B D hB hboundB u‖ ≤ ε * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(coefficient_memLp A C hA hboundA u).coeFn_toLp,
    (coefficient_memLp B D hB hboundB u).coeFn_toLp,
    Lp.coeFn_sub (coefficientCLM A C hA hboundA u) (coefficientCLM B D hB hboundB u)] with x hx hy hz
  rw [hz]
  change ‖((coefficient_memLp A C hA hboundA u).toLp _) x -
    ((coefficient_memLp B D hB hboundB u).toLp _) x‖ ≤ _
  rw [hx,hy]
  exact ((A x - B x).le_opNorm (u x)).trans
    (mul_le_mul_of_nonneg_right (hε x) (norm_nonneg _))

lemma affine_energy_stability (R : ℝ) (A B : E3 → E3 →L[ℝ] E3)
    (C c ε : ℝ) (hc : 0 < c) (hεpos : 0 ≤ ε)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hB : AEStronglyMeasurable B (volume : Measure E3))
    (hboundA : ∀ x, ‖A x‖ ≤ C) (hboundB : ∀ x, ‖B x‖ ≤ C)
    (hposA : ∀ x v, c * ‖v‖^2 ≤ ⟪A x v,v⟫_ℝ)
    (hposB : ∀ x v, c * ‖v‖^2 ≤ ⟪B x v,v⟫_ℝ)
    (hε : ∀ x, ‖A x - B x‖ ≤ ε)
    (D : DerivativeL2) (u w : ZeroSobolev R)
    (hu : ∀ v : ZeroSobolev R,
      ⟪coefficientCLM A C hA hboundA (D + sobolevDerivative R u),sobolevDerivative R v⟫_ℝ = 0)
    (hw : ∀ v : ZeroSobolev R,
      ⟪coefficientCLM B C hB hboundB (D + sobolevDerivative R w),sobolevDerivative R v⟫_ℝ = 0) :
    ‖sobolevDerivative R (u-w)‖ ≤ (ε/c)*(1+C/c)*‖D‖ := by
  let LA := coefficientCLM A C hA hboundA
  let LB := coefficientCLM B C hB hboundB
  let e := sobolevDerivative R (u-w)
  let p := D + sobolevDerivative R w
  have he : e = sobolevDerivative R u - sobolevDerivative R w := map_sub _ _ _
  have hid : ⟪LA e,e⟫_ℝ = -⟪LA p-LB p,e⟫_ℝ := by
    have hu' := hu (u-w)
    have hw' := hw (u-w)
    change ⟪LA (D + sobolevDerivative R u),e⟫_ℝ = 0 at hu'
    change ⟪LB p,e⟫_ℝ = 0 at hw'
    have hsum : D + sobolevDerivative R u = p + e := by simp [p,he]
    rw [hsum,map_add,inner_add_left] at hu'
    rw [inner_sub_left,hw']
    linarith
  have hp := coefficientCLM_coercive A C c hA hboundA hposA e
  change c * ‖e‖^2 ≤ ⟪LA e,e⟫_ℝ at hp
  have hdiff : ‖LA p-LB p‖ ≤ ε * ‖p‖ :=
    coefficientCLM_difference_bound A B C C ε hA hB hboundA hboundB hε p
  have hw_bound := affine_energy_gradient_bound R B C c hc hB hboundB hposB D w hw
  have hpnorm : ‖p‖ ≤ (1+C/c)*‖D‖ := by
    have := norm_add_le D (sobolevDerivative R w)
    dsimp [p]
    nlinarith
  have hn := real_inner_le_norm (-(LA p-LB p)) e
  rw [inner_neg_left,norm_neg] at hn
  rw [hid] at hp
  have hh : c * ‖e‖^2 ≤ (ε * ((1+C/c)*‖D‖))*‖e‖ := by
    have hm := mul_le_mul_of_nonneg_right
      (hdiff.trans (mul_le_mul_of_nonneg_left hpnorm hεpos)) (norm_nonneg e)
    linarith
  have hC : 0 ≤ C := (norm_nonneg (B 0)).trans (hboundB 0)
  by_cases hz : ‖e‖ = 0
  · change ‖e‖ ≤ _
    rw [hz]; positivity
  · have hne : 0 < ‖e‖ := (norm_nonneg _).lt_of_ne' hz
    have hle : c * ‖e‖ ≤ ε * ((1+C/c)*‖D‖) := by
      apply (mul_le_mul_iff_left₀ hne).mp
      nlinarith [hh]
    change ‖e‖ ≤ _
    have hle' : ‖e‖ ≤ ε * ((1+C/c)*‖D‖) / c :=
      (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hle)
    convert hle' using 1
    ring

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
