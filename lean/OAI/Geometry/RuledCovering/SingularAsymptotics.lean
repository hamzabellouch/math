import OAI.Geometry.RuledCovering.EnergyIntegral

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singular_weighted_integral_tendsto {p gamma : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hg : 1 < gamma) :
    Tendsto (fun c : ℝ =>
      ((∫ z in singularDomain p gamma c, physicalWeight (Real.sqrt 2) (c • singularField p z))-1/4)/c^2)
      (𝓝[>] 0) (𝓝 (singularCoefficient p)) := by
  have ht := (singularDomain_volume_tendsto (by linarith : 0 ≤ p) hp2 hg).add
    (energyCorrection_integral_tendsto hp hp2 (by linarith : 0 < gamma))
  have hlim : (∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b) +
      -(∫ z in coneTriangle (1/2), singularEnergy p z)/2 = singularCoefficient p := by
    rw [neg_div,← sub_eq_add_neg]
    exact singular_exact_coefficient hp
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc0 : c ≠ 0 := ne_of_gt hc
  rw [singular_weighted_integral_expansion hp gamma c]
  field_simp
  ring

lemma singular_totalCost_quotient_tendsto {p gamma : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hg : 1 < gamma) :
    Tendsto (fun c : ℝ =>
      (2*singularCost p gamma c+8*Real.sqrt 2*(c^gamma)^2-Real.sqrt 2/2)/c^2)
      (𝓝[>] 0) (𝓝 (2*Real.sqrt 2*singularCoefficient p)) := by
  have ht := ((singular_weighted_integral_tendsto hp hp2 hg).const_mul (2*Real.sqrt 2)).add
    ((singular_tip_small hg).tendsto_div_nhds_zero.const_mul (8*Real.sqrt 2))
  simp only [mul_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards with c
  unfold singularCost
  ring

lemma singular_asymptotic {p gamma : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hg : 1 < gamma) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun c => 2*singularCost p gamma c+8*Real.sqrt 2*(c^gamma)^2-
        (Real.sqrt 2/2+2*Real.sqrt 2*singularCoefficient p*c^2))
      (fun c => c^2) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · have ht := (singular_totalCost_quotient_tendsto hp hp2 hg).sub_const (2*Real.sqrt 2*singularCoefficient p)
    simp only [sub_self] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hc0 : c ≠ 0 := ne_of_gt hc
    field_simp
    ring
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact fun h => False.elim ((pow_ne_zero 2 (ne_of_gt hc)) h)

lemma singular_totalCost_small {p gamma : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hg : 1 < gamma)
    (hk : singularCoefficient p < 0) :
    ∀ᶠ c : ℝ in 𝓝[>] 0,
      2*singularCost p gamma c+8*Real.sqrt 2*(c^gamma)^2 < Real.sqrt 2/2 := by
  have hk' : 2*Real.sqrt 2*singularCoefficient p < 0 := mul_neg_of_pos_of_neg
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))) hk
  filter_upwards [self_mem_nhdsWithin,
    (singular_totalCost_quotient_tendsto hp hp2 hg).eventually (gt_mem_nhds hk')] with c hc hcost
  exact sub_neg.mp (by simpa only [zero_mul] using (div_lt_iff₀ (sq_pos_of_pos hc)).mp hcost)

end RuledApproximation

end

end OAI
