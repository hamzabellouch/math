import OAI.Probability.FreeIsing.Stochastic.BinaryFusionIntegral

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def binaryFusionJointLaw (mu nu : Measure ℝ) : Measure (ℝ × ℝ) :=
  (mu.prod nu).withDensity (fun p => ENNReal.ofReal (1 + p.1 * p.2))

private theorem integral_id_eq_zero_of_neg_invariant {mu : Measure ℝ}
    (hsym : Measure.map (fun u : ℝ => -u) mu = mu) : (∫ u : ℝ, u ∂mu) = 0 := by
  have hneg : MeasurePreserving (fun u : ℝ => -u) mu mu := ⟨measurable_neg, hsym⟩
  have h := hneg.integral_comp measurableEmbedding_neg (fun u : ℝ => u)
  change (∫ u : ℝ, -u ∂mu) = (∫ u : ℝ, u ∂mu) at h
  rw [integral_neg] at h
  linarith

private theorem integrable_id_of_ae_abs_lt_one {mu : Measure ℝ}
    [IsProbabilityMeasure mu] (hu : ∀ᵐ u ∂mu, |u| < 1) :
    Integrable (fun u : ℝ => u) mu := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [hu] with u hu
  simpa only [Real.norm_eq_abs] using hu.le

theorem binaryFusionJointLaw_probability {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1)
    (hsym : Measure.map (fun v : ℝ => -v) nu = nu) :
    IsProbabilityMeasure (binaryFusionJointLaw mu nu) := by
  have hip := (integrable_id_of_ae_abs_lt_one hu).mul_prod
    (integrable_id_of_ae_abs_lt_one hv)
  have hid : Integrable (fun p : ℝ × ℝ => 1 + p.1 * p.2) (mu.prod nu) :=
    (integrable_const 1).add hip
  have hnonneg : 0 ≤ᵐ[mu.prod nu] (fun p : ℝ × ℝ => 1 + p.1 * p.2) := by
    filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
    exact (binaryFusion_denominator_pos hp.1 hp.2).le
  have hint : (∫ p : ℝ × ℝ, 1 + p.1 * p.2 ∂mu.prod nu) = 1 := by
    rw [integral_add (integrable_const 1) hip,
      integral_prod_mul (μ := mu) (ν := nu) (fun u : ℝ => u) (fun v : ℝ => v),
      integral_id_eq_zero_of_neg_invariant hsym]
    simp
  constructor
  rw [binaryFusionJointLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hid hnonneg, hint]
  simp

theorem integral_binaryFusion_sq_jointLaw {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    (∫ p : ℝ × ℝ, binaryFusion p.1 p.2 ^ 2 ∂binaryFusionJointLaw mu nu) =
      ∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 / (1 + p.1 * p.2) ∂mu.prod nu := by
  rw [binaryFusionJointLaw, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
  have hd := binaryFusion_denominator_pos hp.1 hp.2
  rw [ENNReal.toReal_ofReal hd.le, smul_eq_mul, binaryFusion]
  field_simp

theorem binaryFusionJointLaw_secondMoment {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1)
    (hsym : Measure.map (fun v : ℝ => -v) nu = nu) :
    (∫ p : ℝ × ℝ, binaryFusion p.1 p.2 ^ 2 ∂binaryFusionJointLaw mu nu) =
      (∫ u : ℝ, u ^ 2 ∂mu) + (∫ v : ℝ, v ^ 2 ∂nu) -
        ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
  rw [integral_binaryFusion_sq_jointLaw hu hv]
  exact integral_binaryFusion_symmetric_square hu hv hsym

theorem binaryFusionJointLaw_secondMoment_le {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] {theta : ℝ}
    (hu : ∀ᵐ u ∂mu, |u| ≤ theta) (hv : ∀ᵐ v ∂nu, |v| ≤ theta)
    (htheta : theta < 1) (hsym : Measure.map (fun v : ℝ => -v) nu = nu) :
    (∫ p : ℝ × ℝ, binaryFusion p.1 p.2 ^ 2 ∂binaryFusionJointLaw mu nu) ≤
      (∫ u : ℝ, u ^ 2 ∂mu) + (∫ v : ℝ, v ^ 2 ∂nu) -
        2 * (1 - theta ^ 2) * (∫ u : ℝ, u ^ 2 ∂mu) * (∫ v : ℝ, v ^ 2 ∂nu) := by
  have hu1 := hu.mono (fun _ h => lt_of_le_of_lt h htheta)
  have hv1 := hv.mono (fun _ h => lt_of_le_of_lt h htheta)
  rw [integral_binaryFusion_sq_jointLaw hu1 hv1]
  exact integral_binaryFusion_le_sum_sq_sub_loss hu hv htheta hsym

theorem binaryFusionJointLaw_neg_invariant {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : Measure.map (fun u : ℝ => -u) mu = mu)
    (hnu : Measure.map (fun v : ℝ => -v) nu = nu) :
    MeasurePreserving (fun p : ℝ × ℝ => (-p.1, -p.2))
      (binaryFusionJointLaw mu nu) (binaryFusionJointLaw mu nu) := by
  have hR : MeasurePreserving (fun p : ℝ × ℝ => (-p.1, -p.2))
      (mu.prod nu) (mu.prod nu) :=
    (show MeasurePreserving (fun u : ℝ => -u) mu mu from ⟨measurable_neg, hmu⟩).prod
      ⟨measurable_neg, hnu⟩
  refine ⟨hR.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hR.measurable hs, binaryFusionJointLaw,
    withDensity_apply _ (hR.measurable hs), withDensity_apply _ hs]
  simpa only [neg_mul_neg] using hR.setLIntegral_comp_preimage hs
    (show Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (1 + p.1 * p.2)) by fun_prop)

theorem binaryFusion_map_neg_invariant {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : Measure.map (fun u : ℝ => -u) mu = mu)
    (hnu : Measure.map (fun v : ℝ => -v) nu = nu) :
    Measure.map (fun u : ℝ => -u)
        (Measure.map (fun p : ℝ × ℝ => binaryFusion p.1 p.2) (binaryFusionJointLaw mu nu)) =
      Measure.map (fun p : ℝ × ℝ => binaryFusion p.1 p.2) (binaryFusionJointLaw mu nu) := by
  have hf : Measurable (fun p : ℝ × ℝ => binaryFusion p.1 p.2) := by
    unfold binaryFusion
    fun_prop
  have hR := binaryFusionJointLaw_neg_invariant hmu hnu
  rw [Measure.map_map measurable_neg hf]
  calc
    Measure.map ((fun u : ℝ => -u) ∘ (fun p : ℝ × ℝ => binaryFusion p.1 p.2))
        (binaryFusionJointLaw mu nu) =
      Measure.map ((fun p : ℝ × ℝ => binaryFusion p.1 p.2) ∘
        (fun p : ℝ × ℝ => (-p.1, -p.2))) (binaryFusionJointLaw mu nu) := by
      congr 1
      funext p
      simp only [Function.comp_apply, binaryFusion, neg_mul_neg, ← neg_add, neg_div]
    _ = Measure.map (fun p : ℝ × ℝ => binaryFusion p.1 p.2)
        (Measure.map (fun p : ℝ × ℝ => (-p.1, -p.2)) (binaryFusionJointLaw mu nu)) :=
      (Measure.map_map hf hR.measurable).symm
    _ = _ := by rw [hR.map_eq]

theorem binaryFusion_map_abs_lt_one {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    ∀ᵐ u ∂Measure.map (fun p : ℝ × ℝ => binaryFusion p.1 p.2)
      (binaryFusionJointLaw mu nu), |u| < 1 := by
  have hf : Measurable (fun p : ℝ × ℝ => binaryFusion p.1 p.2) := by
    unfold binaryFusion
    fun_prop
  rw [ae_map_iff hf.aemeasurable (by measurability)]
  have hb : ∀ᵐ p ∂binaryFusionJointLaw mu nu, |p.1| < 1 ∧ |p.2| < 1 :=
    (withDensity_absolutelyContinuous (mu.prod nu)
      (fun p => ENNReal.ofReal (1 + p.1 * p.2))).ae_le (ae_binaryFusion_bounds hu hv)
  filter_upwards [hb] with p hp
  exact abs_binaryFusion_lt_one hp.1 hp.2

theorem binaryFusion_map_probability {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1)
    (hsym : Measure.map (fun v : ℝ => -v) nu = nu) :
    IsProbabilityMeasure (Measure.map (fun p : ℝ × ℝ => binaryFusion p.1 p.2)
      (binaryFusionJointLaw mu nu)) := by
  let := binaryFusionJointLaw_probability hu hv hsym
  infer_instance

end Problem367

end

end OAI
