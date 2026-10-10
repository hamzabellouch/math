import OAI.Probability.FreeIsing.Gaussian.BinaryFusionMixture
import OAI.Probability.FreeIsing.Spins.PosteriorCertification
import OAI.Probability.FreeIsing.Spins.PosteriorLaw

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace Problem367

theorem measure_eq_fair_spin_mixture
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsFiniteMeasure mu]
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hfair : ∀ a : IsingSpin, mu {x | S x = a} = (1 / 2 : ENNReal)) :
    mu = (1 / 2 : ENNReal) • cond mu {x | S x = .pos} +
      (1 / 2 : ENNReal) • cond mu {x | S x = .neg} := by
  have h := sum_meas_smul_cond_fiber hS mu
  change (∑ a : IsingSpin, mu {x | S x = a} • cond mu {x | S x = a}) = mu at h
  simpa only [sum_isingSpin, hfair, add_comm] using h.symm

theorem map_posterior_pair_eq_binaryFusionJointLaw
    {Ω : Type*} {mLeft mRight m : MeasurableSpace Ω}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    (hLeft : mLeft ≤ m) (hRight : mRight ≤ m)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hfair : ∀ a : IsingSpin, mu {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin,
      IndepFun (mu[fun x => spinSign (S x) | mLeft])
        (mu[fun x => spinSign (S x) | mRight]) (cond mu {x | S x = a}))
    (hL : ∀ᵐ x ∂mu, |mu[fun y => spinSign (S y) | mLeft] x| < 1)
    (hR : ∀ᵐ x ∂mu, |mu[fun y => spinSign (S y) | mRight] x| < 1) :
    Measure.map (fun x =>
        (mu[fun y => spinSign (S y) | mLeft] x,
         mu[fun y => spinSign (S y) | mRight] x)) mu =
      binaryFusionJointLaw
        (Measure.map (mu[fun y => spinSign (S y) | mLeft]) mu)
        (Measure.map (mu[fun y => spinSign (S y) | mRight]) mu) := by
  let L : Ω → ℝ := mu[fun y => spinSign (S y) | mLeft]
  let R : Ω → ℝ := mu[fun y => spinSign (S y) | mRight]
  have hLm : Measurable L := stronglyMeasurable_condExp.measurable.mono hLeft le_rfl
  have hRm : Measurable R := stronglyMeasurable_condExp.measurable.mono hRight le_rfl
  have hpair (a : IsingSpin) :
      Measure.map (fun x => (L x, R x)) (cond mu {x | S x = a}) =
        (linearSignalTilt (Measure.map L mu) id (spinSign a)).prod
          (linearSignalTilt (Measure.map R mu) id (spinSign a)) := by
    let : IsProbabilityMeasure (cond mu {x | S x = a}) :=
      cond_isProbabilityMeasure (by rw [hfair]; norm_num)
    rw [(hInd a).map_prod_eq_prod_map_map hLm.aemeasurable hRm.aemeasurable,
      map_cond_spin_posterior_eq_linearSignalTilt hLeft hS a (hfair a),
      map_cond_spin_posterior_eq_linearSignalTilt hRight hS a (hfair a)]
  have hLmap : ∀ᵐ u ∂Measure.map L mu, |u| < 1 :=
    (ae_map_iff hLm.aemeasurable (measurableSet_lt measurable_abs measurable_const)).2 hL
  have hRmap : ∀ᵐ v ∂Measure.map R mu, |v| < 1 :=
    (ae_map_iff hRm.aemeasurable (measurableSet_lt measurable_abs measurable_const)).2 hR
  change Measure.map (fun x => (L x, R x)) mu =
    binaryFusionJointLaw (Measure.map L mu) (Measure.map R mu)
  calc
    _ = Measure.map (fun x => (L x, R x))
        ((1 / 2 : ENNReal) • cond mu {x | S x = .pos} +
          (1 / 2 : ENNReal) • cond mu {x | S x = .neg}) := by
      rw [← measure_eq_fair_spin_mixture hS hfair]
    _ = _ := by
      rw [Measure.map_add _ _ (hLm.prodMk hRm),
        Measure.map_smul _ (hLm.prodMk hRm).aemeasurable,
        Measure.map_smul _ (hLm.prodMk hRm).aemeasurable,
        hpair .pos, hpair .neg]
      exact binaryFusionJointLaw_eq_conditional_mixture hLmap hRmap

theorem condExp_spin_given_posterior_pair_eq_binaryFusion
    {Ω : Type*} {mLeft mRight m : MeasurableSpace Ω}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    (hLeft : mLeft ≤ m) (hRight : mRight ≤ m)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hfair : ∀ a : IsingSpin, mu {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin,
      IndepFun (mu[fun x => spinSign (S x) | mLeft])
        (mu[fun x => spinSign (S x) | mRight]) (cond mu {x | S x = a}))
    (hL : ∀ᵐ x ∂mu, |mu[fun y => spinSign (S y) | mLeft] x| < 1)
    (hR : ∀ᵐ x ∂mu, |mu[fun y => spinSign (S y) | mRight] x| < 1) :
    mu[fun x => spinSign (S x) | MeasurableSpace.comap
      (fun x => (mu[fun y => spinSign (S y) | mLeft] x,
        mu[fun y => spinSign (S y) | mRight] x)) inferInstance] =ᵐ[mu]
      fun x => binaryFusion (mu[fun y => spinSign (S y) | mLeft] x)
        (mu[fun y => spinSign (S y) | mRight] x) := by
  let L : Ω → ℝ := mu[fun y => spinSign (S y) | mLeft]
  let R : Ω → ℝ := mu[fun y => spinSign (S y) | mRight]
  have hLm : Measurable L := stronglyMeasurable_condExp.measurable.mono hLeft le_rfl
  have hRm : Measurable R := stronglyMeasurable_condExp.measurable.mono hRight le_rfl
  have hfm : Measurable (fun p : ℝ × ℝ => binaryFusion p.1 p.2) := by
    unfold binaryFusion
    fun_prop
  have hLmap : ∀ᵐ u ∂Measure.map L mu, |u| < 1 :=
    (ae_map_iff hLm.aemeasurable (measurableSet_lt measurable_abs measurable_const)).2 hL
  have hRmap : ∀ᵐ v ∂Measure.map R mu, |v| < 1 :=
    (ae_map_iff hRm.aemeasurable (measurableSet_lt measurable_abs measurable_const)).2 hR
  apply condExp_spin_eq_of_conditional_linearTilt hS (hLm.prodMk hRm) hfm
  · apply (ae_map_iff (hLm.prodMk hRm).aemeasurable
      (measurableSet_le hfm.abs measurable_const)).2
    filter_upwards [hL, hR] with x hxL hxR
    exact (abs_binaryFusion_lt_one hxL hxR).le
  · exact hfair .pos
  · let : IsProbabilityMeasure (cond mu {x | S x = IsingSpin.pos}) :=
      cond_isProbabilityMeasure (by rw [hfair]; norm_num)
    rw [(hInd .pos).map_prod_eq_prod_map_map hLm.aemeasurable hRm.aemeasurable,
      map_cond_spin_posterior_eq_linearSignalTilt hLeft hS .pos (hfair .pos),
      map_cond_spin_posterior_eq_linearSignalTilt hRight hS .pos (hfair .pos)]
    change (linearSignalTilt (Measure.map L mu) id 1).prod
      (linearSignalTilt (Measure.map R mu) id 1) =
      linearSignalTilt (Measure.map (fun x => (L x, R x)) mu)
        (fun p => binaryFusion p.1 p.2) 1
    rw [binaryFusion_conditional_product_eq_tilt (Or.inl rfl) hLmap hRmap]
    have hjoint : Measure.map (fun x => (L x, R x)) mu =
        binaryFusionJointLaw (Measure.map L mu) (Measure.map R mu) :=
      map_posterior_pair_eq_binaryFusionJointLaw hLeft hRight hS hfair hInd hL hR
    rw [hjoint]

theorem condExp_posterior_pair_secondMoment_le
    {Ω : Type*} {mLeft mRight m : MeasurableSpace Ω}
    {mu : Measure Ω} [IsProbabilityMeasure mu] {theta : ℝ}
    (hLeft : mLeft ≤ m) (hRight : mRight ≤ m)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hfair : ∀ a : IsingSpin, mu {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin,
      IndepFun (mu[fun x => spinSign (S x) | mLeft])
        (mu[fun x => spinSign (S x) | mRight]) (cond mu {x | S x = a}))
    (hL : ∀ᵐ x ∂mu, |mu[fun y => spinSign (S y) | mLeft] x| ≤ theta)
    (hR : ∀ᵐ x ∂mu, |mu[fun y => spinSign (S y) | mRight] x| ≤ theta)
    (htheta : theta < 1)
    (hsym : Measure.map (fun u : ℝ => -u)
      (Measure.map (mu[fun y => spinSign (S y) | mRight]) mu) =
        Measure.map (mu[fun y => spinSign (S y) | mRight]) mu) :
    (∫ x, (mu[fun x => spinSign (S x) | MeasurableSpace.comap
      (fun x => (mu[fun y => spinSign (S y) | mLeft] x,
        mu[fun y => spinSign (S y) | mRight] x)) inferInstance] x) ^ 2 ∂mu) ≤
      (∫ x, (mu[fun y => spinSign (S y) | mLeft] x) ^ 2 ∂mu) +
      (∫ x, (mu[fun y => spinSign (S y) | mRight] x) ^ 2 ∂mu) -
      2 * (1 - theta ^ 2) * (∫ x, (mu[fun y => spinSign (S y) | mLeft] x) ^ 2 ∂mu) *
        (∫ x, (mu[fun y => spinSign (S y) | mRight] x) ^ 2 ∂mu) := by
  let L : Ω → ℝ := mu[fun y => spinSign (S y) | mLeft]
  let R : Ω → ℝ := mu[fun y => spinSign (S y) | mRight]
  have hLm : Measurable L := stronglyMeasurable_condExp.measurable.mono hLeft le_rfl
  have hRm : Measurable R := stronglyMeasurable_condExp.measurable.mono hRight le_rfl
  have hL1 := hL.mono (fun _ hx => lt_of_le_of_lt hx htheta)
  have hR1 := hR.mono (fun _ hx => lt_of_le_of_lt hx htheta)
  have hCE := condExp_spin_given_posterior_pair_eq_binaryFusion hLeft hRight hS hfair hInd hL1 hR1
  have hiCE := integral_congr_ae (hCE.fun_comp (fun x : ℝ => x ^ 2))
  simp only [Function.comp_apply] at hiCE
  rw [hiCE]
  have hjoint : Measure.map (fun x => (L x, R x)) mu =
      binaryFusionJointLaw (Measure.map L mu) (Measure.map R mu) :=
    map_posterior_pair_eq_binaryFusionJointLaw hLeft hRight hS hfair hInd hL1 hR1
  have hfm : Measurable (fun p : ℝ × ℝ => binaryFusion p.1 p.2 ^ 2) := by
    unfold binaryFusion
    fun_prop
  have hmap := integral_map (μ := mu) (hLm.prodMk hRm).aemeasurable hfm.aestronglyMeasurable
  rw [hjoint] at hmap
  change (∫ x, binaryFusion (L x) (R x) ^ 2 ∂mu) ≤ _
  rw [← hmap]
  have hLmap : ∀ᵐ u ∂Measure.map L mu, |u| ≤ theta :=
    (ae_map_iff hLm.aemeasurable (measurableSet_le measurable_abs measurable_const)).2 hL
  have hRmap : ∀ᵐ v ∂Measure.map R mu, |v| ≤ theta :=
    (ae_map_iff hRm.aemeasurable (measurableSet_le measurable_abs measurable_const)).2 hR
  have hb := binaryFusionJointLaw_secondMoment_le hLmap hRmap htheta hsym
  have hLp : (∫ u : ℝ, u ^ 2 ∂Measure.map L mu) = ∫ x, L x ^ 2 ∂mu :=
    integral_map hLm.aemeasurable (by fun_prop)
  have hRp : (∫ u : ℝ, u ^ 2 ∂Measure.map R mu) = ∫ x, R x ^ 2 ∂mu :=
    integral_map hRm.aemeasurable (by fun_prop)
  rw [hLp, hRp] at hb
  exact hb

end Problem367

end

end OAI
