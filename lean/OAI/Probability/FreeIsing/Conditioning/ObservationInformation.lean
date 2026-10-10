import OAI.Probability.FreeIsing.Spins.ObservationFusion

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

section Observations

variable {Ω A B : Type*} {mΩ : MeasurableSpace Ω} {mA : MeasurableSpace A}
  {mB : MeasurableSpace B} {rho : Measure Ω} [IsProbabilityMeasure rho]
  {S : Ω → IsingSpin} (hS : Measurable S)
  {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
  {q : A → ℝ} {r : B → ℝ} (hq : Measurable q) (hr : Measurable r)
  (hpostX : rho[fun x => spinSign (S x) | mA.comap X] =ᵐ[rho] fun x => q (X x))
  (hpostY : rho[fun x => spinSign (S x) | mB.comap Y] =ᵐ[rho] fun x => r (Y x))
  (hqb : ∀ᵐ x ∂rho, |q (X x)| < 1) (hrb : ∀ᵐ x ∂rho, |r (Y x)| < 1)
  (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
  (hInd : ∀ a : IsingSpin, IndepFun X Y (cond rho {x | S x = a}))

include hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd

theorem map_observation_posterior_pair_eq_binaryFusionJointLaw :
    Measure.map (fun x => (q (X x), r (Y x))) rho =
      binaryFusionJointLaw (Measure.map (fun x => q (X x)) rho)
        (Measure.map (fun x => r (Y x)) rho) := by
  have hL : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | mA.comap X] x| < 1 := by
    filter_upwards [hpostX, hqb] with x hx hb
    simpa only [hx] using hb
  have hR : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | mB.comap Y] x| < 1 := by
    filter_upwards [hpostY, hrb] with x hx hb
    simpa only [hx] using hb
  have hInd' (a : IsingSpin) :
      IndepFun (rho[fun y => spinSign (S y) | mA.comap X])
        (rho[fun y => spinSign (S y) | mB.comap Y]) (cond rho {x | S x = a}) :=
    ((hInd a).comp hq hr).congr
      (cond_absolutelyContinuous.ae_le hpostX.symm)
      (cond_absolutelyContinuous.ae_le hpostY.symm)
  have hjoint := map_posterior_pair_eq_binaryFusionJointLaw
    hX.comap_le hY.comap_le hS hfair hInd' hL hR
  have hp : (fun x => (rho[fun y => spinSign (S y) | mA.comap X] x,
      rho[fun y => spinSign (S y) | mB.comap Y] x)) =ᵐ[rho]
        (fun x => (q (X x), r (Y x))) := by
    filter_upwards [hpostX, hpostY] with x hx hy
    rw [hx, hy]
  rw [Measure.map_congr hp, Measure.map_congr hpostX, Measure.map_congr hpostY] at hjoint
  exact hjoint

theorem condExp_observation_pair_map_eq_binaryFusion :
    Measure.map (rho[fun x => spinSign (S x) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun x => (X x, Y x))]) rho =
      Measure.map (fun p : ℝ × ℝ => binaryFusion p.1 p.2)
        (binaryFusionJointLaw (Measure.map (fun x => q (X x)) rho)
          (Measure.map (fun x => r (Y x)) rho)) := by
  have hCE := condExp_spin_given_observation_pair_eq_binaryFusion
    hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd
  rw [Measure.map_congr hCE,
    ← map_observation_posterior_pair_eq_binaryFusionJointLaw
      hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd,
    Measure.map_map (show Measurable (fun p : ℝ × ℝ => binaryFusion p.1 p.2) by
      unfold binaryFusion; fun_prop) (show Measurable (fun x => (q (X x), r (Y x))) from
      (hq.comp hX).prodMk (hr.comp hY))]
  rfl

theorem condExp_observation_pair_secondMoment
    (hsym : Measure.map (fun u : ℝ => -u)
      (Measure.map (fun x => r (Y x)) rho) = Measure.map (fun x => r (Y x)) rho) :
    (∫ x, (rho[fun x => spinSign (S x) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun x => (X x, Y x))] x) ^ 2 ∂rho) =
      (∫ x, q (X x) ^ 2 ∂rho) + (∫ x, r (Y x) ^ 2 ∂rho) -
        ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂
          (Measure.map (fun x => q (X x)) rho).prod (Measure.map (fun x => r (Y x)) rho) := by
  have hCE := condExp_spin_given_observation_pair_eq_binaryFusion
    hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd
  have hiCE := integral_congr_ae (hCE.fun_comp (fun x : ℝ => x ^ 2))
  simp only [Function.comp_apply] at hiCE
  rw [hiCE]
  have hpair : Measurable (fun x => (q (X x), r (Y x))) :=
    (hq.comp hX).prodMk (hr.comp hY)
  have hmap := integral_map (μ := rho) hpair.aemeasurable
    (show AEStronglyMeasurable (fun p : ℝ × ℝ => binaryFusion p.1 p.2 ^ 2) _ by
      apply Measurable.aestronglyMeasurable; unfold binaryFusion; fun_prop)
  rw [map_observation_posterior_pair_eq_binaryFusionJointLaw
    hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd] at hmap
  rw [← hmap]
  have hqm : ∀ᵐ u ∂Measure.map (fun x => q (X x)) rho, |u| < 1 :=
    (ae_map_iff (hq.comp hX).aemeasurable
      (measurableSet_lt measurable_abs measurable_const)).2 hqb
  have hrm : ∀ᵐ u ∂Measure.map (fun x => r (Y x)) rho, |u| < 1 :=
    (ae_map_iff (hr.comp hY).aemeasurable
      (measurableSet_lt measurable_abs measurable_const)).2 hrb
  rw [binaryFusionJointLaw_secondMoment hqm hrm hsym,
    integral_map (μ := rho) (φ := fun x => q (X x)) (f := fun u : ℝ => u ^ 2)
      (hq.comp hX).aemeasurable (by fun_prop),
    integral_map (μ := rho) (φ := fun x => r (Y x)) (f := fun u : ℝ => u ^ 2)
      (hr.comp hY).aemeasurable (by fun_prop)]

theorem condExp_observation_pair_secondMoment_le_add
    (hsym : Measure.map (fun u : ℝ => -u)
      (Measure.map (fun x => r (Y x)) rho) = Measure.map (fun x => r (Y x)) rho) :
    (∫ x, (rho[fun x => spinSign (S x) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun x => (X x, Y x))] x) ^ 2 ∂rho) ≤
      (∫ x, q (X x) ^ 2 ∂rho) + (∫ x, r (Y x) ^ 2 ∂rho) := by
  rw [condExp_observation_pair_secondMoment
    hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd hsym]
  apply sub_le_self
  apply integral_binaryFusionLoss_nonneg
  · exact (ae_map_iff (hq.comp hX).aemeasurable
      (measurableSet_lt measurable_abs measurable_const)).2 hqb
  · exact (ae_map_iff (hr.comp hY).aemeasurable
      (measurableSet_lt measurable_abs measurable_const)).2 hrb

theorem condExp_observation_pair_abs_lt_one :
    ∀ᵐ x ∂rho, |rho[fun x => spinSign (S x) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun x => (X x, Y x))] x| < 1 := by
  have hCE := condExp_spin_given_observation_pair_eq_binaryFusion
    hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd
  filter_upwards [hCE, hqb, hrb] with x hx hqx hrx
  rw [hx]
  exact abs_binaryFusion_lt_one hqx hrx

theorem condExp_observation_pair_neg_invariant
    (hsymq : Measure.map (fun u : ℝ => -u)
      (Measure.map (fun x => q (X x)) rho) = Measure.map (fun x => q (X x)) rho)
    (hsymr : Measure.map (fun u : ℝ => -u)
      (Measure.map (fun x => r (Y x)) rho) = Measure.map (fun x => r (Y x)) rho) :
    Measure.map (fun u : ℝ => -u)
      (Measure.map (rho[fun x => spinSign (S x) |
        (inferInstance : MeasurableSpace (A × B)).comap (fun x => (X x, Y x))]) rho) =
      Measure.map (rho[fun x => spinSign (S x) |
        (inferInstance : MeasurableSpace (A × B)).comap (fun x => (X x, Y x))]) rho := by
  rw [condExp_observation_pair_map_eq_binaryFusion
    hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd]
  exact binaryFusion_map_neg_invariant hsymq hsymr

omit hqb hrb in

theorem condExp_observation_pair_secondMoment_le
    {theta : ℝ}
    (hqtheta : ∀ᵐ x ∂rho, |q (X x)| ≤ theta)
    (hrtheta : ∀ᵐ x ∂rho, |r (Y x)| ≤ theta) (htheta : theta < 1)
    (hsym : Measure.map (fun u : ℝ => -u)
      (Measure.map (fun x => r (Y x)) rho) = Measure.map (fun x => r (Y x)) rho) :
    (∫ x, (rho[fun x => spinSign (S x) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun x => (X x, Y x))] x) ^ 2 ∂rho) ≤
      (∫ x, q (X x) ^ 2 ∂rho) + (∫ x, r (Y x) ^ 2 ∂rho) -
        2 * (1 - theta ^ 2) * (∫ x, q (X x) ^ 2 ∂rho) * (∫ x, r (Y x) ^ 2 ∂rho) := by
  have hq1 := hqtheta.mono (fun _ hx => lt_of_le_of_lt hx htheta)
  have hr1 := hrtheta.mono (fun _ hx => lt_of_le_of_lt hx htheta)
  rw [condExp_observation_pair_secondMoment
    hS hX hY hq hr hpostX hpostY hq1 hr1 hfair hInd hsym]
  have hqm : ∀ᵐ u ∂Measure.map (fun x => q (X x)) rho, |u| ≤ theta :=
    (ae_map_iff (hq.comp hX).aemeasurable
      (measurableSet_le measurable_abs measurable_const)).2 hqtheta
  have hrm : ∀ᵐ u ∂Measure.map (fun x => r (Y x)) rho, |u| ≤ theta :=
    (ae_map_iff (hr.comp hY).aemeasurable
      (measurableSet_le measurable_abs measurable_const)).2 hrtheta
  have hloss := integral_binaryFusionLoss_lower_bound hqm hrm htheta
  rw [integral_map (μ := rho) (φ := fun x => q (X x)) (f := fun u : ℝ => u ^ 2)
      (hq.comp hX).aemeasurable (by fun_prop),
    integral_map (μ := rho) (φ := fun x => r (Y x)) (f := fun u : ℝ => u ^ 2)
      (hr.comp hY).aemeasurable (by fun_prop)] at hloss
  exact sub_le_sub_left hloss _

end Observations

end Problem367

end

end OAI
