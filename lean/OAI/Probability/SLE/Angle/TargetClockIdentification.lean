import OAI.Probability.SLE.Angle.TargetFlowIdentification
import OAI.Probability.SLE.Multipoint.MultipointRegulatorTransport

namespace OAI

/-! Exact clock and radius normalization for the source-prescribed flow. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Target

lemma clock_eq_activeRadiusClock
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ) (hUc : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (θ : ℝ) (x : ℂ) (T : ℝ≥0)
    (hz : diskMapInv θ x ∈ survivingDomain γ T) :
    clock κ θ b x (κ*T)=κ*Multipoint.activeRadiusClock G (diskMapInv θ x) 0 T := by
  let z := diskMapInv θ x
  let f (s : ℝ) := chartPoissonRate U G (s/κ).toNNReal z ^ 2
  let C (s : ℝ) := κ*Multipoint.activeRadiusClock G z 0 (s/κ)
  have hT : 0 ≤ κ*(T:ℝ) := mul_nonneg hκ.le T.coe_nonneg
  have hmaps : MapsTo (fun s : ℝ => s/κ) (Icc 0 (κ*T)) (Icc 0 (T:ℝ)) := by
    intro s hs
    exact ⟨div_nonneg hs.1 hκ.le,(div_le_iff₀ hκ).2 (by simpa only [mul_comm] using hs.2)⟩
  have hfc : ContinuousOn f (Icc 0 (κ*T)) :=
    ((hw.poissonRate_continuousOn hUc T z hz).pow 2).comp
      (continuous_id.div_const κ).continuousOn hmaps
  have hCc : ContinuousOn C (Icc 0 (κ*T)) := continuous_const.continuousOn.mul
    ((hw.activeRadiusClock_continuousOn hUc 0 T z hz).comp
      (continuous_id.div_const κ).continuousOn hmaps)
  have hCd (s : ℝ) (hs : s ∈ Ioo 0 (κ*T)) : HasDerivAt C (f s) s := by
    have hinner : HasDerivWithinAt (fun r : ℝ => r/κ) (1/κ)
        (Icc 0 (κ*T)) s := ((hasDerivAt_id s).div_const κ).hasDerivWithinAt
    have hd := (hw.activeRadiusClock_hasDerivWithinAt hUc 0 T z hz (s/κ)
      (hmaps (Ioo_subset_Icc_self hs))).scomp s hinner hmaps
    have hd' : HasDerivWithinAt C (f s) (Icc 0 (κ*T)) s := by
      apply (hd.const_mul κ).congr_deriv
      dsimp only [f]
      simp only [smul_eq_mul]
      field_simp [hκ.ne']
    exact hd'.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hCc hCd
    (hfc.intervalIntegrable_of_Icc hT)
  have hpoint (s : ℝ) (hs : s ∈ Icc 0 (κ*T)) :
      (flow κ b z s).im^2/‖centeredFlow κ b z s‖^4=f s := by
    have hst : (s/κ).toNNReal ≤ T :=
      (Real.toNNReal_le_iff_le_coe).2 (hmaps hs).2
    have hlive := survivingDomain_antitone γ hst hz
    have hf := flow_eq_witness_real_time κ hκ b U γ G F hw hU s hs.1 z hlive
    have hu : U (s/κ).toNNReal=driverValue b s := by
      rw [hU _ (hmaps hs).1,mul_div_cancel₀ _ hκ.ne']
    rw [centeredFlow,hf]
    simp only [f,chartPoissonRate,hu,div_pow]
    norm_num only [← pow_mul]
  have hzero : Multipoint.activeRadiusClock G z 0 (0:ℝ)=0 := by
    simp [Multipoint.activeRadiusClock]
  calc
    clock κ θ b x (κ*T) = ∫ s in Icc 0 (κ*T), f s :=
      setIntegral_congr_fun measurableSet_Icc hpoint
    _ = ∫ s in 0..(κ*T), f s := by
      rw [intervalIntegral.integral_of_le hT,integral_Icc_eq_integral_Ioc]
    _ = C (κ*T)-C 0 := hi
    _ = κ*Multipoint.activeRadiusClock G z 0 T := by
      simp only [C,mul_div_cancel_left₀ _ hκ.ne',zero_div,hzero,mul_zero,sub_zero]

lemma radius_eq_physicalConformalRadius
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ) (hUc : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (θ : ℝ) (x : ℂ) (T : ℝ≥0)
    (hz : diskMapInv θ x ∈ survivingDomain γ T) :
    radius κ θ b x (κ*T)=physicalConformalRadius (diskMap θ) G T (diskMapInv θ x) := by
  let z := diskMapInv θ x
  have hz0 := survivingDomain_antitone γ (show 0 ≤ T from zero_le) hz
  have hp := hw.physical_radius_active_clock hUc (diskMap θ) 0 T z hz0 hz
  have hi : physicalConformalRadius (diskMap θ) G 0 z=initialRadius θ x := by
    rw [physicalConformalRadius,hw.fullRadius_initial hUc z hz0]
    dsimp only [initialRadius,z]
    ring
  rw [hp,hi,radius,clock_eq_activeRadiusClock κ hκ b U hUc γ G F hw hU θ x T hz]
  congr 2
  dsimp only [a,z]
  field_simp [hκ.ne']
  ring

lemma angle_eq_witness
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (θ : ℝ) (x : ℂ) (T : ℝ≥0)
    (hz : diskMapInv θ x ∈ survivingDomain γ T) :
    angle κ θ b x (κ*T)=Complex.arg (G T (diskMapInv θ x)-(U T:ℂ)) := by
  have hu : driverValue b (κ*T)=U T := by
    simpa only [Real.toNNReal_coe] using (hU T T.coe_nonneg).symm
  rw [angle,centeredFlow,flow_eq_witness κ hκ b U γ G F hw hU T _ hz,hu]

private lemma alpha_eq_codimension (κ : ℝ) (_hκ : 0 < κ) : α κ=codimension κ := by
  dsimp only [α,d,a,codimension,dimension]
  field_simp
  ring

private lemma p_eq_greenExponent (κ : ℝ) : p κ=greenExponent κ := by
  dsimp only [p,a,greenExponent]
  ring

lemma green_eq_transported_density
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ) (hUc : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (θ : ℝ) (x : ℂ) (T : ℝ≥0) :
    green κ θ b x (κ*T)=‖deriv (diskMap θ) (diskMapInv θ x)‖^(-codimension κ)*
      greenDensity κ U γ G T (diskMapInv θ x) := by
  classical
  by_cases hz : diskMapInv θ x ∈ survivingDomain γ T
  · have hs := (surviving_iff_witness κ hκ b U γ G F hw hU T _).2 hz
    rw [green,ite_eq_left hs,greenDensity,ite_eq_left hz,
      radius_eq_physicalConformalRadius κ hκ b U hUc γ G F hw hU θ x T hz,
      angle_eq_witness κ hκ b U γ G F hw hU θ x T hz,
      alpha_eq_codimension κ hκ,p_eq_greenExponent κ,physicalConformalRadius,
      Real.mul_rpow (norm_nonneg _) (hw.fullRadius_positive hUc T _ hz).le]
    ring
  · have hs : ¬Surviving κ b (diskMapInv θ x) (κ*T) :=
      fun h => hz ((surviving_iff_witness κ hκ b U γ G F hw hU T _).1 h)
    rw [green,ite_eq_right hs,greenDensity,ite_eq_right hz,mul_zero]

end SLEExactGauge.Target

end

end OAI
