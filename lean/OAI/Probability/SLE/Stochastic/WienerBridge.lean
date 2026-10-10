import OAI.Probability.SLE.Geometry.PublishedWienerSupport
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

namespace OAI

/-! Independence of the Brownian endpoint and its pinned bridge, used in
the finite-window Wiener support theorem. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def unitBridge {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (t : unitInterval) (ω : Ω) : ℝ :=
  B (T*⟨t,t.2.1⟩) ω-(t:ℝ)*B T ω

lemma unitBridge_joint_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0) :
    IsGaussianProcess (Sum.elim (fun _ : Unit => B T) (unitBridge B T)) P := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  rintro (s | t)
  · exact ⟨{T},{toFun := fun x => x ⟨T,by simp⟩
                map_add' := by simp
                map_smul' := by simp},by simp⟩
  · let q : ℝ≥0 := T*⟨t,t.2.1⟩
    refine ⟨{q,T},
      { toFun := fun x => x ⟨q,by simp⟩ - (t:ℝ)*x ⟨T,by simp⟩
        map_add' := ?_
        map_smul' := ?_ }, ?_⟩
    · intro x y
      simp only [Pi.add_apply]
      ring
    · intro c x
      simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
      ring
    · intro ω
      rfl

lemma unitBridge_endpoint_covariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0) (t : unitInterval) :
    cov[B T,unitBridge B T t;P]=0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have ht : T*⟨t,t.2.1⟩≤T := by
    apply NNReal.coe_le_coe.mp
    change (T:ℝ)*(t:ℝ) ≤ T
    nlinarith [NNReal.coe_nonneg T,t.2.2]
  change cov[B T, fun ω => B (T*⟨t,t.2.1⟩) ω - (t:ℝ)*B T ω; P] = 0
  rw [covariance_fun_sub_right,
    covariance_const_mul_right,hB.covariance_eval,hB.covariance_eval,
    min_eq_right ht,min_self]
  · change (T:ℝ)*(t:ℝ) - (t:ℝ)*(T:ℝ) = 0
    ring
  · exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
  · exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
  · exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.const_mul _

lemma unitBridge_independent_endpoint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0) :
    IndepFun (B T) (fun ω t => unitBridge B T t ω) P := by
  have hi := (unitBridge_joint_gaussian hB T).indepFun_of_covariance_eq_zero
    (fun _ => hB.aemeasurable T)
    (fun t => (hB.aemeasurable _).sub ((hB.aemeasurable T).const_mul (t:ℝ)))
    (fun _ t => unitBridge_endpoint_covariance hB T t)
  simpa only [Function.comp_def, id_eq] using
    hi.comp (measurable_pi_apply ()) measurable_id

end SLEExactGauge

end

end OAI
