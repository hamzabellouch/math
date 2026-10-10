import Mathlib
import OAI.Analysis.HardSphere.Geometry.KilledEigenvector
import OAI.Analysis.HardSphere.Geometry.GroundPositionLaw
import OAI.Analysis.HardSphere.Cutoffs.Regularize

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace HardSphere
open MeasureTheory Wiener Set Filter
open scoped ComplexConjugate
noncomputable section
variable {N : ℕ} {L : Length} {a t : ℝ}

lemma integrable_norm_endpoints (N : ℕ) (L : Length) (a t : ℝ)
    (f g : ScalarL2 N L) (s v : Time) :
    Integrable (fun ω : ConfigurationPath N L ↦ ‖f (ω s)‖*‖g (ω v)‖)
      (killedPathLaw N L a t) := by
  exact (((Lp.memLp f).comp_measurePreserving (freePathLaw_marginal N L t s)).norm.integrable_mul
    ((Lp.memLp g).comp_measurePreserving (freePathLaw_marginal N L t v)).norm).restrict

lemma modulus_killed_pairing (f g : ScalarL2 N L) :
    inner ℂ (modulusScalar f) (killedTransition N L a t (modulusScalar g)) =
      ((∫ ω : ConfigurationPath N L, ‖f (ω 0)‖*‖g (ω 1)‖ ∂killedPathLaw N L a t):ℝ) := by
  rw [killedTransition_pairing,← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [((freePathLaw_marginal N L t 0).quasiMeasurePreserving.ae_eq_comp
      (coe_modulusScalar f)).filter_mono (ae_mono Measure.restrict_le_self),
    ((freePathLaw_marginal N L t 1).quasiMeasurePreserving.ae_eq_comp
      (coe_modulusScalar g)).filter_mono (ae_mono Measure.restrict_le_self)] with ω hf hg
  dsimp only [Function.comp_def] at hf hg
  rw [hf,hg,Complex.conj_ofReal,Complex.ofReal_mul]

lemma IsGroundVector.integral_norm_endpoints {u : Jet N L} (hu : IsGroundVector N L a u)
    (ht : 0 ≤ t) :
    (∫ ω : ConfigurationPath N L, ‖u.1 (ω 0)‖*‖u.1 (ω 1)‖ ∂killedPathLaw N L a t)=
      Real.exp (-t*energy u) := by
  apply Complex.ofReal_injective
  rw [← modulus_killed_pairing,show modulusScalar u.1=(modulusJet u).1 from rfl,
    hu.modulus.killed_eigenvector ht,inner_smul_right,inner_self_eq_norm_sq_to_K,
    hu.modulus.2.2.1,RCLike.ofReal_one,one_pow,mul_one,hu.energy_modulus]

def groundPathWeight (u : Jet N L) (t : ℝ) (ω : ConfigurationPath N L) : ℝ :=
  Real.exp (t*energy u)*(‖u.1 (ω 0)‖*‖u.1 (ω 1)‖)

def groundPathLaw (N : ℕ) (L : Length) (a t : ℝ) (u : Jet N L) :
    Measure (ConfigurationPath N L) :=
  (killedPathLaw N L a t).withDensity (fun ω ↦ ENNReal.ofReal (groundPathWeight u t ω))

lemma groundPathWeight_measurable (u : Jet N L) (t : ℝ) : Measurable (groundPathWeight u t) := by
  exact measurable_const.mul (((Lp.stronglyMeasurable u.1).measurable.comp
    (continuous_eval_const (0:Time)).measurable).norm.mul
    (((Lp.stronglyMeasurable u.1).measurable.comp (continuous_eval_const (1:Time)).measurable).norm))

lemma groundPathWeight_nonneg (u : Jet N L) (t : ℝ) (ω : ConfigurationPath N L) :
    0 ≤ groundPathWeight u t ω := by
  unfold groundPathWeight
  positivity

lemma groundPathWeight_integrable (u : Jet N L) (a t : ℝ) :
    Integrable (groundPathWeight u t) (killedPathLaw N L a t) :=
  (integrable_norm_endpoints N L a t u.1 u.1 0 1).const_mul _

lemma IsGroundVector.integral_groundPathWeight {u : Jet N L} (hu : IsGroundVector N L a u)
    (ht : 0 ≤ t) : ∫ ω, groundPathWeight u t ω ∂killedPathLaw N L a t=1 := by
  simp only [groundPathWeight,integral_const_mul]
  rw [hu.integral_norm_endpoints ht,← Real.exp_add,
    show t*energy u+ -t*energy u=0 by ring,Real.exp_zero]

lemma IsGroundVector.groundPathLaw_probability {u : Jet N L} (hu : IsGroundVector N L a u)
    (ht : 0 ≤ t) : IsProbabilityMeasure (groundPathLaw N L a t u) := by
  constructor
  rw [groundPathLaw,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (groundPathWeight_integrable u a t)
      (Eventually.of_forall (groundPathWeight_nonneg u t)),hu.integral_groundPathWeight ht,
    ENNReal.ofReal_one]

end
end HardSphere

namespace HardSphere
open MeasureTheory Wiener Set Filter
open scoped ComplexConjugate
noncomputable section
variable {N : ℕ} {L : Length} {a t : ℝ}

lemma IsGroundVector.integral_complex_endpoints {u : Jet N L} (hu : IsGroundVector N L a u)
    (ht : 0 ≤ t) :
    (∫ ω : ConfigurationPath N L, conj (u.1 (ω 0))*u.1 (ω 1) ∂killedPathLaw N L a t)=
      (Real.exp (-t*energy u):ℂ) := by
  rw [← killedTransition_pairing,hu.killed_eigenvector ht,inner_smul_right,
    inner_self_eq_norm_sq_to_K,hu.2.2.1,RCLike.ofReal_one,one_pow,mul_one]

lemma IsGroundVector.ae_killed_endpoints_phase {u : Jet N L} (hu : IsGroundVector N L a u)
    (ht : 0 ≤ t) :
    ∀ᵐ ω ∂killedPathLaw N L a t,
      conj (u.1 (ω 0))*u.1 (ω 1)=(‖u.1 (ω 0)‖*‖u.1 (ω 1)‖:ℝ) := by
  let z : ConfigurationPath N L → ℂ := fun ω ↦ conj (u.1 (ω 0))*u.1 (ω 1)
  let M : ConfigurationPath N L → ℝ := fun ω ↦ ‖u.1 (ω 0)‖*‖u.1 (ω 1)‖
  have hiz : Integrable z (killedPathLaw N L a t) := integrable_killed_endpoints N L a t u.1 u.1 0 1
  have hiM : Integrable M (killedPathLaw N L a t) := integrable_norm_endpoints N L a t u.1 u.1 0 1
  have hn (ω : ConfigurationPath N L) : ‖z ω‖=M ω := by
    simp only [z,M,norm_mul,RCLike.norm_conj]
  have hnn : ∀ᵐ ω ∂killedPathLaw N L a t, 0 ≤ M ω-(z ω).re :=
    Eventually.of_forall fun ω ↦ sub_nonneg.mpr ((Complex.re_le_norm _).trans_eq (hn ω))
  have hr : (∫ ω, (z ω).re ∂killedPathLaw N L a t)=Real.exp (-t*energy u) := by
    calc
      _ = (∫ ω, z ω ∂killedPathLaw N L a t).re := Complex.reCLM.integral_comp_comm hiz
      _ = _ := congrArg Complex.re (hu.integral_complex_endpoints ht)
  have hire : Integrable (fun ω ↦ (z ω).re) (killedPathLaw N L a t) :=
    Complex.reCLM.integrable_comp hiz
  have hh : ∫ ω, (M ω-(z ω).re) ∂killedPathLaw N L a t=0 := by
    rw [integral_sub hiM hire,hr,hu.integral_norm_endpoints ht,sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn (hiM.sub hire)).mp hh
  filter_upwards [hae] with ω hω
  have he : (z ω).re=M ω := (sub_eq_zero.mp hω).symm
  have him : (z ω).im=0 := Complex.abs_re_eq_norm.mp (by
    rw [he,abs_of_nonneg (by dsimp only [M]; positivity),hn])
  change z ω=(M ω:ℂ)
  apply Complex.ext
  · exact he
  · exact him

end
end HardSphere

namespace HardSphere
open MeasureTheory Wiener Set Filter
open scoped ComplexConjugate
noncomputable section

lemma measurePreserving_weighted_invariant {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {R : α → α} (hR : MeasurePreserving R μ μ)
    (w : α → ℝ≥0∞) (hw : Measurable w) (hi : ∀ x, w (R x)=w x) :
    MeasurePreserving R (μ.withDensity w) (μ.withDensity w) := by
  refine ⟨hR.measurable,Measure.ext fun S hS ↦ ?_⟩
  rw [Measure.map_apply hR.measurable hS,withDensity_apply _ (hS.preimage hR.measurable),
    withDensity_apply _ hS,← lintegral_indicator (hS.preimage hR.measurable),
    ← lintegral_indicator hS]
  calc
    _ = ∫⁻ x, (S.indicator w) (R x) ∂μ := by
      apply lintegral_congr
      intro x
      by_cases hx : R x∈S
      · simp only [Set.indicator_of_mem hx,Set.indicator_of_mem (show x∈R ⁻¹' S from hx),hi]
      · simp only [Set.indicator_of_notMem hx,Set.indicator_of_notMem (show x∉R ⁻¹' S from hx)]
    _ = _ := hR.lintegral_comp (hw.indicator hS)

variable {N : ℕ} {L : Length} {a t : ℝ}

lemma groundPathLaw_reversal (u : Jet N L) (a t : ℝ) :
    MeasurePreserving (reverseConfigurationPath N L) (groundPathLaw N L a t u)
      (groundPathLaw N L a t u) := by
  apply measurePreserving_weighted_invariant (reverse_killedPath_preserving N L a t)
    _ (groundPathWeight_measurable u t).ennreal_ofReal
  intro ω
  congr 1
  simp only [groundPathWeight,reverseConfigurationPath_apply,reverseTime_zero,reverseTime_one]
  ring

lemma modulus_indicator_pairing (f g : ScalarL2 N L) {S : Set (Configuration N L)}
    (hS : MeasurableSet S) :
    inner ℂ (((Lp.memLp (modulusScalar f)).indicator hS).toLp (S.indicator (modulusScalar f)))
      (killedTransition N L a t (modulusScalar g)) =
      ((∫ ω : ConfigurationPath N L in (fun ω ↦ ω 0) ⁻¹' S,
        ‖f (ω 0)‖*‖g (ω 1)‖ ∂killedPathLaw N L a t):ℝ) := by
  rw [killedTransition_pairing,← integral_complex_ofReal,
    ← integral_indicator (hS.preimage (continuous_eval_const (0:Time)).measurable)]
  apply integral_congr_ae
  have h₁ := ((freePathLaw_marginal N L t 0).quasiMeasurePreserving.ae_eq_comp
    ((Lp.memLp (modulusScalar f)).indicator hS).coeFn_toLp).filter_mono (ae_mono (Measure.restrict_le_self (s := staysAllowed N L a)))
  have h₂ := ((freePathLaw_marginal N L t 0).quasiMeasurePreserving.ae_eq_comp
    (coe_modulusScalar f)).filter_mono (ae_mono (Measure.restrict_le_self (s := staysAllowed N L a)))
  have h₃ := ((freePathLaw_marginal N L t 1).quasiMeasurePreserving.ae_eq_comp
    (coe_modulusScalar g)).filter_mono (ae_mono (Measure.restrict_le_self (s := staysAllowed N L a)))
  filter_upwards [h₁,h₂,h₃] with ω h₁ h₂ h₃
  dsimp only [Function.comp_def] at h₁ h₂ h₃
  rw [h₁]
  by_cases hx : ω 0∈S
  · simp only [Set.indicator_of_mem hx,Set.indicator_of_mem (show ω∈(fun ω : ConfigurationPath N L ↦ ω 0) ⁻¹' S from hx),
      h₂,h₃,Complex.conj_ofReal,Complex.ofReal_mul]
  · simp only [Set.indicator_of_notMem hx,Set.indicator_of_notMem (show ω∉(fun ω : ConfigurationPath N L ↦ ω 0) ⁻¹' S from hx),
      map_zero,zero_mul]

lemma modulus_indicator_inner (f : ScalarL2 N L) {S : Set (Configuration N L)}
    (hS : MeasurableSet S) :
    inner ℂ (((Lp.memLp (modulusScalar f)).indicator hS).toLp (S.indicator (modulusScalar f)))
      (modulusScalar f) = ((∫ X in S, ‖f X‖^2):ℝ) := by
  rw [L2.inner_def,← integral_complex_ofReal,← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [((Lp.memLp (modulusScalar f)).indicator hS).coeFn_toLp,
    coe_modulusScalar f] with X h₁ h₂
  rw [h₁]
  by_cases hx : X∈S
  · simp only [Set.indicator_of_mem hx,h₂,RCLike.inner_apply,Complex.conj_ofReal,
      pow_two,Complex.ofReal_mul]
  · simp only [Set.indicator_of_notMem hx,inner_zero_left]

lemma IsGroundVector.endpoint_norm_setIntegral {u : Jet N L} (hu : IsGroundVector N L a u)
    (ht : 0 ≤ t) {S : Set (Configuration N L)} (hS : MeasurableSet S) :
    (∫ ω : ConfigurationPath N L in (fun ω ↦ ω 0) ⁻¹' S,
      ‖u.1 (ω 0)‖*‖u.1 (ω 1)‖ ∂killedPathLaw N L a t)=
      Real.exp (-t*energy u)*(∫ X in S, ‖u.1 X‖^2) := by
  apply Complex.ofReal_injective
  rw [← modulus_indicator_pairing u.1 u.1 hS,
    show modulusScalar u.1=(modulusJet u).1 from rfl,hu.modulus.killed_eigenvector ht,
    inner_smul_right,hu.energy_modulus]
  change _ * inner ℂ (((Lp.memLp (modulusScalar u.1)).indicator hS).toLp (S.indicator (modulusScalar u.1)))
      (modulusScalar u.1) = _
  rw [modulus_indicator_inner u.1 hS,Complex.ofReal_mul]

lemma IsGroundVector.groundPathLaw_initial {u : Jet N L} (hu : IsGroundVector N L a u)
    (ht : 0 ≤ t) :
    MeasurePreserving (fun ω : ConfigurationPath N L ↦ ω 0) (groundPathLaw N L a t u)
      (groundPositionLaw N L u) := by
  refine ⟨(continuous_eval_const (0:Time)).measurable,Measure.ext fun S hS ↦ ?_⟩
  rw [Measure.map_apply (continuous_eval_const (0:Time)).measurable hS,
    groundPathLaw,groundPositionLaw,
    withDensity_apply _ (hS.preimage (continuous_eval_const (0:Time)).measurable),
    withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal (groundPathWeight_integrable u a t).integrableOn
      (Eventually.of_forall (groundPathWeight_nonneg u t)),
    ← ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp u.1).integrable_norm_pow (by norm_num : (2:ℕ)≠0)).integrableOn
      (Eventually.of_forall fun X ↦ sq_nonneg ‖u.1 X‖)]
  congr 1
  simp only [groundPathWeight,integral_const_mul]
  rw [hu.endpoint_norm_setIntegral ht hS,← mul_assoc,← Real.exp_add,
    show t*energy u+ -t*energy u=0 by ring,Real.exp_zero,one_mul]

lemma IsGroundVector.groundPathLaw_terminal {u : Jet N L} (hu : IsGroundVector N L a u)
    (ht : 0 ≤ t) :
    MeasurePreserving (fun ω : ConfigurationPath N L ↦ ω 1) (groundPathLaw N L a t u)
      (groundPositionLaw N L u) := by
  simpa only [Function.comp_def,reverseConfigurationPath_apply,reverseTime_zero] using
    (hu.groundPathLaw_initial ht).comp (groundPathLaw_reversal u a t)

end
end HardSphere

end
end
end

end OAI
