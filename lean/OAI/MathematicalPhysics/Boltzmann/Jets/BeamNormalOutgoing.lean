import OAI.MathematicalPhysics.Boltzmann.Branching.NormalGainMeasureActions
import OAI.MathematicalPhysics.Boltzmann.Branching.NormalOutgoingSymmetry
import OAI.MathematicalPhysics.Boltzmann.Branching.PerturbedFiniteBlock
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalGainTransport
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricDampedRetention
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricPositiveCompact

namespace OAI

section

/-! # Space-time coordinates normalized by the local cold density -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.ReferenceGeometry

def normalizedPoint (ρ t₀ : ℝ) (x₀ : V) (p : ℝ × V) : ℝ × V :=
  (t₀+p.1/ρ,x₀+ρ⁻¹ • p.2)

theorem normalizedPoint_measurable (ρ t₀ : ℝ) (x₀ : V) :
    Measurable (normalizedPoint ρ t₀ x₀) := by
  unfold normalizedPoint
  fun_prop

def BeamCoefficients.normalized (b : BeamCoefficients) (ρ t₀ : ℝ) (x₀ : V) : BeamCoefficients where
  plusPartner := b.plusPartner ∘ normalizedPoint ρ t₀ x₀
  minusPartner := b.minusPartner ∘ normalizedPoint ρ t₀ x₀
  plusDensity := b.plusDensity ∘ normalizedPoint ρ t₀ x₀
  minusDensity := b.minusDensity ∘ normalizedPoint ρ t₀ x₀
  plusPartner_measurable := b.plusPartner_measurable.comp (normalizedPoint_measurable ρ t₀ x₀)
  minusPartner_measurable := b.minusPartner_measurable.comp (normalizedPoint_measurable ρ t₀ x₀)
  plusDensity_measurable := b.plusDensity_measurable.comp (normalizedPoint_measurable ρ t₀ x₀)
  minusDensity_measurable := b.minusDensity_measurable.comp (normalizedPoint_measurable ρ t₀ x₀)

theorem normalizedPoint_bounds {ρ t₀ A : ℝ} (hρ : 0 < ρ) (x₀ : V) (p : ℝ × V)
    (ht : p.1 ∈ Icc 0 A) (hx : ‖p.2‖ ≤ 6*A) :
    (normalizedPoint ρ t₀ x₀ p).1 ∈ Icc t₀ (t₀+A/ρ) ∧
      ‖(normalizedPoint ρ t₀ x₀ p).2-x₀‖ ≤ 6*A/ρ := by
  constructor
  · constructor
    · change t₀ ≤ t₀+p.1/ρ
      exact le_add_of_nonneg_right (div_nonneg ht.1 hρ.le)
    · change t₀+p.1/ρ ≤ t₀+A/ρ
      exact add_le_add le_rfl (div_le_div_of_nonneg_right ht.2 hρ.le)
  · simp only [normalizedPoint,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_inv,abs_of_pos hρ]
    simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hρ.le)

theorem normalized_beam_near (b : BeamCoefficients) {ρ t₀ A ε : ℝ}
    (hρ : 0 < ρ) (x₀ : V)
    (hnear : ∀ p : ℝ × V, p.1 ∈ Icc t₀ (t₀+A/ρ) → ‖p.2-x₀‖ ≤ 6*A/ρ → BeamNear b ε p)
    (p : ℝ × V) (ht : p.1 ∈ Icc 0 A) (hx : ‖p.2‖ ≤ 6*A) :
    BeamNear (b.normalized ρ t₀ x₀) ε p := by
  have H := normalizedPoint_bounds (t₀ := t₀) hρ x₀ p ht hx
  exact hnear _ H.1 H.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The physical beam source in characteristic variables has no terminal-time dependence -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def characteristicBeamPoint (z : ℝ × WeakTime.Phase) : ℝ × V :=
  (z.1,z.2.1+z.1 • z.2.2)

def characteristicBeamJump (z : ℝ × WeakTime.Phase) (v : V) : ℝ × WeakTime.Phase :=
  (z.1,(z.2.1+z.1 • z.2.2-z.1 • v,v))

theorem beamCharacteristicKernel_lintegral (b : BeamCoefficients) (endTime : ℝ)
    (z : ℝ × WeakTime.Phase) {F : ℝ × WeakTime.Phase → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂beamCharacteristicKernel b endTime z) =
      mediumMarkedRate b 1 (characteristicBeamPoint z,z.2.2) *
        (∫⁻ n : Sphere, F (characteristicBeamJump z
          (markedChild 1 z.2.2 (b.plusPartner (characteristicBeamPoint z))
            (b.minusPartner (characteristicBeamPoint z)) n.1)) ∂sphereProbability) +
      mediumMarkedRate b 2 (characteristicBeamPoint z,z.2.2) *
        (∫⁻ n : Sphere, F (characteristicBeamJump z
          (markedChild 2 z.2.2 (b.plusPartner (characteristicBeamPoint z))
            (b.minusPartner (characteristicBeamPoint z)) n.1)) ∂sphereProbability) := by
  let e := flightCharacteristicEquiv endTime
  have hm : Measurable (fun q : PhysicalFlightState => F (e q)) := hF.comp e.measurable
  have ht : endTime-(e.symm z).1 = z.1 := by
    change endTime-(endTime-z.1) = z.1
    ring
  have hj (v : V) : e ((e.symm z).1,((e.symm z).2.1,v)) = characteristicBeamJump z v := by
    change (endTime-(endTime-z.1),
      (z.2.1+z.1 • z.2.2-(endTime-(endTime-z.1)) • v,v)) = _
    rw [sub_sub_cancel]
    rfl
  rw [beamCharacteristicKernel,transportedKernel_lintegral _ _ _ hF]
  change (∫⁻ q, F (e q) ∂physicalBeamCollision b endTime (e.symm z)) = _
  rw [physicalBeamCollision_lintegral,physicalMarkedCollision_lintegral b endTime 1 _ hm,
    physicalMarkedCollision_lintegral b endTime 2 _ hm]
  simp_rw [hj]
  rw [ht]
  rfl

theorem beamCharacteristicKernel_independent (b : BeamCoefficients) (T U : ℝ) :
    beamCharacteristicKernel b T = beamCharacteristicKernel b U := by
  apply Kernel.ext_fun
  intro z F hF
  rw [beamCharacteristicKernel_lintegral b T z hF,beamCharacteristicKernel_lintegral b U z hF]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A velocity margin for smooth cutoffs around the bounded physical histories -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem medium_frequency_seven {v wp wm : V} {bp bm : ℝ}
    (hv : ‖v‖ ≤ 7) (hwp : ‖wp‖ ≤ 2) (hwm : ‖wm‖ ≤ 2)
    (hbp : 0 ≤ bp) (hbm : 0 ≤ bm) (hbp1 : bp ≤ 5/4) (hbm1 : bm ≤ 5/4) :
    0 ≤ mediumFrequency v wp wm bp bm ∧ mediumFrequency v wp wm bp bm ≤ 45*Real.pi := by
  have hp : ‖v-wp‖ ≤ 9 := (norm_sub_le v wp).trans (by linarith)
  have hm : ‖v-wm‖ ≤ 9 := (norm_sub_le v wm).trans (by linarith)
  have hp' : bp*‖v-wp‖ ≤ 45/4 := by
    calc
      _ ≤ (5/4:ℝ)*9 := mul_le_mul hbp1 hp (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hm' : bm*‖v-wm‖ ≤ 45/4 := by
    calc
      _ ≤ (5/4:ℝ)*9 := mul_le_mul hbm1 hm (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  constructor
  · unfold mediumFrequency
    positivity
  · unfold mediumFrequency
    have h := mul_le_mul_of_nonneg_left (add_le_add hp' hm') (by positivity : 0 ≤ 2*Real.pi)
    nlinarith

theorem BeamNear.frequency_margin {b : BeamCoefficients} {ε : ℝ} {p : ℝ × V}
    (hε : ε ≤ 1/4) (hnear : BeamNear b ε p) {v : V} (hv : ‖v‖ ≤ 7) :
    0 ≤ mediumFrequency v (b.plusPartner p) (b.minusPartner p)
      (b.plusDensity p) (b.minusDensity p) ∧
    mediumFrequency v (b.plusPartner p) (b.minusPartner p)
      (b.plusDensity p) (b.minusDensity p) ≤ 45*Real.pi := by
  have hwp : ‖b.plusPartner p‖ ≤ 2 := by
    have h := norm_add_le (b.plusPartner p-beamAxis) beamAxis
    rw [sub_add_cancel,axis_norms.2.2] at h
    linarith [hnear.1]
  have hwm : ‖b.minusPartner p‖ ≤ 2 := by
    have h := norm_add_le (b.minusPartner p-(-beamAxis)) (-beamAxis)
    rw [sub_add_cancel,norm_neg,axis_norms.2.2] at h
    linarith [hnear.2.1]
  have hp := abs_le.mp hnear.2.2.1
  have hm := abs_le.mp hnear.2.2.2
  exact medium_frequency_seven hv hwp hwm (by linarith [hp.1]) (by linarith [hm.1])
    (by linarith [hp.2]) (by linarith [hm.2])

end BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

open ReferenceGeometry

theorem frequency_le_near_clock_seven {θ K α γ r t ε : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r)
    (ht : 0 ≤ t) (η l : ℝ) (x v : Velocity) (hv : ‖v‖ ≤ 7) (hε : ε ≤ 1/4)
    (hnear : BeamNear (beamCoefficients hθ hα hγ η r) ε (t,x)) :
    frequency θ η l K α γ t (VelocityWeight.transverse x,VelocityWeight.axial x) v ≤
      (K/(4*r))*(48*Real.pi) := by
  by_cases ha : active θ η l (VelocityWeight.transverse x)
  · rw [frequency_eq_beamFrequency hθ hK hα hγ hr ht η l x v ha]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hf := hnear.frequency_margin hε hv
    linarith [Real.pi_pos]
  · rw [frequency,background,ite_eq_right ha,integral_zero_measure,mul_zero]
    positivity

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The two atomic cold beams as a measurable partner kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def beamPartnerKernel (b : BeamCoefficients) : Kernel (ℝ × V) V :=
  (Kernel.deterministic b.plusPartner b.plusPartner_measurable).withDensity
    (fun p _ => ENNReal.ofReal (b.plusDensity p))+
  (Kernel.deterministic b.minusPartner b.minusPartner_measurable).withDensity
    (fun p _ => ENNReal.ofReal (b.minusDensity p))

instance beamPartnerKernel_sFinite (b : BeamCoefficients) : IsSFiniteKernel (beamPartnerKernel b) := by
  have hp : IsSFiniteKernel ((Kernel.deterministic b.plusPartner b.plusPartner_measurable).withDensity
      (fun p _ => ENNReal.ofReal (b.plusDensity p))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  have hn : IsSFiniteKernel ((Kernel.deterministic b.minusPartner b.minusPartner_measurable).withDensity
      (fun p _ => ENNReal.ofReal (b.minusDensity p))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  unfold beamPartnerKernel
  infer_instance

theorem beamPartnerKernel_apply (b : BeamCoefficients) (p : ℝ × V) :
    beamPartnerKernel b p = beamMeasure b p := by
  rw [beamPartnerKernel,add_apply,
    Kernel.withDensity_apply (f := fun p _ => ENNReal.ofReal (b.plusDensity p)) _
      (b.plusDensity_measurable.ennreal_ofReal.comp measurable_fst),
    Kernel.withDensity_apply (f := fun p _ => ENNReal.ofReal (b.minusDensity p)) _
      (b.minusDensity_measurable.ennreal_ofReal.comp measurable_fst),
    withDensity_const,withDensity_const,Kernel.deterministic_apply,Kernel.deterministic_apply]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The atomic beam's genuine normal-angle collision law in characteristic coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.ReferenceGeometry

def beamNormalCharacteristicKernel (b : BeamCoefficients) :
    Kernel CharacteristicPhase CharacteristicPhase :=
  transportedKernel characteristicEquiv (normalPhaseGainKernel (beamPartnerKernel b))

instance beamNormalCharacteristicKernel_sFinite (b : BeamCoefficients) :
    IsSFiniteKernel (beamNormalCharacteristicKernel b) := by
  unfold beamNormalCharacteristicKernel
  infer_instance

theorem beamNormalCharacteristicKernel_lintegral (b : BeamCoefficients)
    (z : CharacteristicPhase) {f : CharacteristicPhase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ q, f q ∂beamNormalCharacteristicKernel b z) =
      ∫⁻ v, f (characteristicBeamJump z v)
        ∂normalGainKernel (beamPartnerKernel b) (characteristicBeamPoint z,z.2.2) := by
  rw [beamNormalCharacteristicKernel,transportedKernel_lintegral _ _ z hf,
    normalPhaseGainKernel_lintegral_gain _ _
      (f := fun y => f (characteristicEquiv.symm y)) (hf.comp characteristicEquiv.symm.measurable)]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The two atomic partners' normal-angle gain equals the outgoing-sphere gain -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem normalGain_beam_projection (b : BeamCoefficients) (p : ℝ × V) (v : V)
    (hp : 0 ≤ b.plusDensity p) (hm : 0 ≤ b.minusDensity p) :
    normalGainKernel (beamPartnerKernel b) (p,v) =
      ENNReal.ofReal (4*Real.pi*b.plusDensity p*‖v-b.plusPartner p‖) • outgoing (v,b.plusPartner p)+
      ENNReal.ofReal (4*Real.pi*b.minusDensity p*‖v-b.minusPartner p‖) • outgoing (v,b.minusPartner p) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [normalGainKernel_lintegral _ _ hf]
  simp_rw [normal_left_integral_outgoing _ _ hf,normal_right_integral_outgoing _ _ hf]
  rw [beamPartnerKernel_apply,beamMeasure]
  simp only [lintegral_add_measure,lintegral_smul_measure,lintegral_dirac,smul_eq_mul]
  rw [outgoing_swap (b.plusPartner p) v,outgoing_swap (b.minusPartner p) v,
    norm_sub_rev (b.plusPartner p) v,norm_sub_rev (b.minusPartner p) v]
  have hc (a : ℝ) (hn : 0 ≤ a) (r : ℝ) :
      2*(ENNReal.ofReal a*ENNReal.ofReal (2*Real.pi*r)) = ENNReal.ofReal (4*Real.pi*a*r) := by
    rw [← ENNReal.ofReal_mul hn,← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [show (ENNReal.ofReal (b.plusDensity p)*
      (ENNReal.ofReal (2*Real.pi*‖v-b.plusPartner p‖)*∫⁻ u, f u ∂outgoing (v,b.plusPartner p))+
      ENNReal.ofReal (b.minusDensity p)*
      (ENNReal.ofReal (2*Real.pi*‖v-b.minusPartner p‖)*∫⁻ u, f u ∂outgoing (v,b.minusPartner p)))+
      (ENNReal.ofReal (b.plusDensity p)*
      (ENNReal.ofReal (2*Real.pi*‖v-b.plusPartner p‖)*∫⁻ u, f u ∂outgoing (v,b.plusPartner p))+
      ENNReal.ofReal (b.minusDensity p)*
      (ENNReal.ofReal (2*Real.pi*‖v-b.minusPartner p‖)*∫⁻ u, f u ∂outgoing (v,b.minusPartner p))) =
      (2*(ENNReal.ofReal (b.plusDensity p)*ENNReal.ofReal (2*Real.pi*‖v-b.plusPartner p‖)))*
        (∫⁻ u, f u ∂outgoing (v,b.plusPartner p))+
      (2*(ENNReal.ofReal (b.minusDensity p)*ENNReal.ofReal (2*Real.pi*‖v-b.minusPartner p‖)))*
        (∫⁻ u, f u ∂outgoing (v,b.minusPartner p)) by ring]
  rw [hc _ hp _,
    hc _ hm _]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
