import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotUndamped
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapColdBounds
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildCharacteristics
import OAI.MathematicalPhysics.Boltzmann.Branching.DilationBoxOrder
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanBackwardMap
import OAI.MathematicalPhysics.Boltzmann.Branching.HotSeedCoreLower
import OAI.MathematicalPhysics.Boltzmann.Branching.IncomingLossRate
import OAI.MathematicalPhysics.Boltzmann.Branching.SeparationBoxContainment
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdCentralVanishing

namespace OAI

section

/-! # Positivity and local integrability of the full physical cap density -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.physical_nonneg {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (z : Published.KineticPhase) :
    0 ≤ EuclideanFlight.density q F.solution.value z :=
  mul_nonneg (H_nonneg q _) (F.solution.value_bounds _).1

theorem CapApproximation.scaled_box_integrable {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (hq : 0 ≤ q) (hr : 0 < r) (j : ℕ) :
    IntegrableOn (fun z => r⁻¹*EuclideanFlight.density q F.solution.value (kineticDilation r z))
      (separationBox j) := by
  let μ : Measure Published.KineticPhase := volume.restrict (separationBox j)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (awayKineticBox_measure_lt_top _ _ _).ne
  have hm := (EuclideanFlight.density_measurable F.solution.measurable_value q).comp
    (kineticDilation_quasiMeasurePreserving hr).measurable
  let C := r⁻¹*((1+(1/((j:ℝ)+1))^(-q))*(2*F.amplitude))
  apply (integrable_const C).mono' (hm.const_mul _).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_separationBox j)] with z hz
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) (F.physical_nonneg _))]
  have hH := H_le_off_axis hq (by positivity : 0 < 1/((j:ℝ)+1)) hz.2
  have hb := (F.solution.value_bounds (r*z.1.1,EuclideanFlight.phaseEquiv ((r • z.1.2),z.2))).2
  change r⁻¹*(H q z.2*F.solution.value _) ≤ C
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul hH hb (F.solution.value_bounds _).1 (by positivity)) (inv_nonneg.mpr hr.le)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The attained-scale hot density is dominated by the actual full density -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.hot_le_value {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) (u) :
    F.hot u ≤ F.solution.value u := by
  have hc := ((F.coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq hT).2 u).2.1
  change 0 ≤ ∑' i, F.cold i u at hc
  change F.solution.value u-(∑' i, F.cold i u) ≤ F.solution.value u
  linarith

theorem physical_scaled_twice {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (f : Published.KineticPhase → ℝ) (z : Published.KineticPhase) :
    (r/t)⁻¹*(t⁻¹*f (kineticDilation t (kineticDilation (r/t) z))) =
      r⁻¹*f (kineticDilation r z) := by
  rw [kineticDilation_mul,mul_div_cancel₀ _ ht.ne']
  field_simp

namespace AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem euclideanHot_full_bound (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (z : Published.KineticPhase) :
    0 ≤ S.euclideanHot n z ∧ S.euclideanHot n z ≤
      (S.radius n)⁻¹*EuclideanFlight.density q (F.approximation n).solution.value
        (kineticDilation (S.radius n) z) := by
  let u : ℝ × JetPrototype.Phase :=
    (S.radius n*z.1.1,(S.radius n • EuclideanFlight.spaceEquiv z.1.2,z.2))
  have hr := S.radius_pos hs₀ n
  have hn := ((F.approximation n).hot_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le).2.1 u
  have hb := (F.approximation n).hot_le_value hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le u
  have he : S.euclideanHot n z = (S.radius n)⁻¹*(H q z.2*(F.approximation n).hot u) := by
    change H q z.2*((F.approximation n).hot u/S.radius n) = _
    ring
  have hs : EuclideanFlight.spaceEquiv (S.radius n • z.1.2) =
      S.radius n • EuclideanFlight.spaceEquiv z.1.2 := by
    simp only [EuclideanFlight.spaceEquiv_apply,JetPeriodicDatum.spatialMap]
    rfl
  have hf : EuclideanFlight.density q (F.approximation n).solution.value
      (kineticDilation (S.radius n) z) = H q z.2*(F.approximation n).solution.value u := by
    change H q z.2*(F.approximation n).solution.value
      (S.radius n*z.1.1,(EuclideanFlight.spaceEquiv (S.radius n • z.1.2),z.2)) = _
    rw [hs]
  rw [he,hf]
  exact ⟨mul_nonneg (inv_nonneg.mpr hr.le) (mul_nonneg (H_nonneg q _) hn),
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (H_nonneg q _)) (inv_nonneg.mpr hr.le)⟩

end AttainedCapSequence
end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Actual undamped hot evolution along backward Euclidean paths -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem backward_normalizedHot (S : AttainedCapSequence F) (n : ℕ)
    (p : Velocity × Velocity) (t s : ℝ) :
    S.normalizedHot n (s,JetBarrier.flight s (EuclideanFlight.phaseEquiv (EuclideanFlight.flight (-t) p))) =
      S.euclideanHot n (PositiveIteration.flight ((t,p.1),p.2) s)/H q p.2 := by
  rw [← EuclideanFlight.backward_kineticMap]
  change S.normalizedHot n _ = (H q p.2*S.normalizedHot n _)/H q p.2
  rw [mul_div_cancel_left₀ _ (H_pos q p.2).ne']
  rfl

theorem backward_normalizedSource (S : AttainedCapSequence F) (n : ℕ)
    (p : Velocity × Velocity) (t s : ℝ) :
    S.rescaledHotSource n (s,JetBarrier.flight s (EuclideanFlight.phaseEquiv (EuclideanFlight.flight (-t) p))) =
      S.euclideanHotSource n (PositiveIteration.flight ((t,p.1),p.2) s)/H q p.2 := by
  rw [← EuclideanFlight.backward_kineticMap]
  change S.rescaledHotSource n _ = (H q p.2*S.rescaledHotSource n _)/H q p.2
  rw [mul_div_cancel_left₀ _ (H_pos q p.2).ne']
  rfl

theorem normalizedHot_backward_mild (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hT : S.radius n*t ≤ shrinkingHorizon F.horizonScale n) :
    ∀ᵐ p : Velocity × Velocity, S.euclideanHot n ((t,p.1),p.2)/H q p.2 =
      (F.approximation n).hotInitial (PositiveIntegral.scalePhase (S.radius n)
        (EuclideanFlight.phaseEquiv (EuclideanFlight.flight (-t) p)))/S.radius n+
      ∫ s in 0..t, S.euclideanHotSource n (PositiveIteration.flight ((t,p.1),p.2) s)/H q p.2 := by
  have hp := (EuclideanFlight.phaseEquiv_measurePreserving.comp
    (EuclideanFlight.flight_measurePreserving (-t))).quasiMeasurePreserving.ae
    (S.normalizedHot_undamped hs₀ hsmax hη hηmax hK hd₀ hq n ht hT)
  filter_upwards [hp] with p hp
  change S.normalizedHot n (t,JetBarrier.flight t
    (EuclideanFlight.phaseEquiv (EuclideanFlight.flight (-t) p))) = _ at hp
  rw [S.backward_normalizedHot n p t t] at hp
  simp only [PositiveIteration.flight,sub_self,zero_smul,sub_zero] at hp
  rw [hp]
  congr 1
  exact intervalIntegral.integral_congr (fun s _ => S.backward_normalizedSource n p t s)

theorem normalizedHot_backward_source_integrable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hT : S.radius n*t ≤ shrinkingHorizon F.horizonScale n) :
    ∀ᵐ p : Velocity × Velocity, IntervalIntegrable
      (fun s => S.euclideanHotSource n (PositiveIteration.flight ((t,p.1),p.2) s)/H q p.2) volume 0 t := by
  have hm := S.normalizedHot_mild hs₀ hsmax hη hηmax hK hd₀ hq n hT
  have hfm := S.normalizedHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq n
  obtain ⟨hgm,B,hB⟩ := S.rescaledHotForcing_properties hs₀ hsmax hη hηmax hK hd₀ hq n
  have hi : Measurable (fun p =>
      (F.approximation n).hotInitial (PositiveIntegral.scalePhase (S.radius n) p)/S.radius n) :=
    (((F.approximation n).hotInitial_measurable).comp
      (by unfold PositiveIntegral.scalePhase; fun_prop)).div_const _
  have hh := PositiveIntegral.netSource_integrable_characteristic ht hi hfm hgm hB hm
  have hp := (EuclideanFlight.phaseEquiv_measurePreserving.comp
    (EuclideanFlight.flight_measurePreserving (-t))).quasiMeasurePreserving.ae hh
  filter_upwards [hp] with p hp
  simpa only [Function.comp_apply,S.normalizedHot_netSource hs₀ n,S.backward_normalizedSource n p t] using hp

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot mild formula between two nonnegative times -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem normalizedHot_backward_between (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {a t : ℝ}
    (ha : 0 ≤ a) (hat : a ≤ t) (hT : S.radius n*t ≤ shrinkingHorizon F.horizonScale n) :
    ∀ᵐ p : Velocity × Velocity,
      S.euclideanHot n ((t,p.1),p.2)/H q p.2 =
        S.euclideanHot n (PositiveIteration.flight ((t,p.1),p.2) a)/H q p.2+
        ∫ s in a..t, S.euclideanHotSource n (PositiveIteration.flight ((t,p.1),p.2) s)/H q p.2 := by
  have hA := (mul_le_mul_of_nonneg_left hat (S.radius_pos hs₀ n).le).trans hT
  have hpA := (EuclideanFlight.phaseEquiv_measurePreserving.comp
    (EuclideanFlight.flight_measurePreserving (-t))).quasiMeasurePreserving.ae
    (S.normalizedHot_undamped hs₀ hsmax hη hηmax hK hd₀ hq n ha hA)
  have hpT := S.normalizedHot_backward_mild hs₀ hsmax hη hηmax hK hd₀ hq n (ha.trans hat) hT
  have hpi := S.normalizedHot_backward_source_integrable hs₀ hsmax hη hηmax hK hd₀ hq n
    (ha.trans hat) hT
  filter_upwards [hpA,hpT,hpi] with p hpA hpT hpi
  simp only [Function.comp_apply] at hpA
  change S.normalizedHot n (a,JetBarrier.flight a
    (EuclideanFlight.phaseEquiv (EuclideanFlight.flight (-t) p))) = _ at hpA
  rw [S.backward_normalizedHot n p t a] at hpA
  simp_rw [S.backward_normalizedSource n p t] at hpA
  have hiA := hpi.mono_set (show uIcc 0 a ⊆ uIcc 0 t by
    rw [uIcc_of_le ha,uIcc_of_le (ha.trans hat)]
    exact Icc_subset_Icc le_rfl hat)
  have hiAT := hpi.mono_set (show uIcc a t ⊆ uIcc 0 t by
    rw [uIcc_of_le hat,uIcc_of_le (ha.trans hat)]
    exact Icc_subset_Icc ha le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hiA hiAT
  linarith

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot box mass is bounded by an original-scale full box mass -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem hot_box_mass_comparison (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : 0 ≤ q) (hqmax : q < 2)
    (n : ℕ) {t A R ε : ℝ} {j : ℕ} (ht : 0 < t) (hA : A ≤ 1)
    (htime : (S.radius n/t)*A ≤ 1) (hspace : (S.radius n/t)*R ≤ (j:ℝ)+1)
    (hR : R ≤ (j:ℝ)+1) (hε : 1/((j:ℝ)+1) ≤ ε) :
    0 ≤ (∫ z in awayKineticBox A R ε, S.euclideanHot n z) ∧
      (∫ z in awayKineticBox A R ε, S.euclideanHot n z) ≤
        ((S.radius n/t)^5)⁻¹*scaledBoxMass t
          (EuclideanFlight.density q (F.approximation n).solution.value) j := by
  let f := EuclideanFlight.density q (F.approximation n).solution.value
  have hr := S.radius_pos hs₀ n
  have hb := S.euclideanHot_full_bound hs₀ hsmax hη hηmax hK hd₀ hqmax n
  have hi := ((F.approximation n).scaled_box_integrable hq hr j).mono_set
    (awayKineticBox_subset_separationBox hA hR hε)
  refine ⟨integral_nonneg (fun z => (hb z).1),?_⟩
  calc
    _ ≤ ∫ z in awayKineticBox A R ε, (S.radius n)⁻¹*f (kineticDilation (S.radius n) z) :=
      integral_mono_of_nonneg (ae_of_all _ (fun z => (hb z).1)) hi
        (ae_of_all _ (fun z => (hb z).2))
    _ = ∫ z in awayKineticBox A R ε, (S.radius n/t)⁻¹*
        (t⁻¹*f (kineticDilation t (kineticDilation (S.radius n/t) z))) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => (physical_scaled_twice hr ht f z).symm)
    _ ≤ _ := dilation_box_mass_le (div_pos hr ht) htime hspace hR hε
      ((F.approximation n).scaled_box_integrable hq ht j)
      (fun z => mul_nonneg (inv_nonneg.mpr ht.le) ((F.approximation n).physical_nonneg _))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Finite collision measures for the actual limiting cold–hot background -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.incomingRate_integrable (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) :
    Integrable incomingRate (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)) := by
  have ht : ∀ᵐ x ∂coldCylinderVolume a A R, x.1 ≤ A :=
    (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).mono
      (fun _ hx => hx.2)
  have hm := E.mixedMeasure_gaussian_bound ha hA hK hα hγ hq (coldCylinderVolume a A R) ht
  apply incomingRate_integrable_of_gaussian
  apply hm.trans_lt
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem HotLimitExtraction.incomingGainMeasure_finite (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) :
    IsFiniteMeasure (incomingGainMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) := by
  let _ : SFinite (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)) := by
    unfold HotLimitExtraction.mixedMeasure
    infer_instance
  exact CollisionCompactness.incomingGainMeasure_finite (E.incomingRate_integrable ha hA hK hα hγ hq)

theorem HotLimitExtraction.incomingLossMeasure_finite (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) :
    IsFiniteMeasure (incomingLossMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) := by
  let _ : SFinite (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)) := by
    unfold HotLimitExtraction.mixedMeasure
    infer_instance
  exact CollisionCompactness.incomingLossMeasure_finite (E.incomingRate_integrable ha hA hK hα hγ hq)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual initial hot ratio is small with the shot coefficient -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.hotInitial_eq {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (p : JetPrototype.Phase) :
    F.hotInitial p = F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p := by
  simp only [CapApproximation.hotInitial,initial,seed,add_sub_cancel_left]

namespace AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem hotInitial_ratio_bound (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 ≤ η) (hq : 0 ≤ q)
    (n : ℕ) (p : JetPrototype.Phase) :
    (F.approximation n).hotInitial p/S.radius n ≤
      (F.approximation n).coefficient*(HotSeedProfile.bound/HotSeedProfile.normLower q) := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (F.indices n+1)
  have hδmax : DatumBounds.scale s₀ η (F.indices n+1) ≤ 1 := by
    have hh := JetGeometry.scale_antitone hs₀.le hη (Nat.zero_le (F.indices n+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at hh
    linarith
  have hcoef := (F.approximation n).coefficient_mem.1
  have hM : 0 ≤ HotSeedProfile.bound/HotSeedProfile.normLower q :=
    div_nonneg HotSeedProfile.bound_pos.le (HotSeedProfile.normLower_pos q).le
  rw [(F.approximation n).hotInitial_eq]
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (HotSeedProfile.normalized_uniform_bound hq hδ hδmax p) hcoef)
      (S.radius_pos hs₀ n).le).trans
  have hδr : DatumBounds.scale s₀ η (F.indices n+1) ≤ S.radius n := by
    dsimp [radius]
    linarith [(S.time_mem n).1]
  apply (div_le_iff₀ (S.radius_pos hs₀ n)).mpr
  calc
    _ = ((F.approximation n).coefficient*(HotSeedProfile.bound/HotSeedProfile.normLower q))*
      DatumBounds.scale s₀ η (F.indices n+1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hδr (mul_nonneg hcoef hM)

end AttainedCapSequence
end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Integrability of the actual limiting attenuation density -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem slab_frequency_measurable {a θ K α γ : ℝ}
    (ha : 0 < a) (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (η l : ℝ) :
    Measurable (fun z : (ℝ × JetPrototype.Space) × Velocity =>
      frequency θ η l K α γ (max a z.1.1) z.1.2 z.2) := by
  have hm := (clamped_frequency_measurable hθ hK hα hγ η l).comp
    (show Measurable (fun z : (ℝ × JetPrototype.Space) × Velocity =>
      ((max a z.1.1,z.1.2),z.2)) from by fun_prop)
  convert hm using 1
  funext z
  change frequency θ η l K α γ (max a z.1.1) z.1.2 z.2 =
    frequency θ η l K α γ (max 0 (max a z.1.1)) z.1.2 z.2
  rw [max_eq_right (ha.le.trans (le_max_left a z.1.1))]

end BoltzmannNonuniqueness.GeometricBackground

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.loss_density_integrable (E : HotLimitExtraction S)
    {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) (μ : Measure (ℝ × JetPrototype.Space)) [IsFiniteMeasure μ]
    (ht : ∀ᵐ x ∂μ, x.1 ≤ A) :
    Integrable (fun z : HotKineticPhase => E.cappedHot z*
      GeometricBackground.frequency E.phase η E.fraction K α γ (max a z.1.1) z.1.2 z.2)
      (μ.prod volume) := by
  have hv : Integrable (fun v : Velocity => (‖v‖+1+α)*H q v) := by
    convert (integrable_moment_H hq 1).add ((integrable_H hq).const_mul (1+α)) using 1
    funext v
    simp only [pow_one,Pi.add_apply]
    ring
  let C := (A+1)*(GeometricBackground.lossCoefficient K α γ/a)
  have hm := E.cappedHot_measurable.mul (GeometricBackground.slab_frequency_measurable ha
    (zero_lt_one.trans_le E.phase_mem.1) hK hα.le hγ.le η E.fraction)
  apply ((hv.const_mul C).comp_snd μ).mono' hm.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ht] with z hz
  have hc : E.cappedHot z ≤ (A+1)*H q z.2 := by
    apply (min_le_right _ _).trans
    apply mul_le_mul_of_nonneg_right _ (H_nonneg q z.2)
    exact max_le (by linarith) (by linarith [E.fraction_mem.2])
  have hf := GeometricBackground.frequency_slab_bound (η := η)
    (zero_lt_one.trans_le E.phase_mem.1) E.fraction_mem.1 hK hα hγ ha
    (le_max_left a z.1.1) z.1.2 z.2
  simp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (E.cappedHot_nonneg z)
    (GeometricBackground.frequency_nonneg _ _ _ _ _ _ _ _ _))]
  calc
    _ ≤ ((A+1)*H q z.2)*((GeometricBackground.lossCoefficient K α γ/a)*(‖z.2‖+1+α)) :=
      mul_le_mul hc hf (GeometricBackground.frequency_nonneg _ _ _ _ _ _ _ _ _)
        (mul_nonneg (by linarith) (H_nonneg q z.2))
    _ = _ := by dsimp only [C]; ring

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A positive shot coefficient preserves a fixed dilated initial core -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem initial_core_lower (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 ≤ η) (hq : 0 ≤ q)
    (n : ℕ) {ell c : ℝ} (_hell : 0 < ell) (hc : 0 ≤ c)
    (hl : ell/2 ≤ S.coldFraction n) (hcoef : c ≤ (F.approximation n).coefficient)
    {p : JetPrototype.Phase} (hx : ‖p.1‖ < ell/16) (hv : p.2 ∈ HotSeedProfile.velocityCore) :
    c*(ell/2)*(HotSeedProfile.normLower q/HotSeedProfile.bound) ≤
      (F.approximation n).hotInitial (PositiveIntegral.scalePhase (S.radius n) p)/S.radius n := by
  have hr := S.radius_pos hs₀ n
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (F.indices n+1)
  have hδmax : DatumBounds.scale s₀ η (F.indices n+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη (Nat.zero_le (F.indices n+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hδeq : S.radius n*S.coldFraction n = DatumBounds.scale s₀ η (F.indices n+1) := by
    dsimp [coldFraction]; field_simp
  have hspace : ‖(PositiveIntegral.scalePhase (S.radius n) p).1‖ <
      DatumBounds.scale s₀ η (F.indices n+1)/8 := by
    change ‖S.radius n • p.1‖ < _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,← hδeq]
    nlinarith [mul_lt_mul_of_pos_left hx hr,mul_le_mul_of_nonneg_left hl hr.le]
  have hseed := HotSeedProfile.normalized_core_lower hq hδ hδmax hspace hv
  have hratio : 0 ≤ HotSeedProfile.normLower q/HotSeedProfile.bound :=
    div_nonneg (HotSeedProfile.normLower_pos q).le HotSeedProfile.bound_pos.le
  rw [(F.approximation n).hotInitial_eq]
  apply (le_div_iff₀ hr).mpr
  calc
    _ = c*((S.radius n*(ell/2))*(HotSeedProfile.normLower q/HotSeedProfile.bound)) := by ring
    _ ≤ c*(DatumBounds.scale s₀ η (F.indices n+1)*(HotSeedProfile.normLower q/HotSeedProfile.bound)) := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply mul_le_mul_of_nonneg_right _ hratio
      rw [← hδeq]
      exact mul_le_mul_of_nonneg_left hl hr.le
    _ ≤ (F.approximation n).coefficient*HotSeedProfile.normalized q
        (DatumBounds.scale s₀ η (F.indices n+1)) (PositiveIntegral.scalePhase (S.radius n) p) :=
      mul_le_mul hcoef hseed (mul_nonneg hδ.le hratio) (F.approximation n).coefficient_mem.1

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual atomic-background loss measure has the expected density -/

noncomputable section

open MeasureTheory ProbabilityTheory
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.loss_measure_density_integral (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (μ : Measure (ℝ × JetPrototype.Space)) [SFinite μ]
    (hi : Integrable incomingRate (E.mixedMeasure ha hK hα hγ μ))
    {ψ : HotKineticPhase → ℝ} (hψ : Measurable ψ) {B : ℝ} (hB : ∀ z, |ψ z| ≤ B) :
    (∫ z, ψ z ∂incomingLossMeasure (E.mixedMeasure ha hK hα hγ μ)) =
      ∫ x, ∫ v, ψ (x,v)*E.cappedHot (x,v)*
        GeometricBackground.frequency E.phase η E.fraction K α γ (max a x.1) x.2 v ∂volume ∂μ := by
  let _ : SFinite (E.mixedMeasure ha hK hα hγ μ) := by
    unfold HotLimitExtraction.mixedMeasure
    infer_instance
  have htest : Measurable (fun z : (ℝ × JetPrototype.Space) × (Velocity × Velocity) =>
      ψ (z.1,z.2.2)) := hψ.comp (measurable_fst.prodMk measurable_snd.snd)
  have hF : Integrable (fun z => incomingRate z*ψ (z.1,z.2.2))
      (E.mixedMeasure ha hK hα hγ μ) := by
    simpa only [mul_comm] using hi.bdd_mul htest.aestronglyMeasurable (ae_of_all _ (fun z => hB _))
  rw [incomingLossMeasure_rate_integral hi hψ hB]
  unfold HotLimitExtraction.mixedMeasure at hF ⊢
  rw [Measure.integral_compProd hF]
  apply integral_congr_ae
  filter_upwards [(Measure.integrable_compProd_iff hF.aestronglyMeasurable).mp hF |>.1] with x hx
  let _ : IsFiniteMeasure (E.background (max a x.1) x.2) :=
    GeometricBackground.background_finite E.phase η E.fraction K α γ (max a x.1) x.2
  rw [E.mixedKernel_apply] at hx ⊢
  rw [integral_prod_symm _ hx,E.hotKernel_integral]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [incomingRate]
  rw [integral_mul_const,integral_const_mul]
  simp only [norm_sub_rev]
  unfold GeometricBackground.frequency HotLimitExtraction.background
  ring

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Attenuation density on the actual positive-time cylinder -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.loss_measure_product_integral (E : HotLimitExtraction S)
    {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) (μ : Measure (ℝ × JetPrototype.Space)) [IsFiniteMeasure μ]
    (ht : ∀ᵐ x ∂μ, x.1 ≤ A)
    (hiR : Integrable incomingRate (E.mixedMeasure ha hK hα hγ μ))
    {ψ : HotKineticPhase → ℝ}
    (hψ : Measurable ψ) {B : ℝ} (hB : ∀ z, |ψ z| ≤ B) :
    (∫ z, ψ z ∂incomingLossMeasure (E.mixedMeasure ha hK hα hγ μ)) =
      ∫ z, ψ z*E.cappedHot z*
        GeometricBackground.frequency E.phase η E.fraction K α γ (max a z.1.1) z.1.2 z.2
        ∂μ.prod volume := by
  have hi := E.loss_density_integrable ha hA hK hα hγ hq μ ht
  have hip : Integrable (fun z => ψ z*E.cappedHot z*
      GeometricBackground.frequency E.phase η E.fraction K α γ (max a z.1.1) z.1.2 z.2)
      (μ.prod volume) := by
    simpa only [mul_assoc] using hi.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hB)
  rw [E.loss_measure_density_integral ha hK hα hγ μ hiR hψ hB,integral_prod _ hip]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The limiting loss is hot density times the atomic-background frequency -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.loss_cylinder_ae (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 ≤ a) :
    (fun z : HotKineticPhase => E.cappedHot z*
      GeometricBackground.frequency E.phase η E.fraction K α γ (max a z.1.1) z.1.2 z.2)
    =ᵐ[(coldCylinderVolume a A R).prod volume]
      (fun z => E.hotLimit z*GeometricBackground.frequency E.phase η E.fraction K α γ
        z.1.1 z.1.2 z.2) := by
  have ht : ∀ᵐ x ∂coldCylinderVolume a A R, a ≤ x.1 :=
    (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).mono
      (fun _ hx => hx.1)
  have he : E.cappedHot =ᵐ[(coldCylinderVolume a A R).prod volume] E.hotLimit := by
    rw [coldCylinderVolume_eq_hot_restrict ha]
    exact (E.cappedHot_eq A R).filter_mono ae_restrict_le
  filter_upwards [he,Measure.quasiMeasurePreserving_fst.ae ht] with z hz ht
  rw [hz,max_eq_right ht]

theorem HotLimitExtraction.actual_loss_cylinder_integrable (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) :
    Integrable (fun z : HotKineticPhase => E.hotLimit z*
      GeometricBackground.frequency E.phase η E.fraction K α γ z.1.1 z.1.2 z.2)
      ((coldCylinderVolume a A R).prod volume) := by
  apply (E.loss_density_integrable ha (ha.le.trans haA) hK hα hγ hq
    (coldCylinderVolume a A R) ?_).congr (E.loss_cylinder_ae ha.le)
  exact (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).mono
    (fun _ hx => hx.2)

theorem HotLimitExtraction.actual_loss_cylinder_integral (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) {ψ : HotKineticPhase → ℝ}
    (hψ : Measurable ψ) {B : ℝ} (hB : ∀ z, |ψ z| ≤ B) :
    (∫ z, ψ z ∂incomingLossMeasure
      (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) =
      ∫ z, ψ z*(E.hotLimit z*GeometricBackground.frequency E.phase η E.fraction K α γ
        z.1.1 z.1.2 z.2) ∂(coldCylinderVolume a A R).prod volume := by
  rw [E.loss_measure_product_integral ha (ha.le.trans haA) hK hα hγ hq
    (coldCylinderVolume a A R)
    ((Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).mono
      (fun _ hx => hx.2))
    (E.incomingRate_integrable ha (ha.le.trans haA) hK hα hγ hq) hψ hB]
  apply integral_congr_ae
  filter_upwards [E.loss_cylinder_ae (R := R) (A := A) ha.le] with z hz
  rw [mul_assoc,hz]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
