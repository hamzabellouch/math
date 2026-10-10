import OAI.MathematicalPhysics.Boltzmann.Branching.CausalConvolution
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanKineticMap
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedGainSmoothingAE
import OAI.MathematicalPhysics.Boltzmann.Compactness.MeasurableResolvent

namespace OAI

section

/-! # The damped resolvent's free flight preserves kinetic Lebesgue measure -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.Published

def resolventBack (s : ℝ) (z : KineticPhase) : KineticPhase :=
  ((z.1.1-s,z.1.2-s • z.2),z.2)

def resolventBackEquiv (s : ℝ) : KineticPhase ≃ᵐ KineticPhase where
  toFun := resolventBack s
  invFun := resolventBack (-s)
  left_inv z := by
    dsimp [resolventBack]
    simp
  right_inv z := by
    dsimp [resolventBack]
    simp
  measurable_toFun := by
    change Measurable (resolventBack s)
    unfold resolventBack
    fun_prop
  measurable_invFun := by
    change Measurable (resolventBack (-s))
    unfold resolventBack
    fun_prop

theorem resolventBack_measurePreserving (s : ℝ) :
    MeasurePreserving (resolventBack s) (volume : Measure KineticPhase) volume := by
  have ha := measurePreserving_prodAssoc (volume : Measure ℝ)
    (volume : Measure Velocity) (volume : Measure Velocity)
  have hb := (measurePreserving_add_right (volume : Measure ℝ) (-s)).prod
    (EuclideanFlight.flight_measurePreserving (-s))
  have h := ha.symm.comp (hb.comp ha)
  convert h using 1
  funext z
  change ((z.1.1-s,z.1.2-s • z.2),z.2) =
    ((z.1.1+ -s,z.1.2+(-s) • z.2),z.2)
  simp only [sub_eq_add_neg,neg_smul]

theorem lintegral_resolventBack (s : ℝ) (f : KineticPhase → ℝ≥0∞) :
    (∫⁻ z, f (resolventBack s z)) = ∫⁻ z, f z :=
  (resolventBack_measurePreserving s).lintegral_comp_emb
    (resolventBackEquiv s).measurableEmbedding f

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Exact L1 mass preservation for the nonnegative damped transport resolvent -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Published

def nonnegativeResolvent (f : KineticPhase → ℝ≥0∞) (z : KineticPhase) : ℝ≥0∞ :=
  ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s))*f (resolventBack s z)

theorem lintegral_exp_neg_one :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s))) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
    (ae_of_all _ (fun s => (Real.exp_pos (-s)).le)),integral_exp_neg_Ioi_zero]
  norm_num

theorem nonnegativeResolvent_measurable {f : KineticPhase → ℝ≥0∞}
    (hf : Measurable f) : Measurable (nonnegativeResolvent f) := by
  have hm : Measurable (fun p : KineticPhase × ℝ =>
      ENNReal.ofReal (Real.exp (-p.2))*f (resolventBack p.2 p.1)) := by
    apply Measurable.mul (by fun_prop)
    apply hf.comp
    unfold resolventBack
    fun_prop
  exact hm.lintegral_prod_right'

theorem lintegral_nonnegativeResolvent {f : KineticPhase → ℝ≥0∞}
    (hf : Measurable f) : (∫⁻ z, nonnegativeResolvent f z) = ∫⁻ z, f z := by
  have hm : Measurable (fun p : KineticPhase × ℝ =>
      ENNReal.ofReal (Real.exp (-p.2))*f (resolventBack p.2 p.1)) := by
    apply Measurable.mul (by fun_prop)
    apply hf.comp
    unfold resolventBack
    fun_prop
  unfold nonnegativeResolvent
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hi (s : ℝ) :
      (∫⁻ z : KineticPhase, ENNReal.ofReal (Real.exp (-s))*f (resolventBack s z)) =
        ENNReal.ofReal (Real.exp (-s))*(∫⁻ z, f z) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_resolventBack]
  simp_rw [hi]
  rw [lintegral_mul_const _]
  · rw [lintegral_exp_neg_one,one_mul]
  · exact (by fun_prop : Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (-s))))

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The actual local solutions are the precise published transport resolvents -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem resolvent_representation (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0) :
    ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      χ ((T,p.1),p.2)*density q F.value ((T,p.1),p.2) =
        Published.transportResolvent
          (localizedSource U χ (density q F.value) (source b q F.value)) ((T,p.1),p.2) := by
  have hl := smooth_localized hcarleman F hq₁ hq₂ hb hR hT hTU hloss hf₀ hχ hzero
  have hback := (flight_measurePreserving (-T)).quasiMeasurePreserving.ae hl
  filter_upwards [hback] with p hp
  simp only [characteristic_endpoint,characteristic_back] at hp
  rw [TransportPrimitive.transportResolvent_eq
    (fun z hz => localizedSource_causal U χ _ _ z hz) _ hT]
  rw [hp]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  dsimp only
  rw [localizedSource_on χ _ _ _ ⟨ht.1,ht.2.trans hTU⟩]

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # The actual signed transport resolvent is an L1 contraction -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Published

theorem transportResolvent_enorm_le (r : KineticPhase → ℝ) (z : KineticPhase) :
    ‖transportResolvent r z‖ₑ ≤ nonnegativeResolvent (fun p => ‖r p‖ₑ) z := by
  unfold transportResolvent nonnegativeResolvent
  rw [← restrict_Ioi_eq_restrict_Ici]
  calc
    _ ≤ ∫⁻ s in Ioi (0 : ℝ), ‖Real.exp (-s)*r (resolventBack s z)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ = _ := by
      apply lintegral_congr
      intro s
      rw [enorm_mul]
      congr 1
      simp [Real.enorm_eq_ofReal,le_of_lt (Real.exp_pos (-s))]

theorem lintegral_transportResolvent_enorm_le {r : KineticPhase → ℝ}
    (hr : Measurable r) :
    (∫⁻ z, ‖transportResolvent r z‖ₑ) ≤ ∫⁻ z, ‖r z‖ₑ := by
  calc
    _ ≤ ∫⁻ z, nonnegativeResolvent (fun p => ‖r p‖ₑ) z :=
      lintegral_mono (transportResolvent_enorm_le r)
    _ = _ := lintegral_nonnegativeResolvent hr.enorm

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The velocity-averaged resolvent has its actual L1 operator bound -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.Published

theorem transportResolvent_integrable {r : KineticPhase → ℝ}
    (hr : Measurable r) (hi : Integrable r) : Integrable (transportResolvent r) := by
  refine ⟨(transportResolvent_measurable hr).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (lintegral_transportResolvent_enorm_le hr) hi.hasFiniteIntegral

theorem resolventAverage_enorm_le {r : KineticPhase → ℝ} (hr : Measurable r)
    {ψ : Velocity → ℝ} {M : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M) (z : SpaceTime) :
    ‖resolventAverage r ψ z‖ₑ ≤ ENNReal.ofReal M * ∫⁻ v, ‖transportResolvent r (z,v)‖ₑ := by
  have hu : Measurable (fun v : Velocity => transportResolvent r (z,v)) :=
    (transportResolvent_measurable hr).comp measurable_prodMk_left
  calc
    _ ≤ ∫⁻ v, ‖ψ v * transportResolvent r (z,v)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ v, ENNReal.ofReal M * ‖transportResolvent r (z,v)‖ₑ := by
      apply lintegral_mono
      intro v
      change ‖ψ v * transportResolvent r (z,v)‖ₑ ≤ _
      rw [enorm_mul]
      exact mul_le_mul' (by simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hM v)) le_rfl
    _ = _ := lintegral_const_mul _ hu.enorm

theorem lintegral_resolventAverage_enorm_le {r : KineticPhase → ℝ} (hr : Measurable r)
    {ψ : Velocity → ℝ} {M : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M) :
    (∫⁻ z, ‖resolventAverage r ψ z‖ₑ) ≤ ENNReal.ofReal M * ∫⁻ p, ‖r p‖ₑ := by
  have hu := (transportResolvent_measurable hr).enorm
  calc
    _ ≤ ∫⁻ z : SpaceTime, ENNReal.ofReal M * ∫⁻ v : Velocity, ‖transportResolvent r (z,v)‖ₑ :=
      lintegral_mono (resolventAverage_enorm_le hr hM)
    _ = ENNReal.ofReal M * ∫⁻ z : SpaceTime, ∫⁻ v : Velocity, ‖transportResolvent r (z,v)‖ₑ :=
      lintegral_const_mul _ hu.lintegral_prod_right'
    _ = ENNReal.ofReal M * ∫⁻ p : KineticPhase, ‖transportResolvent r p‖ₑ := by
      congr 1
      change (∫⁻ z : SpaceTime, ∫⁻ v : Velocity, ‖transportResolvent r (z,v)‖ₑ) =
        ∫⁻ p : KineticPhase, ‖transportResolvent r p‖ₑ ∂(volume.prod volume)
      exact (lintegral_prod _ hu.aemeasurable).symm
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_transportResolvent_enorm_le hr)

end BoltzmannNonuniqueness.Published

end

end

end OAI
