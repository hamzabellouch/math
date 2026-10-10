import OAI.MathematicalPhysics.Boltzmann.Branching.FlightConeLocalization
import OAI.MathematicalPhysics.Boltzmann.Branching.LateBoxCommonDamping
import OAI.MathematicalPhysics.Boltzmann.Branching.ScaledBoundedEvent
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteEntryPhaseBound
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteGainHistoryComparison
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedBlockComparison
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedDampedBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalGlobalRenormalized
import OAI.MathematicalPhysics.Boltzmann.Jets.BeamNormalCharacteristicIdentity
import OAI.MathematicalPhysics.Boltzmann.Jets.BeamNormalOutgoing
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricAnnularFrequency
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricDampedRetention
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricPositiveCompact

namespace OAI

section

/-! # Local density normalization cancels from the actual beam measure and frequency -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem scaled_beamDensity {θ η α γ r s K σ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (p : ℝ × Velocity) :
    (K/(4*r))*beamDensity θ η α γ r σ p =
      (K/(4*s))*beamDensity θ η α γ s σ p := by
  unfold beamDensity
  field_simp

theorem scaled_beamMeasure {θ K α γ r s : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hr : 0 < r) (hs : 0 < s) (η : ℝ) (p : ℝ × Velocity) :
    ENNReal.ofReal (K/(4*r)) • beamMeasure (beamCoefficients hθ hα hγ η r) p =
      ENNReal.ofReal (K/(4*s)) • beamMeasure (beamCoefficients hθ hα hγ η s) p := by
  simp only [beamMeasure,beamCoefficients,smul_add,smul_smul]
  rw [← ENNReal.ofReal_mul (show 0 ≤ K/(4*r) by positivity),
    ← ENNReal.ofReal_mul (show 0 ≤ K/(4*r) by positivity),
    ← ENNReal.ofReal_mul (show 0 ≤ K/(4*s) by positivity),
    ← ENNReal.ofReal_mul (show 0 ≤ K/(4*s) by positivity),
    scaled_beamDensity hr hs,scaled_beamDensity hr hs]

theorem scaled_characteristicBeamFrequency {θ α γ r s K : ℝ}
    (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r) (hs : 0 < s)
    (η : ℝ) (z : EuclideanFlight.CharacteristicPhase) :
    (K/(4*r))*characteristicBeamFrequency (beamCoefficients hθ hα hγ η r) z =
      (K/(4*s))*characteristicBeamFrequency (beamCoefficients hθ hα hγ η s) z := by
  unfold characteristicBeamFrequency mediumFrequency
  simp only [beamCoefficients]
  calc
    _ = 2*Real.pi *
        (((K/(4*r))*beamDensity θ η α γ r 1 (characteristicBeamPoint z))*
            ‖z.2.2-beamVelocity θ η α γ 1 (characteristicBeamPoint z)‖+
         ((K/(4*r))*beamDensity θ η α γ r (-1) (characteristicBeamPoint z))*
            ‖z.2.2-beamVelocity θ η α γ (-1) (characteristicBeamPoint z)‖) := by ring
    _ = _ := by rw [scaled_beamDensity hr hs,scaled_beamDensity hr hs]; ring

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Actual geometric gain histories enter the localized normal-angle comparison -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.GeometricBackground

theorem beamPartner_norm_le_two {θ α γ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hαsmall : α ≤ 1) (η r : ℝ) (p : ℝ × Velocity) :
    ‖(beamCoefficients hθ hα hγ η r).plusPartner p‖ ≤ 2 ∧
    ‖(beamCoefficients hθ hα hγ η r).minusPartner p‖ ≤ 2 := by
  have hb (σ : ℝ) (hσ : |σ| = 1) : ‖beamVelocity θ η α γ σ p‖ ≤ 2 := by
    have he := beamVelocity_error hα θ η γ σ p
    have ht := norm_sub_norm_le (beamVelocity θ η α γ σ p) (σ • beamAxis)
    rw [norm_smul,Real.norm_eq_abs,hσ,axis_norms.2.2,mul_one] at ht
    linarith
  exact ⟨hb 1 (by norm_num),hb (-1) (by norm_num)⟩

theorem geometric_finite_gain_endpoint_le
    {θ η α γ r t h R a l : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hαsmall : α ≤ 1) (hr : 0 ≤ r) (hh : 0 ≤ h) (ha : a ≤ t) (hl : 0 ≤ l)
    (N : ℕ) (hshort : h*(R+2*N) ≤ 1) (x v : Velocity)
    (hx : Real.exp η*l+1 < ‖VelocityWeight.transverse x‖) (hv : ‖v‖ ≤ R)
    (C : ℝ≥0) {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω)
    (hΩcone : ∀ n ≤ N, ∀ q, finiteFlightCone N n h R x q →
      flightCharacteristicEquiv (t+h) q ∈ Ω)
    {A : Set (Velocity × Velocity)} (hA : MeasurableSet A) :
    physicalGainEndpoint (beamCoefficients hθ hα hγ η r) (t+h) C N (h,(x,v)) A ≤
      (WeakTime.phaseEndpointKernel C (t+h) ∘ₖ
        ((((localizedNormalBeamKernel (beamCoefficients hθ hα hγ η r) 1 C a η l hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc t (t+h)))) ∘ₖ
            WeakTime.residenceKernel C (t+h))^N))
        (flightCharacteristicEquiv (t+h) (h,(x,v))) (flight (t+h) ⁻¹' A) := by
  have he : t+h-h = t := by ring
  simpa only [he] using finite_gain_endpoint_le_localized
    (beamCoefficients hθ hα hγ η r) C (t+h) a η l h R N x v hh hv hΩ hΩcone
    (fun _ _ q _ => beamPartner_norm_le_two hθ hα hγ hαsmall η r (t+h-q.1,q.2.1))
    (fun _ _ q hq => ⟨finiteFlightCone_cold_domain ha hl hshort hx hq,
      beamDensity_nonneg hθ hα hγ hr η 1 _,beamDensity_nonneg hθ hα hγ hr η (-1) _⟩) hA

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Actual geometric coefficients on the cone visited by a finite history -/

noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.ReferenceGeometry

def characteristicHistoryCore (t₀ R : ℝ) (x : V) : Set (ℝ × WeakTime.Phase) :=
  {z | ‖z.2.1+t₀ • z.2.2-x‖ ≤ R ∧ ‖z.2.2‖ ≤ 6}

theorem characteristicHistoryCore_measurable (t₀ R : ℝ) (x : V) :
    MeasurableSet (characteristicHistoryCore t₀ R x) := by
  unfold characteristicHistoryCore
  have hx : Measurable (fun z : ℝ × WeakTime.Phase => ‖z.2.1+t₀ • z.2.2-x‖) := by fun_prop
  have hv : Measurable (fun z : ℝ × WeakTime.Phase => ‖z.2.2‖) := by fun_prop
  exact (measurableSet_le hx measurable_const).inter (measurableSet_le hv measurable_const)

theorem boundedFlightCone_mem_historyCore {t₀ Δ : ℝ} {x v : V}
    {q : PhysicalFlightState} (hq : boundedFlightCone (Δ,(x,v)) q) :
    flightCharacteristicEquiv (t₀+Δ) q ∈ characteristicHistoryCore t₀ (12*Δ) x := by
  obtain ⟨_,hv,hx,_⟩ := boundedFlightCone_characteristic hq
  exact ⟨hx,hv⟩

end BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_history_cone_conditions {ε M : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1/4) (hM : 1 ≤ M) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ {θ η r α γ t₀ Δ a l : ℝ},
      (hθ : 0 < θ) → 0 < η → η ≤ Real.log (1+ε/20) → 0 < r →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 ≤ t₀ → t₀ ≤ M*r/2 → 6*Δ ≤ (ε/20)*r → a ≤ t₀ → 0 ≤ l →
      Real.exp η*l+6*Δ < r → ∀ x v : Velocity,
      ‖transverse x‖ = r → |axial x| ≤ M*r/2 →
      ∀ q : PhysicalFlightState, boundedFlightCone (Δ,(x,v)) q →
        let z := flightCharacteristicEquiv (t₀+Δ) q;
        z ∈ coldCharacteristicDomain a η l ∧
        0 ≤ (beamCoefficients hθ hα hγ η r).plusDensity (characteristicBeamPoint z) ∧
        0 ≤ (beamCoefficients hθ hα hγ η r).minusDensity (characteristicBeamPoint z) ∧
        characteristicBeamFrequency (beamCoefficients hθ hα hγ η r) z ≤ (referenceClock:ℝ) := by
  obtain ⟨γ₀,hγ₀,hnear⟩ := beam_near_on_cylinder hε (by linarith) hM
  refine ⟨γ₀,hγ₀,?_⟩
  intro θ η r α γ t₀ Δ a l hθ hη hηsmall hr hα hαsmall hγ hγsmall ht₀ ht₀M hshort ha hl hcut x v hx hax q hq
  let z := flightCharacteristicEquiv (t₀+Δ) q
  have ht := (boundedFlightCone_characteristic (t₀ := t₀) hq).1
  have hdist := (boundedFlightCone_characteristic (t₀ := t₀) hq).2.2.2
  have hpnt : characteristicBeamPoint z = (z.1,q.2.1) := by
    change (t₀+Δ-q.1,(q.2.1-(t₀+Δ-q.1) • q.2.2)+(t₀+Δ-q.1) • q.2.2) = _
    rw [sub_add_cancel]
    rfl
  have hn := hnear hθ hη hηsmall hr hα hαsmall hγ hγsmall (by norm_num : (0:ℝ)<1)
    ht₀ ht₀M (by simpa only [div_one] using hshort) x hx hax (z.1,q.2.1)
    (by simpa only [div_one] using ht) (by simpa only [div_one] using hdist)
  refine ⟨boundedFlightCone_cold_domain ha hl (hx ▸ hcut) hq,?_,?_,?_⟩
  · exact beamDensity_nonneg hθ hα hγ hr.le η 1 _
  · exact beamDensity_nonneg hθ hα hγ hr.le η (-1) _
  · have hf := hn.frequency_margin hεsmall (v := z.2.2) (by
      exact hq.2.2.1.trans (by norm_num))
    change mediumFrequency z.2.2 _ _ _ _ ≤ _
    rw [hpnt]
    exact hf.2.trans (by change 45*Real.pi ≤ 48*Real.pi; nlinarith [Real.pi_pos])

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Domination of finite physical histories in the actual geometric cold medium -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_history_domination {ε M : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1/4) (hM : 1 ≤ M) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ {θ η r α γ t₀ Δ a l : ℝ},
      (hθ : 0 < θ) → 0 < η → η ≤ Real.log (1+ε/20) → 0 < r →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 ≤ t₀ → t₀ ≤ M*r/2 → 0 ≤ Δ → 6*Δ ≤ (ε/20)*r → a ≤ t₀ → 0 ≤ l →
      Real.exp η*l+6*Δ < r → ∀ x v : Velocity,
      ‖transverse x‖ = r → |axial x| ≤ M*r/2 → ‖v‖ ≤ 6 →
      ∀ (C ρ : ℝ≥0), referenceClock ≤ C → ∀ n : ℕ,
      let b := beamCoefficients hθ hα hγ η r;
      ((dampedBoundedDensityScaledEvent C b (t₀+Δ) ρ)^n) (Δ,(x,v)) ≤
        ((localizedNormalWindowEvent b ρ (ρ*C) (t₀+Δ) a η l t₀
          (characteristicHistoryCore_measurable t₀ (12*Δ) x))^n) (Δ,(x,v)) := by
  obtain ⟨γ₀,hγ₀,hlocal⟩ := geometric_history_cone_conditions hε hεsmall hM
  refine ⟨γ₀,hγ₀,?_⟩
  intro θ η r α γ t₀ Δ a l hθ hη hηsmall hr hα hαsmall hγ hγsmall ht₀ ht₀M hΔ hshort ha hl hcut x v hx hax hv C ρ hC n
  have ht : (t₀+Δ)-Δ = t₀ := by ring
  have hh := boundedHistory_le_localized_window hC (beamCoefficients hθ hα hγ η r) ρ
    (t₀+Δ) a η l (characteristicHistoryCore_measurable t₀ (12*Δ) x) (Δ,(x,v)) hΔ hv
    (fun _ hq => boundedFlightCone_mem_historyCore hq)
    (fun q hq => hlocal hθ hη hηsmall hr hα hαsmall hγ hγsmall ht₀ ht₀M hshort ha hl hcut x v hx hax q hq) n
  simpa only [ht] using hh

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # A growing finite block in the actual localized angular history law -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_localized_block_growth {d κ : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1/2) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock:ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ N : ℕ, ∃ ε γ₀ : ℝ,
      0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ {θ η α γ K t a l : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*(4*A₀) ≤ ε*K → 0 < t → a ≤ t → 0 ≤ l →
      ∀ (x : V) (v : RetainedState), (x,(v:V)) ∈ lateBox κ d t →
      let Δ := (8*κ*A₀/K)*t;
      Real.exp η*l+6*Δ < ‖transverse x‖ →
      let b := beamCoefficients hθ hα hγ η ‖transverse x‖;
      let ρ := Real.toNNReal (K/(4*‖transverse x‖));
      let C := Real.toNNReal (96*Real.pi*‖transverse x‖/(κ*t));
      (6:ℝ≥0∞) < localizedHistoryBlockMass b ρ (ρ*C) (t+Δ) a η l t
        (characteristicHistoryCore_measurable t (12*Δ) x) (lateBox κ d (t+Δ)) N
        (flightCharacteristicEquiv (t+Δ) (Δ,(x,(v:V)))) := by
  obtain ⟨A₀,hA₀,N,ε,γ₁,hε,hεsmall,hγ₁,hblock⟩ :=
    lateBox_common_damping_block hd hdsmall hκ hκsmall hg
  have hM : 1 ≤ 4/κ := (le_div_iff₀ hκ).mpr (by linarith)
  obtain ⟨γ₂,hγ₂,hcone⟩ := geometric_history_cone_conditions hε hεsmall hM
  refine ⟨A₀,hA₀,N,ε,min γ₁ γ₂,hε,hεsmall,lt_min hγ₁ hγ₂,?_⟩
  intro θ η α γ K t a l hθ hη hηsmall hα hαsmall hγ hγsmall hK hKlarge ht ha hl x v hp
  dsimp only
  intro hcut
  let Δ := (8*κ*A₀/K)*t
  let r := ‖transverse x‖
  have hr : 0 < r := (lateBox_geometric_scale hκ hκsmall.le hdsmall ht hp).1
  have hΔ : 0 ≤ Δ := by dsimp [Δ]; positivity
  have hρ : 0 < K/(4*r) := by positivity
  have htime := lateBox_block_duration hκ ht hdsmall hK hA₀ hp
  have hshort : 6*Δ ≤ (ε/20)*r := by
    calc
      6*Δ ≤ 6*(4*A₀)/(K/(4*r)) := by
        apply (le_div_iff₀ hρ).mpr
        nlinarith [htime.2]
      _ ≤ _ := cylinder_small_of_density_scale hK hr hKlarge
  have hscale := lateBox_geometric_scale hκ hκsmall.le hdsmall ht hp
  have hlocal := hcone hθ hη hηsmall hr hα hαsmall hγ
    (hγsmall.trans (min_le_right _ _)) ht.le hscale.2.1 hshort ha hl hcut x (v:V) rfl hscale.2.2
  have hC : referenceClock ≤ Real.toNNReal (96*Real.pi*r/(κ*t)) := by
    rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ (referenceClock.property.trans
      (lateBox_damping_range hκ ht hdsmall hp).1)]
    exact (lateBox_damping_range hκ ht hdsmall hp).1
  have hcomp := physicalBlock_le_localized hC (beamCoefficients hθ hα hγ η r)
    (Real.toNNReal (K/(4*r))) t Δ a η l κ d
    (characteristicHistoryCore_measurable t (12*Δ) x) x v hΔ
    ((show ‖(v:V)‖ ≤ 5 by simpa only [referenceRegion,Metric.mem_closedBall,dist_zero_right] using v.property).trans (by norm_num)) hp
    (fun q hq => boundedFlightCone_mem_historyCore hq) hlocal N
  have hgrowth := hblock hθ hη hηsmall hα hαsmall hγ
    (hγsmall.trans (min_le_left _ _)) hK hKlarge ht x v hp
  rw [Real.coe_toNNReal _ hρ.le] at hcomp
  have hρcoe : (Real.toNNReal (K/(4*‖transverse x‖)) : ℝ) = K/(4*‖transverse x‖) :=
    Real.coe_toNNReal _ hρ.le
  simpa only [hρcoe] using hgrowth.trans_le hcomp

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The physical normal-angle source is independent of its reference density scale -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem scaledBeamNormalKernel_independent {θ K α γ r s : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hr : 0 < r) (hs : 0 < s) (η : ℝ) :
    scaledBeamNormalKernel (beamCoefficients hθ hα hγ η r) (K/(4*r)) =
      scaledBeamNormalKernel (beamCoefficients hθ hα hγ η s) (K/(4*s)) := by
  apply Kernel.ext_fun
  intro z f hf
  rw [scaledBeamNormalKernel_apply,scaledBeamNormalKernel_apply,
    lintegral_smul_measure,lintegral_smul_measure,smul_eq_mul,smul_eq_mul,
    beamNormalCharacteristicKernel_lintegral _ z hf,
    beamNormalCharacteristicKernel_lintegral _ z hf]
  have hm : ENNReal.ofReal (K/(4*r)) •
      beamPartnerKernel (beamCoefficients hθ hα hγ η r) (characteristicBeamPoint z) =
      ENNReal.ofReal (K/(4*s)) •
      beamPartnerKernel (beamCoefficients hθ hα hγ η s) (characteristicBeamPoint z) := by
    rw [beamPartnerKernel_apply,beamPartnerKernel_apply]
    exact scaled_beamMeasure hθ hK hα hγ hr hs η _
  have h := normalGainKernel_smul_eq_of_measure_smul_eq _ _
    (characteristicBeamPoint z) (characteristicBeamPoint z) z.2.2 _ _ hm
  have H := congrArg (fun μ : Measure Velocity =>
    ∫⁻ v, f (characteristicBeamJump z v) ∂μ) h
  simpa only [lintegral_smul_measure,smul_eq_mul] using H

theorem beamNormalRetainedKernel_independent {θ K α γ r s : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hr : 0 < r) (hs : 0 < s) (η C : ℝ) :
    beamNormalRetainedKernel (beamCoefficients hθ hα hγ η r) (K/(4*r)) C =
      beamNormalRetainedKernel (beamCoefficients hθ hα hγ η s) (K/(4*s)) C := by
  have hk := scaledBeamNormalKernel_independent hθ hK hα hγ hr hs η
  apply Kernel.ext_fun
  intro z f hf
  have H := congrArg (fun Q : Kernel EuclideanFlight.CharacteristicPhase EuclideanFlight.CharacteristicPhase =>
    ∫⁻ y, f y ∂Q z) hk
  simp only [scaledBeamNormalKernel_apply,lintegral_smul_measure,smul_eq_mul] at H
  rw [beamNormalRetainedKernel_lintegral _ _ _ z hf,
    beamNormalRetainedKernel_lintegral _ _ _ z hf,H,
    scaled_characteristicBeamFrequency hθ hα hγ hr hs η z]

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Positive three-collision entry in the localized normal-angle history law -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.GeometricBackground

theorem localized_three_entry_positive {θ η α γ κ ρ ε L R h t r a l : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r)
    (hαε : α ≤ ε/2) (hε0 : 0 < ε) (hε : ε ≤ 1/12)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1) (hερ : 6*ε ≤ ρ)
    (hh : 0 < h) (hL : 0 < L) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hsmall : (R+6)*h ≤ 1) (ha : a ≤ t) (hl : 0 ≤ l)
    (hcut : Real.exp η*l ≤ L) (x v : Velocity)
    (hxr : L+1 < ‖VelocityWeight.transverse x‖) (hv : ‖v‖ ≤ R)
    (hA : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (C : ℝ≥0) {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω)
    (hΩcone : ∀ n ≤ 3, ∀ q, finiteFlightCone 3 n h R x q →
      flightCharacteristicEquiv (t+h) q ∈ Ω) :
    0 < (WeakTime.phaseEndpointKernel C (t+h) ∘ₖ
      ((((localizedNormalBeamKernel (beamCoefficients hθ hα hγ η r) 1 C a η l hΩ).restrict
        (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc t (t+h)))) ∘ₖ
          WeakTime.residenceKernel C (t+h))^3))
      (flightCharacteristicEquiv (t+h) (h,(x,v)))
      (flight (t+h) ⁻¹' velocityPhaseBall κ ρ) := by
  have hp : 0 < physicalGainEndpoint (beamCoefficients hθ hα hγ η r) (t+h) C 3
      (h,(x,v)) (velocityPhaseBall κ ρ) := by
    rw [physicalGainEndpoint_velocity_ball]
    exact geometric_density_entry_positive hθ hη hα hγ hr hαε hε0 hε hκ0 hκ hρ hερ
      hh hL hR ht hsmall x v hxr hv hA C
  apply hp.trans_le
  apply geometric_finite_gain_endpoint_le hθ hα hγ (by linarith) hr.le hh.le ha hl 3
    (by convert hsmall using 1; ring) x v
    (by linarith) hv C hΩ hΩcone (velocityPhaseBall_measurable κ ρ)

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
