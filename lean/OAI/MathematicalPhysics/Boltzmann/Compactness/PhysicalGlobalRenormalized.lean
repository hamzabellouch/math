import OAI.MathematicalPhysics.Boltzmann.Branching.DampedEndpointHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.LateBoxAccessMeasure
import OAI.MathematicalPhysics.Boltzmann.Branching.RightAverageBound
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticWindowL1
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicStrongAverages
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicCharacteristicGainUnit
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicJointBudgetLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEvolution
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricEntry

namespace OAI

section

/-! # Remaining-flight time and characteristic spacetime coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def flightCharacteristicEquiv (endTime : ℝ) : PhysicalFlightState ≃ᵐ (ℝ × WeakTime.Phase) where
  toFun p := (endTime-p.1,(p.2.1-(endTime-p.1) • p.2.2,p.2.2))
  invFun z := (endTime-z.1,(z.2.1+z.1 • z.2.2,z.2.2))
  left_inv p := by
    ext <;> simp
  right_inv z := by
    ext <;> simp
  measurable_toFun := by
    change Measurable (fun p : PhysicalFlightState =>
      (endTime-p.1,(p.2.1-(endTime-p.1) • p.2.2,p.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ℝ × WeakTime.Phase =>
      (endTime-z.1,(z.2.1+z.1 • z.2.2,z.2.2)))
    fun_prop

theorem flightCharacteristic_advance (endTime : ℝ) (p : PhysicalFlightState) (s : ℝ) :
    flightCharacteristicEquiv endTime (physicalAdvance p s) =
      ((flightCharacteristicEquiv endTime p).1+s,(flightCharacteristicEquiv endTime p).2) := by
  have ht : endTime-(p.1-s) = endTime-p.1+s := by ring
  change (endTime-(p.1-s),(p.2.1+s • p.2.2-(endTime-(p.1-s)) • p.2.2,p.2.2)) = _
  rw [ht,add_smul]
  simp only [flightCharacteristicEquiv,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk]
  congr 2
  abel

theorem translated_time_lintegral (c a : ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ s in Ioc 0 a, f (c+s)) = ∫⁻ t in Ioc c (c+a), f t := by
  have hset : (fun s : ℝ => c+s) ⁻¹' Ioc c (c+a) = Ioc 0 a := by
    ext s
    simp only [mem_preimage,mem_Ioc]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [← hset]
  exact (measurePreserving_add_left (volume : Measure ℝ) c).setLIntegral_comp_preimage
    measurableSet_Ioc hf

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Mass and momentum conservation at every nonnegative physical time -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_conserved_test
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {ψ : Phase → ℝ} (hψ : Measurable ψ) (D : ℝ)
    (hD : ∀ p, |ψ p| ≤ D*(1+‖p.2‖))
    (hc : ∀ᵐ t ∂volume, 0 ≤ t →
      (∫ p : Phase, ψ p*G.weakLimit.density (t,p)) = ∫ p, ψ p*f p)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ p, ψ p*physicalEvolution f G.weakLimit.kineticProfile t p) = ∫ p, ψ p*f p := by
  have he : ∀ᵐ r ∂volume, 0 ≤ r →
      (∫ p, ψ p*physicalEvolution f G.weakLimit.kineticProfile r p) = ∫ p, ψ p*f p := by
    filter_upwards [G.physical_eq_density_ae hf hi,hc] with r hr hc
    intro hr0
    exact (integral_congr_ae ((hr hr0).mono (fun p hp => congrArg (fun a => ψ p*a) hp))).trans (hc hr0)
  obtain ⟨s,hs,hst⟩ := exists_right_good_sequence he t
  have hsm n : s n ∈ Icc 0 (t+1) := by
    have hδ : 1/((n:ℝ)+1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact ⟨ht.trans (hs n).1.le,(hs n).2.1.le.trans (add_le_add le_rfl hδ)⟩
  have hh := G.physical_linear_test_seq hf hi (show 0 ≤ t+1 by linarith)
    (show t ∈ Icc 0 (t+1) from ⟨ht,by linarith⟩) hsm hst hψ D hD
  have heq n := (hs n).2.2 (hsm n).1
  simp only [heq] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds

theorem GlobalCollisionLimit.physical_mass_conservation
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ p, physicalEvolution f G.weakLimit.kineticProfile t p) = ∫ p, f p := by
  have hc : ∀ᵐ r ∂volume, 0 ≤ r →
      (∫ p : Phase, (1:ℝ)*G.weakLimit.density (r,p)) = ∫ p, (1:ℝ)*f p := by
    simpa only [one_mul] using G.mass_conservation_ae hf hi
  simpa only [one_mul] using G.physical_conserved_test hf hi (ψ := fun _ => 1) measurable_const 1
    (fun p => by simp only [abs_one,one_mul]; linarith [norm_nonneg p.2]) hc ht

theorem GlobalCollisionLimit.physical_momentum_coordinate
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (i : Fin 3) {t : ℝ} (ht : 0 ≤ t) :
    (∫ p : Phase, p.2 i*physicalEvolution f G.weakLimit.kineticProfile t p) =
      ∫ p : Phase, p.2 i*f p := by
  apply G.physical_conserved_test hf hi (ψ := fun p => p.2 i) (by fun_prop) 1 _
    (G.momentum_conservation_ae hf hi i) ht
  intro p
  have hv : |p.2 i| ≤ ‖p.2‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p.2 i
  simpa only [one_mul] using hv.trans (by linarith : ‖p.2‖ ≤ 1+‖p.2‖)

theorem GlobalCollisionLimit.physical_momentum_conservation
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    momentum (physicalEvolution f G.weakLimit.kineticProfile t) = momentum f := by
  apply PiLp.ext
  intro i
  let L := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i
  have h₁ := L.integral_comp_comm
    (show FiniteEntropyDatum f from ⟨ae_of_all _ hf,hfm.aestronglyMeasurable,hi⟩).integrable_momentum
  have h₂ := L.integral_comp_comm (G.physical_finiteEntropy hf hi ht).integrable_momentum
  change (momentum (physicalEvolution f G.weakLimit.kineticProfile t)) i = (momentum f) i
  simp only [L,PiLp.proj_apply,PiLp.smul_apply,smul_eq_mul] at h₁ h₂
  unfold momentum
  rw [← h₂,← h₁]
  simpa only [mul_comm] using G.physical_momentum_coordinate hf hi i ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The original energy bound holds at every physical time -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_energy_le
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) : energy (physicalEvolution f G.weakLimit.kineticProfile t) ≤ energy f := by
  have he : ∀ᵐ r ∂volume, 0 ≤ r → energy (physicalEvolution f G.weakLimit.kineticProfile r) ≤ energy f := by
    filter_upwards [G.physical_eq_density_ae hf hi,G.weakLimit.energy_ae hf hi] with r hr hE
    intro hr0
    exact (le_of_eq (integral_congr_ae ((hr hr0).mono
      (fun p hp => congrArg (fun a => ‖p.2‖^2*a) hp)))).trans (hE hr0)
  obtain ⟨s,hs,hst⟩ := exists_right_good_sequence he t
  have hsm n : s n ∈ Icc 0 (t+1) := by
    have hδ : 1/((n:ℝ)+1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact ⟨ht.trans (hs n).1.le,(hs n).2.1.le.trans (add_le_add le_rfl hδ)⟩
  have hw := G.physical_weak_seq hf hi (show 0 ≤ t+1 by linarith)
    (show t ∈ Icc 0 (t+1) from ⟨ht,by linarith⟩) hsm hst
  apply energy_le_of_truncated
    ((physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable).comp
      ((measurable_const (a := t)).prodMk measurable_id))
    (fun _ => physicalEvolution_nonneg _ _ _ _)
    (G.physical_finiteEntropy hf hi ht)
    (integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (hf p)))
  intro k
  apply le_of_tendsto (hw.2.2 (truncatedEnergyWeight k) (truncatedEnergyWeight_measurable k)
    ⟨k,truncatedEnergyWeight_abs_le k⟩)
  apply Eventually.of_forall
  intro n
  have hfinite := G.physical_finiteEntropy hf hi (hsm n).1
  apply le_trans (integral_mono (truncatedEnergy_integrable hfinite.integrable k)
    hfinite.integrable_energy (fun p => mul_le_mul_of_nonneg_right
      (min_le_left _ _) (physicalEvolution_nonneg _ _ _ _)))
  exact (hs n).2.2 (hsm n).1

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The positive physical entry histories reach the late growth box -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def velocityPhaseBall (κ ρ : ℝ) : Set (V × V) := {p | p.2 ∈ ball (κ • firstAxis) ρ}

theorem velocityPhaseBall_measurable (κ ρ : ℝ) : MeasurableSet (velocityPhaseBall κ ρ) :=
  measurable_snd measurableSet_ball

theorem physicalGainEndpoint_velocity_ball (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (n : ℕ) (p : PhysicalFlightState) (κ ρ : ℝ) :
    physicalGainEndpoint b endTime C n p (velocityPhaseBall κ ρ) =
      ∫⁻ q, GeometricBackground.entryTerminal C κ ρ q ∂((physicalBeamEvent b endTime C)^n) p := by
  rw [physicalGainEndpoint_apply _ _ _ _ _ (velocityPhaseBall_measurable κ ρ)]
  apply lintegral_congr
  intro q
  rfl

theorem velocityPhaseBall_subset_entry {κ ρ d : ℝ} (hκ : 0 ≤ κ) (hρd : ρ ≤ d*κ/4)
    (hρ₅ : κ+ρ ≤ 5) : velocityPhaseBall κ ρ ⊆ entryVelocityRegion κ d := by
  intro p hp
  change dist p.2 (κ • firstAxis) < ρ at hp
  rw [dist_eq_norm] at hp
  refine ⟨hp.trans_le hρd,?_⟩
  have hb : ‖p.2‖ ≤ ‖p.2-κ • firstAxis‖+κ := by
    calc
      ‖p.2‖ = ‖(p.2-κ • firstAxis)+κ • firstAxis‖ := by congr 1; module
      _ ≤ ‖p.2-κ • firstAxis‖+‖κ • firstAxis‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hκ,axis_norms.1,mul_one]
  linarith

theorem physical_entry_eventually_lateBox (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (n : ℕ) (p : PhysicalFlightState) {κ ρ d a : ℝ}
    (hκ : 0 < κ) (hd : 0 < d) (ha : 0 ≤ a) (hρd : ρ ≤ d*κ/4) (hρ₅ : κ+ρ ≤ 5)
    (hentry : 0 < ∫⁻ q, GeometricBackground.entryTerminal C κ ρ q
      ∂((physicalBeamEvent b endTime C)^n) p) :
    ∃ T : ℝ, a ≤ T ∧ 0 < T ∧ ∀ t, T ≤ t →
      0 < ((physicalGainEndpoint b endTime C n p).map
        (fun q => (q.1+(t-a) • q.2,q.2))) (lateBox κ d t) := by
  apply positive_mass_eventually_lateBox hκ hd ha
  apply lt_of_lt_of_le _ (measure_mono (velocityPhaseBall_subset_entry hκ.le hρd hρ₅))
  rwa [physicalGainEndpoint_velocity_ball]

end BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

open ReferenceGeometry

theorem geometric_density_lateBox_access {θ η α γ κ ρ ε L R h t r d : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r)
    (hαε : α ≤ ε/2) (hε0 : 0 < ε) (hε : ε ≤ 1/12)
    (hκ0 : 0 < κ) (hκ : κ ≤ 1) (hd : 0 < d) (hρ : ρ ≤ 1) (hερ : 6*ε ≤ ρ)
    (hρd : ρ ≤ d*κ/4) (hρ₅ : κ+ρ ≤ 5)
    (hh : 0 < h) (hL : 0 < L) (hR : 0 ≤ R) (ht : 0 ≤ t) (hsmall : (R+6)*h ≤ 1)
    (x v : V) (hxr : L+1 < ‖VelocityWeight.transverse x‖) (hv : ‖v‖ ≤ R)
    (hA : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (C : ℝ≥0) :
    ∃ T : ℝ, t+h ≤ T ∧ 0 < T ∧ ∀ τ, T ≤ τ →
      0 < ((physicalGainEndpoint (beamCoefficients hθ hα hγ η r) (t+h) C 3 (h,(x,v))).map
        (fun q => (q.1+(τ-(t+h)) • q.2,q.2))) (lateBox κ d τ) := by
  apply physical_entry_eventually_lateBox _ _ _ _ _ hκ0 hd (by linarith) hρd hρ₅
  exact geometric_density_entry_positive hθ hη hα hγ hr hαε hε0 hε hκ0.le hκ hρ hερ
    hh hL hR ht hsmall x v hxr hv hA C

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The full nonlinear renormalized equation on every finite time interval -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_renormalized_integrable
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (β : Renormalization) (φ : KineticTest) :
    Integrable (renormalizedIntegrand (physicalEvolution f G.weakLimit.kineticProfile) β φ)
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  have hA := (G.linear_renormalized_field_integrable hf hi hT β φ).congr
    (G.physical_renormalized_field_along hf hi hT β φ).symm
  have hB := (TorusFlight.back_measurePreserving (volume.restrict (Icc 0 T))).integrable_comp_of_integrable hA
  convert hB using 1
  funext z
  dsimp only [Function.comp_def,TorusFlight.along]
  rw [TorusFlight.neg_flight]

theorem GlobalCollisionLimit.physical_renormalized_balance_terminal_zero
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (β : Renormalization) (φ : KineticTest)
    (hφ : ∀ x v, φ.toFun T x v = 0) :
    (∫ z, renormalizedIntegrand (physicalEvolution f G.weakLimit.kineticProfile) β φ z
      ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase))+
      (∫ p : Phase, maxwellian p.2*β.toFun (f p/maxwellian p.2)*φ.toFun 0 p.1 p.2) = 0 := by
  rw [← TorusFlight.integral_along (G.physical_renormalized_integrable hf hi hT β φ),
    integral_congr_ae (G.physical_renormalized_field_along hf hi hT β φ)]
  exact G.linear_renormalized_balance_terminal_zero hf hi hT β φ hφ

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Free waiting is exactly characteristic residence under the flight chart -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flightCharacteristic_waiting_lintegral (C : ℝ≥0) (endTime : ℝ)
    (p : PhysicalFlightState) {F : ℝ × WeakTime.Phase → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F (flightCharacteristicEquiv endTime q) ∂physicalWaitingKernel C p) =
      ∫⁻ z, F z ∂WeakTime.residenceKernel C endTime (flightCharacteristicEquiv endTime p) := by
  let z := flightCharacteristicEquiv endTime p
  have hc : Measurable (fun q => F (flightCharacteristicEquiv endTime q)) :=
    hF.comp (flightCharacteristicEquiv endTime).measurable
  rw [physicalWaitingKernel_lintegral C p hc,WeakTime.residenceKernel_lintegral _ _ _ hF]
  have hf : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp ((C : ℝ)*(z.1-t)))*F (t,z.2)) :=
    (show Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp ((C : ℝ)*(z.1-t)))) by
      fun_prop).mul (hF.comp (measurable_id.prodMk measurable_const))
  have ht := translated_time_lintegral z.1 p.1 _ hf
  have hz : z.1+p.1 = endTime := by dsimp [z,flightCharacteristicEquiv]; ring
  rw [hz] at ht
  rw [← ht]
  apply lintegral_congr
  intro s
  rw [flightCharacteristic_advance]
  dsimp only [z]
  congr 1
  unfold clockSurvival
  congr 2
  ring

theorem flightCharacteristic_waiting_map (C : ℝ≥0) (endTime : ℝ)
    (p : PhysicalFlightState) :
    (physicalWaitingKernel C p).map (flightCharacteristicEquiv endTime) =
      WeakTime.residenceKernel C endTime (flightCharacteristicEquiv endTime p) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (flightCharacteristicEquiv endTime).measurable]
  exact flightCharacteristic_waiting_lintegral C endTime p hF

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The physical evolution retains the actual global local-mass equation -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_eq_density_nonnegative
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    (fun z : ℝ × Phase => physicalEvolution f G.weakLimit.kineticProfile z.1 z.2)
      =ᵐ[volume.restrict nonnegativeTimes] G.weakLimit.density := by
  have he : ∀ᵐ t ∂volume.restrict (Ici (0:ℝ)), ∀ᵐ p ∂(volume : Measure Phase),
      physicalEvolution f G.weakLimit.kineticProfile t p = G.weakLimit.density (t,p) := by
    filter_upwards [ae_restrict_of_ae (G.physical_eq_density_ae hf hi),
      ae_restrict_mem measurableSet_Ici] with t ht ht0
    exact ht ht0
  have hm : MeasurableSet {z : ℝ × Phase |
      physicalEvolution f G.weakLimit.kineticProfile z.1 z.2 = G.weakLimit.density z} :=
    measurableSet_eq_fun (physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable)
      G.weakLimit.measurable
  have hh := (Measure.ae_prod_iff_ae_ae hm).mpr he
  rw [Measure.restrict_prod_eq_prod_univ,← Measure.volume_eq_prod] at hh
  exact hh

theorem GlobalCollisionLimit.physical_global_mass
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (φ : MassTest) :
    IntegrableOn (fun z : ℝ × Phase => physicalEvolution f G.weakLimit.kineticProfile z.1 z.2*
      φ.transportDerivative z.1 z.2) nonnegativeTimes ∧
    (∫ z in nonnegativeTimes, physicalEvolution f G.weakLimit.kineticProfile z.1 z.2*
      φ.transportDerivative z.1 z.2)+(∫ p : Phase, f p*φ.toFun 0 p.1) = 0 := by
  have h := G.weakLimit.global_local_mass hf hi φ
  have he : (fun z : ℝ × Phase => physicalEvolution f G.weakLimit.kineticProfile z.1 z.2*
      φ.transportDerivative z.1 z.2) =ᵐ[volume.restrict nonnegativeTimes]
      (fun z => G.weakLimit.density z*φ.transportDerivative z.1 z.2) :=
    (G.physical_eq_density_nonnegative hf hi).mono
    (fun z hz => congrArg (fun a => a*φ.transportDerivative z.1 z.2) hz)
  refine ⟨h.1.congr he.symm,?_⟩
  rw [integral_congr_ae he]
  exact h.2

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Global renormalized transport for the physical evolution -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_global_renormalized
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (β : Renormalization) (φ : KineticTest) :
    IntegrableOn (renormalizedIntegrand (physicalEvolution f G.weakLimit.kineticProfile) β φ) nonnegativeTimes ∧
    (∫ z in nonnegativeTimes, renormalizedIntegrand (physicalEvolution f G.weakLimit.kineticProfile) β φ z)+
      (∫ p : Phase, maxwellian p.2*β.toFun (f p/maxwellian p.2)*φ.toFun 0 p.1 p.2) = 0 := by
  obtain ⟨T,hT,hend,hzero⟩ := φ.exists_time_cutoff
  let u := renormalizedIntegrand (physicalEvolution f G.weakLimit.kineticProfile) β φ
  have hui : IntegrableOn u (boundedTimes T) := by
    change Integrable u (volume.restrict (boundedTimes T))
    rw [← phaseInterval_measure]
    exact G.physical_renormalized_integrable hf hi hT.le β φ
  have hsub : boundedTimes T ⊆ nonnegativeTimes := fun _ hz => ⟨hz.1.1,hz.2⟩
  have hm : MeasurableSet nonnegativeTimes := measurableSet_Ici.prod MeasurableSet.univ
  have hz : ∀ z ∈ nonnegativeTimes \ boundedTimes T, u z = 0 := by
    intro z hz
    have ht : T < z.1 := lt_of_not_ge (fun ht => hz.2 ⟨⟨hz.1.1,ht⟩,hz.1.2⟩)
    dsimp only [u,renormalizedIntegrand]
    rw [(hzero z.1 ht z.2).1,(hzero z.1 ht z.2).2,mul_zero,mul_zero,add_zero]
  refine ⟨hui.of_forall_sdiff_eq_zero hm hz,?_⟩
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hm hsub hz,← phaseInterval_measure]
  exact G.physical_renormalized_balance_terminal_zero hf hi hT.le β φ hend

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
