import OAI.MathematicalPhysics.Boltzmann.Branching.BackgroundBeamCloseness
import OAI.MathematicalPhysics.Boltzmann.Branching.BackgroundCappedLoss
import OAI.MathematicalPhysics.Boltzmann.Branching.CenteredPeriodicBound
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedCollisionHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.MediumStateCollision
import OAI.MathematicalPhysics.Boltzmann.Branching.MomentAverageBound
import OAI.MathematicalPhysics.Boltzmann.Branching.PerturbedFiniteBlock
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss
import OAI.MathematicalPhysics.Boltzmann.Jets.AnnularEnvelopes
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdMildRepresentative
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricPositiveCompact
import OAI.MathematicalPhysics.Boltzmann.Jets.PeriodicJetFamilies

namespace OAI

section

/-! # Uniform loss control for the geometric cold family and bounded hot remainder -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem geometric_loss_bound {s₀ η K α γ d₀ q b T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hTmax : T ≤ 1/32) (N : ℕ)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : JetLattice.Label → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hcn : ∀ i u, 0 ≤ c i u)
    (hSum : ∀ s : Finset JetLattice.Label, ∀ u, ∑ i ∈ s, c i u ≤ F u)
    (hzero : ∀ i, ¬i.annulus < N → c i = 0)
    (hU : ∀ t ∈ Ioc 0 T, ∀ i (x w : Velocity),
      H q w*c i (t,(JetPeriodicDatum.spatialMap x,w)) ≤
        JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
          (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
          (JetSpatialBox.shifted x i.lattice,w))
    (hperiodic : ∀ n, pull (displacement n) F = F)
    (hcperiodic : ∀ n i, pull (displacement n) (c i) = c (relabel n i))
    (hnorm : Measurable (fun t => PhaseEssSup.size (fun p => F (t,p)-∑' i, c i (t,p)))) :
    ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T → lossFrequency q b F u ≤
      2*Real.pi*(‖u.2.2‖+1)*
        ((PhaseEssSup.size (fun p => F (u.1,p)-∑' i, c i (u.1,p))+
          escapedConstant s₀ η K α d₀)*hotConstant q+
            JetEnvelopeGain.momentConstant K α γ/u.1) := by
  let G := HotCanonical.familyReplacement F c
  let z (t : ℝ) := PhaseEssSup.size (fun p => F (t,p)-∑' i, c i (t,p))
  let w (t : ℝ) := 2*Real.pi*((z t+escapedConstant s₀ η K α d₀)*hotConstant q+
    JetEnvelopeGain.momentConstant K α γ/t)
  let k (u : ℝ × JetPrototype.Phase) := lossFrequency q b G u/(‖u.2.2‖+1)
  have hcs (u) : Summable (fun i => c i u) := summable_of_sum_le (fun i => hcn i u) (fun s => hSum s u)
  have hcF (u) : (∑' i, c i u) ≤ F u := Real.tsum_le_of_sum_le (fun i => hcn i u) (fun s => hSum s u)
  have hg := HotCanonical.family_properties hFm hcm (fun u => (hF u).2) hcn hcs hcF hnorm
  have hGp (n) : pull (displacement n) G = G :=
    familyReplacement_pull (displacement n) (relabel n) (hperiodic n) (hcperiodic n)
  have hkp (n) : pull (displacement n) k = k := by
    have hf := lossFrequency_pull q b (displacement n) G
    rw [hGp n] at hf
    funext u
    exact congrArg (fun a => a/(‖u.2.2‖+1)) (congrFun hf.symm u)
  have hkm : Measurable k := (measurable_lossFrequency hg.1 q b).div (by fun_prop)
  have hwm : Measurable w := by
    have hzm : Measurable z := hnorm
    unfold w
    fun_prop
  have hb : ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T → k u ≤ w u.1 := by
    apply ae_bound_of_centered_cell hkm hwm hkp
    intro t ht x hx
    apply ae_of_all
    intro v
    let M := (z t+escapedConstant s₀ η K α d₀)*hotConstant q+
      JetEnvelopeGain.momentConstant K α γ/t
    have hM : 0 ≤ M := add_nonneg (mul_nonneg (add_nonneg (PhaseEssSup.size_nonneg _)
      (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _)) (hotConstant_nonneg q))
      (div_nonneg (JetEnvelopeGain.momentConstant_nonneg hK α γ) ht.1.le)
    have hm := cell_moment_bound (Z := z t) hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hq
      (PhaseEssSup.size_nonneg _) ht.1 (ht.2.trans hTmax) hsmall N x hx
      (fun v => G (t,(JetPeriodicDatum.spatialMap x,v)))
      (fun i v => c i (t,(JetPeriodicDatum.spatialMap x,v)))
      (fun i => (hcm i).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
      (fun i v => hcn i _) (fun v => hcs _)
      (fun i hi v => congrFun (hzero i hi) _) (fun i v => hU t ht i x v)
      (ae_of_all _ (fun v => hg.2.2.2.1 (t,(JetPeriodicDatum.spatialMap x,v))))
    have hmi : moment (fun v => H q v*G (t,(JetPeriodicDatum.spatialMap x,v))) ≤
        ENNReal.ofReal M := hm.trans (ENNReal.ofReal_le_ofReal (by
      have he := mul_le_mul_of_nonneg_left
        (AnnularEnvelope.finiteEnvelope_le_inv_time hs₀.le hη.le ht.1 (Finset.range N)
          (transverse x)) (JetEnvelopeGain.momentConstant_nonneg hK α γ)
      dsimp [M]
      simpa only [div_eq_mul_inv,one_mul] using add_le_add (le_refl
        ((z t+escapedConstant s₀ η K α d₀)*hotConstant q)) he))
    have hf := frequency_le_moment b
      (((ChartKernel.measurable_H q).mul (hg.1.comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)))))
      (fun v => mul_nonneg (H_nonneg q v) (hg.2.1 _).1) hM hmi v
    change lossFrequency q b G (t,(JetPeriodicDatum.spatialMap x,v)) ≤
      2*Real.pi*(‖v‖+1)*M at hf
    change lossFrequency q b G (t,(JetPeriodicDatum.spatialMap x,v))/(‖v‖+1) ≤ 2*Real.pi*M
    apply (div_le_iff₀ (by positivity : 0 < ‖v‖+1)).mpr
    nlinarith only [hf]
  filter_upwards [hb,lossFrequency_congr hg.2.2.2.2 q b] with u hu hν ht
  have h := (div_le_iff₀ (by positivity : 0 < ‖u.2.2‖+1)).mp (hu ht)
  change lossFrequency q b G u ≤ w u.1*(‖u.2.2‖+1) at h
  rw [hν] at h
  dsimp [w,z] at h
  nlinarith only [h]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Loss control retaining the smallest finite cold scale -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem geometric_loss_scale_bound {s₀ η K α γ d₀ q b T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hTmax : T ≤ 1/32) (N : ℕ)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : JetLattice.Label → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hcn : ∀ i u, 0 ≤ c i u)
    (hSum : ∀ s : Finset JetLattice.Label, ∀ u, ∑ i ∈ s, c i u ≤ F u)
    (hzero : ∀ i, ¬i.annulus < N → c i = 0)
    (hU : ∀ t ∈ Ioc 0 T, ∀ i (x w : Velocity),
      H q w*c i (t,(JetPeriodicDatum.spatialMap x,w)) ≤
        JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
          (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
          (JetSpatialBox.shifted x i.lattice,w))
    (hperiodic : ∀ n, pull (displacement n) F = F)
    (hcperiodic : ∀ n i, pull (displacement n) (c i) = c (relabel n i))
    (hnorm : Measurable (fun t => PhaseEssSup.size (fun p => F (t,p)-∑' i, c i (t,p)))) :
    ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T → lossFrequency q b F u ≤
      2*Real.pi*(‖u.2.2‖+1)*
        ((PhaseEssSup.size (fun p => F (u.1,p)-∑' i, c i (u.1,p))+
          escapedConstant s₀ η K α d₀)*hotConstant q+
            JetEnvelopeGain.momentConstant K α γ/(u.1+JetGeometry.jetScale s₀ η N)) := by
  let G := HotCanonical.familyReplacement F c
  let z (t : ℝ) := PhaseEssSup.size (fun p => F (t,p)-∑' i, c i (t,p))
  let w (t : ℝ) := 2*Real.pi*((z t+escapedConstant s₀ η K α d₀)*hotConstant q+
    JetEnvelopeGain.momentConstant K α γ/(t+JetGeometry.jetScale s₀ η N))
  let k (u : ℝ × JetPrototype.Phase) := lossFrequency q b G u/(‖u.2.2‖+1)
  have hcs (u) : Summable (fun i => c i u) := summable_of_sum_le (fun i => hcn i u) (fun s => hSum s u)
  have hcF (u) : (∑' i, c i u) ≤ F u := Real.tsum_le_of_sum_le (fun i => hcn i u) (fun s => hSum s u)
  have hg := HotCanonical.family_properties hFm hcm (fun u => (hF u).2) hcn hcs hcF hnorm
  have hGp (n) : pull (displacement n) G = G :=
    familyReplacement_pull (displacement n) (relabel n) (hperiodic n) (hcperiodic n)
  have hkp (n) : pull (displacement n) k = k := by
    have hf := lossFrequency_pull q b (displacement n) G
    rw [hGp n] at hf
    funext u
    exact congrArg (fun a => a/(‖u.2.2‖+1)) (congrFun hf.symm u)
  have hkm : Measurable k := (measurable_lossFrequency hg.1 q b).div (by fun_prop)
  have hwm : Measurable w := by
    have hzm : Measurable z := hnorm
    unfold w
    fun_prop
  have hb : ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T → k u ≤ w u.1 := by
    apply ae_bound_of_centered_cell hkm hwm hkp
    intro t ht x hx
    apply ae_of_all
    intro v
    let M := (z t+escapedConstant s₀ η K α d₀)*hotConstant q+
      JetEnvelopeGain.momentConstant K α γ/(t+JetGeometry.jetScale s₀ η N)
    have hM : 0 ≤ M := add_nonneg (mul_nonneg (add_nonneg (PhaseEssSup.size_nonneg _)
      (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _)) (hotConstant_nonneg q))
      (div_nonneg (JetEnvelopeGain.momentConstant_nonneg hK α γ)
        (add_nonneg ht.1.le (DatumBounds.scale_pos hs₀ _).le))
    have hm := cell_moment_bound (Z := z t) hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hq
      (PhaseEssSup.size_nonneg _) ht.1 (ht.2.trans hTmax) hsmall N x hx
      (fun v => G (t,(JetPeriodicDatum.spatialMap x,v)))
      (fun i v => c i (t,(JetPeriodicDatum.spatialMap x,v)))
      (fun i => (hcm i).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
      (fun i v => hcn i _) (fun v => hcs _)
      (fun i hi v => congrFun (hzero i hi) _) (fun i v => hU t ht i x v)
      (ae_of_all _ (fun v => hg.2.2.2.1 (t,(JetPeriodicDatum.spatialMap x,v))))
    have hmi : moment (fun v => H q v*G (t,(JetPeriodicDatum.spatialMap x,v))) ≤
        ENNReal.ofReal M := hm.trans (ENNReal.ofReal_le_ofReal (by
      have he := mul_le_mul_of_nonneg_left
        (AnnularEnvelope.finiteEnvelope_le_minimum_scale hs₀ hη.le ht.1.le N (transverse x)) (JetEnvelopeGain.momentConstant_nonneg hK α γ)
      dsimp [M]
      simpa only [div_eq_mul_inv,one_mul] using add_le_add (le_refl
        ((z t+escapedConstant s₀ η K α d₀)*hotConstant q)) he))
    have hf := frequency_le_moment b
      (((ChartKernel.measurable_H q).mul (hg.1.comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)))))
      (fun v => mul_nonneg (H_nonneg q v) (hg.2.1 _).1) hM hmi v
    change lossFrequency q b G (t,(JetPeriodicDatum.spatialMap x,v)) ≤
      2*Real.pi*(‖v‖+1)*M at hf
    change lossFrequency q b G (t,(JetPeriodicDatum.spatialMap x,v))/(‖v‖+1) ≤ 2*Real.pi*M
    apply (div_le_iff₀ (by positivity : 0 < ‖v‖+1)).mpr
    nlinarith only [hf]
  filter_upwards [hb,lossFrequency_congr hg.2.2.2.2 q b] with u hu hν ht
  have h := (div_le_iff₀ (by positivity : 0 < ‖u.2.2‖+1)).mp (hu ht)
  change lossFrequency q b G u ≤ w u.1*(‖u.2.2‖+1) at h
  rw [hν] at h
  dsimp [w,z] at h
  nlinarith only [h]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual cold frequency is controlled by the nearby two-beam clock -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem beamMeasure_integral (b : BeamCoefficients) (p : ℝ × V)
    (hp : 0 ≤ b.plusDensity p) (hm : 0 ≤ b.minusDensity p) (f : V → ℝ) :
    (∫ v, f v ∂beamMeasure b p) =
      b.plusDensity p*f (b.plusPartner p)+b.minusDensity p*f (b.minusPartner p) := by
  have hi (c : ℝ) (w : V) : Integrable f (ENNReal.ofReal c • Measure.dirac w) :=
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  rw [beamMeasure,integral_add_measure (hi _ _) (hi _ _)]
  simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal hp,
    ENNReal.toReal_ofReal hm,smul_eq_mul]

theorem BeamNear.frequency_bound {b : BeamCoefficients} {ε : ℝ} {p : ℝ × V}
    (hε : ε ≤ 1/4) (hnear : BeamNear b ε p) {v : V} (hv : ‖v‖ ≤ 6) :
    0 ≤ mediumFrequency v (b.plusPartner p) (b.minusPartner p)
      (b.plusDensity p) (b.minusDensity p) ∧
    mediumFrequency v (b.plusPartner p) (b.minusPartner p)
      (b.plusDensity p) (b.minusDensity p) ≤ 40*Real.pi := by
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
  exact medium_frequency_bounds hv hwp hwm (by linarith [hp.1]) (by linarith [hm.1])
    (by linarith [hp.2]) (by linarith [hm.2])

end BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

open ReferenceGeometry

theorem frequency_eq_beamFrequency {θ K α γ r t : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r)
    (ht : 0 ≤ t) (η l : ℝ) (x v : Velocity) (ha : active θ η l (transverse x)) :
    frequency θ η l K α γ t (transverse x,axial x) v =
      (K/(4*r))*mediumFrequency v
        ((beamCoefficients hθ hα hγ η r).plusPartner (t,x))
        ((beamCoefficients hθ hα hγ η r).minusPartner (t,x))
        ((beamCoefficients hθ hα hγ η r).plusDensity (t,x))
        ((beamCoefficients hθ hα hγ η r).minusDensity (t,x)) := by
  rw [frequency,background_eq_beamMeasure hθ hK hα hγ hr ht η l x ha,
    integral_smul_measure,ENNReal.toReal_ofReal (by positivity),smul_eq_mul,
    beamMeasure_integral _ _ (beamDensity_nonneg hθ hα hγ hr.le η 1 (t,x))
      (beamDensity_nonneg hθ hα hγ hr.le η (-1) (t,x))]
  unfold mediumFrequency
  ring

theorem frequency_le_near_clock {θ K α γ r t ε : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r)
    (ht : 0 ≤ t) (η l : ℝ) (x v : Velocity) (hv : ‖v‖ ≤ 6) (hε : ε ≤ 1/4)
    (hnear : BeamNear (beamCoefficients hθ hα hγ η r) ε (t,x)) :
    frequency θ η l K α γ t (transverse x,axial x) v ≤ (K/(4*r))*(48*Real.pi) := by
  by_cases ha : active θ η l (transverse x)
  · rw [frequency_eq_beamFrequency hθ hK hα hγ hr ht η l x v ha]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hf := hnear.frequency_bound hε hv
    linarith [Real.pi_pos]
  · rw [frequency,background,ite_eq_right ha,integral_zero_measure,mul_zero]
    positivity

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Uniform local closeness of the selected geometric cold beams -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem join_zero_axis (z : ℝ) : PlaneChart.join 0 z = z • ReferenceGeometry.beamAxis := by
  apply split.injective
  rw [show split (PlaneChart.join 0 z) = (z,0) from split.apply_symm_apply (z,0),split_apply]
  apply Prod.ext
  · simp [axial,ReferenceGeometry.beamAxis]
  · apply (WithLp.ext_iff 2).mpr
    funext i
    fin_cases i <;> simp [transverse,ReferenceGeometry.beamAxis]

theorem beamVelocity_error {α : ℝ} (hα : 0 ≤ α) (θ η γ σ : ℝ) (p : ℝ × Velocity) :
    ‖beamVelocity θ η α γ σ p-σ • ReferenceGeometry.beamAxis‖ ≤ α := by
  unfold beamVelocity
  rw [join_zero_axis,← sub_smul,norm_smul,Real.norm_eq_abs,ReferenceGeometry.axis_norms.2.2,mul_one]
  exact AxialFlow.velocity_sub_center_le hα

theorem selected_scale_error_small {θ η r ε : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hηsmall : η ≤ Real.log (1+ε/20)) (hr : 0 < r)
    (y : Transverse) (hy : 0 < ‖y‖) (hw : |‖y‖-r| ≤ (ε/20)*r) :
    |r/scale θ η y-1| ≤ ε/5 := by
  have hδ : 0 ≤ ε/20 := by positivity
  have hδ1 : ε/20 < 1 := by linarith
  have hscale := selected_scale_ratio_error hθ hη hr hδ hδ1 y hy hw
  have he : Real.exp η-1 ≤ ε/20 := by
    have hh := Real.exp_le_exp.mpr hηsmall
    rw [Real.exp_log (by positivity : 0 < 1+ε/20)] at hh
    linarith
  apply hscale.trans
  apply (div_le_iff₀ (sub_pos.mpr hδ1)).mpr
  nlinarith

theorem beam_density_tolerance {ε C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 < C) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ {θ η r α γ t : ℝ},
      0 < θ → 0 < η → η ≤ Real.log (1+ε/20) → 0 < r →
      0 ≤ α → α ≤ 1 → 0 ≤ γ → γ ≤ γ₀ → 0 ≤ t → t ≤ C*r →
      ∀ x : Velocity, 0 < ‖transverse x‖ →
      |‖transverse x‖-r| ≤ (ε/20)*r → |axial x| ≤ C*r →
      ∀ σ : ℝ, |σ| = 1 → |beamDensity θ η α γ r σ (t,x)-1| ≤ ε := by
  obtain ⟨δ,hδ,hS⟩ := AxialBackground.axial_weight_close_to_one (div_pos hε (by norm_num : (0:ℝ)<5))
  let γ₀ := min (δ/(6*C)) ((ε/5)/(2*C))
  have hγ₀ : 0 < γ₀ := lt_min (by positivity) (by positivity)
  refine ⟨γ₀,hγ₀,?_⟩
  intro θ η r α γ t hθ hη hηsmall hr hα hα1 hγ hγsmall ht htC x hx hwindow hz σ hσ
  have hmesh := selected_scale_error_small hθ hη hε hε1 hηsmall hr (transverse x) hx hwindow
  have hR : r/scale θ η (transverse x) ≤ 2 := by
    have hh := (abs_le.mp hmesh).2
    linarith
  have hb := AxialBackground.beam_argument_bound hr (scale_pos hθ η _) hα hα1 hγ ht hC.le
    htC hz hR hσ
  have hg1 : 6*C*γ ≤ δ := by
    have hh := (le_div_iff₀ (by positivity : 0 < 6*C)).mp
      (hγsmall.trans (min_le_left _ _))
    nlinarith
  have hg2 : 2*C*γ ≤ ε/5 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*C)).mp
      (hγsmall.trans (min_le_right _ _))
    nlinarith
  rw [beamDensity_eq_relative hθ hα hγ hr η σ (t,x) ht]
  exact AxialBackground.relativeWeight_close hr.le (scale_pos hθ η _) hα hγ ht hε.le
    hR hmesh σ (axial x) (hS _ (hb.1.trans hg1)) (hb.2.trans hg2)

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The normalized holding term is the actual geometric loss complement -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedMediumCollision_eq_nonzero_marks {D : ℝ≥0} (hD : referenceClock ≤ D)
    (b : BeamCoefficients) (z : MediumState)
    (hf : mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
      (b.plusDensity z.1) (b.minusDensity z.1) ≤ (referenceClock:ℝ)) :
    dampedMediumCollision D b z = mediumMarkedKernel b 1 z+mediumMarkedKernel b 2 z+
      ENNReal.ofReal ((D:ℝ)-mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
        (b.plusDensity z.1) (b.minusDensity z.1)) • Measure.dirac z.2 := by
  rw [dampedMediumCollision_projection hD b z hf,
    mediumMarkedKernel_apply,mediumMarkedKernel_apply]
  simp only [mediumMarkedRate,markedRate,markedChildKernel,Fin.isValue,one_ne_zero,
    show (2 : HistoryMark) ≠ 0 by decide,show (2 : HistoryMark) ≠ 1 by decide,
    ↓reduceIte,Kernel.comap_apply]

end BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

open ReferenceGeometry

theorem scaled_retention_eq_actual {θ K α γ r t : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r)
    (ht : 0 ≤ t) (η l D : ℝ) (x v : Velocity) (ha : active θ η l (transverse x)) :
    ENNReal.ofReal (K/(4*r))*
        ENNReal.ofReal (D-mediumFrequency v
          ((beamCoefficients hθ hα hγ η r).plusPartner (t,x))
          ((beamCoefficients hθ hα hγ η r).minusPartner (t,x))
          ((beamCoefficients hθ hα hγ η r).plusDensity (t,x))
          ((beamCoefficients hθ hα hγ η r).minusDensity (t,x))) =
      ENNReal.ofReal ((K/(4*r))*D-frequency θ η l K α γ t (transverse x,axial x) v) := by
  rw [← ENNReal.ofReal_mul (by positivity),frequency_eq_beamFrequency hθ hK hα hγ hr ht η l x v ha]
  congr 1
  ring

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
