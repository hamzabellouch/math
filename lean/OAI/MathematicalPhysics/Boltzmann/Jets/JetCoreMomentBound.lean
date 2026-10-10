import OAI.MathematicalPhysics.Boltzmann.Branching.MixedRealGain
import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreConvergence
import OAI.MathematicalPhysics.Boltzmann.Jets.JetPeriodicDatum

namespace OAI

section

/-! # Replacing the annular part of the full oscillating mask -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

theorem mask_indicator_factor (η s : ℝ) (a : Bool) (y : Transverse) :
    (mask η s a).indicator (fun _ => (1:ℝ)) y =
      (annularCore η s).indicator (fun _ => (1:ℝ)) y *
        (stripe s a).indicator (fun _ => (1:ℝ)) y := by
  by_cases hc : y ∈ annularCore η s <;> by_cases hs : y ∈ stripe s a <;>
    simp [mask,Set.indicator,hc,hs]

private theorem mask_error_le (η s μ : ℝ) (a : Bool) (y x : Transverse) :
    |(mask η s a).indicator (fun _ => (1:ℝ)) y -
        (scaleShell η μ).indicator (fun _ => (1:ℝ)) x *
          (stripe s a).indicator (fun _ => (1:ℝ)) y| ≤
      |(annularCore η s).indicator (fun _ => (1:ℝ)) y -
        (scaleShell η μ).indicator (fun _ => (1:ℝ)) x| := by
  rw [mask_indicator_factor,← sub_mul,abs_mul]
  by_cases h : y ∈ stripe s a
  · simp only [indicator_of_mem h,abs_one,mul_one,le_refl]
  · simp only [indicator_of_notMem h,abs_zero,mul_zero,abs_nonneg]

theorem spatial_mask_L1_tendsto {r s d : ℕ → ℝ} {μ : ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    (η t : ℝ) (a : Bool) (Ω : Set Transverse) (hΩ : volume Ω < ⊤) :
    Tendsto (fun n => ∫ p : Transverse × (Transverse × ℝ),
      |(mask η (r n*s n) a).indicator (fun _ => (1:ℝ))
          (r n • (p.1-t • (d n • p.2.1))) -
        (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1 *
          (stripe (r n*s n) a).indicator (fun _ => (1:ℝ))
            (r n • (p.1-t • (d n • p.2.1)))| *
      JetThermalKernel.J (SheetMeasures.join p.2)
      ∂(volume.restrict Ω).prod ((volume : Measure Transverse).prod volume))
      atTop (𝓝 0) := by
  let _ : IsFiniteMeasure ((volume : Measure Transverse).restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hΩ⟩
  have hm (n) : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (mask η (r n*s n) a).indicator (fun _ => (1:ℝ))
        (r n • (p.1-t • (d n • p.2.1)))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_mask η (r n*s n) a)).comp (by fun_prop)
  have hstripe (n) : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (stripe (r n*s n) a).indicator (fun _ => (1:ℝ))
        (r n • (p.1-t • (d n • p.2.1)))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_stripe (r n*s n) a)).comp (by fun_prop)
  have hshell : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1) :=
    (measurable_const.indicator (measurableSet_scaleShell η μ)).comp measurable_fst
  have hJ := (HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable).comp_snd ((volume : Measure Transverse).restrict Ω)
  have hmJ : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      JetThermalKernel.J (SheetMeasures.join p.2)) :=
    (JetThermalKernel.J_smooth.continuous.measurable.comp SheetMeasures.join.measurable).comp measurable_snd
  have hl := tendsto_integral_of_dominated_convergence
    (μ := (volume.restrict Ω).prod ((volume : Measure Transverse).prod volume))
    (F := fun n p => |(mask η (r n*s n) a).indicator (fun _ => (1:ℝ))
      (r n • (p.1-t • (d n • p.2.1)))-
      (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1 *
      (stripe (r n*s n) a).indicator (fun _ => (1:ℝ))
        (r n • (p.1-t • (d n • p.2.1)))| *JetThermalKernel.J (SheetMeasures.join p.2))
    (f := fun _ => (0:ℝ)) (fun p => 2*JetThermalKernel.J (SheetMeasures.join p.2))
    (fun n => (((hm n).sub (hshell.mul (hstripe n))).abs.mul hmJ).aestronglyMeasurable)
    (hJ.const_mul 2) ?_ ?_
  · simpa only [integral_zero] using hl
  · intro n
    filter_upwards [] with p
    change ‖|_ - _| *JetThermalKernel.J (SheetMeasures.join p.2)‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (JetThermalKernel.J_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (JetThermalKernel.J_nonneg _)
    apply (mask_error_le η (r n*s n) μ a _ _).trans
    have hbound (A : Set Transverse) (y : Transverse) : |A.indicator (fun _ => (1:ℝ)) y| ≤ 1 := by
      by_cases h : y ∈ A <;> simp [Set.indicator,h]
    exact (abs_sub _ _).trans ((add_le_add (hbound _ _) (hbound _ _)).trans (by norm_num))
  · filter_upwards [ae_annular_indicator_tendsto hr hrlim hslim hdlim η t Ω] with p hp
    apply squeeze_zero (fun _ => mul_nonneg (abs_nonneg _) (JetThermalKernel.J_nonneg _))
      (fun n => mul_le_mul_of_nonneg_right (mask_error_le η (r n*s n) μ a _ _)
        (JetThermalKernel.J_nonneg _)) hp

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # Exponential velocity moments of the actual cold supersolutions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.SheetClass

def exponentialMoment (μ : Measure Velocity) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (Real.exp (2*‖v‖^2)) ∂μ

theorem exponentialMoment_mono {μ ν : Measure Velocity} (h : μ ≤ ν) :
    exponentialMoment μ ≤ exponentialMoment ν := lintegral_mono' h le_rfl

theorem exponentialMoment_smul (a : ℝ≥0∞) (μ : Measure Velocity) :
    exponentialMoment (a • μ) = a*exponentialMoment μ := lintegral_smul_measure a _

theorem exponentialMoment_add (μ ν : Measure Velocity) :
    exponentialMoment (μ+ν) = exponentialMoment μ+exponentialMoment ν := lintegral_add_measure _ _ _

theorem elementary_exponentialMoment {L : ℝ} {μ : Measure Velocity} (h : IsElementary L μ) :
    exponentialMoment μ ≤ ENNReal.ofReal (4*L) := by
  obtain ⟨d,ρ,hd,hdmax,hprob,hρ,rfl⟩ := h
  let := hprob
  have he : exponentialMoment (SheetMeasures.sheetLaw d ρ) = SheetMeasures.tiltedSheet d ρ univ := by
    simp only [exponentialMoment,SheetMeasures.tiltedSheet,withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ]
  rw [he]
  exact SheetMeasures.tiltedSheet_mass_le hd hdmax hρ

theorem exponentialMoment_density {f : Velocity → ℝ} (hf : Measurable f) :
    exponentialMoment (volume.withDensity (fun v => ENNReal.ofReal (f v))) =
      ∫⁻ v, ENNReal.ofReal (Real.exp (2*‖v‖^2)*f v) := by
  have he : Measurable (fun v : Velocity => ENNReal.ofReal (Real.exp (2*‖v‖^2))) := by fun_prop
  rw [exponentialMoment,lintegral_withDensity_eq_lintegral_mul _ hf.ennreal_ofReal he]
  apply lintegral_congr
  intro v
  change ENNReal.ofReal (f v)*ENNReal.ofReal (Real.exp (2*‖v‖^2)) = _
  rw [mul_comm,← ENNReal.ofReal_mul (Real.exp_pos _).le]

end BoltzmannNonuniqueness.SheetClass

namespace BoltzmannNonuniqueness.JetEnvelopeGain

theorem exponential_moment_le {K α γ s d t : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s)
    (hd : 0 < d) (hdmax : d ≤ 1/16) (ht : 0 ≤ t) (htmax : t ≤ 1)
    (η : ℝ) (a : Bool) (x : Space) :
    SheetClass.exponentialMoment
      (volume.withDensity (fun v => ENNReal.ofReal (JetSupersolution.U η K α γ s d t a (x,v)))) ≤
      ENNReal.ofReal (amplitude η K α γ s d t a x * (8*Real.exp (16*(1+α)^2))) := by
  let L := 2*Real.exp (16*(1+α)^2)
  have hc : SheetClass.IsElementary L
      (SheetMeasures.sheetLaw d (JetAxialLaw.law (sign a) α γ s d t x.2)) := by
    have hp := JetAxialLaw.probability (sign a) α γ s d t x.2
    have hm := JetAxialLaw.moment hα.le hγ.le hs hd hdmax ht (sign a) x.2
    have he : |sign a| = 1 := JetSupport.abs_sign a
    rw [he] at hm
    exact ⟨d,_,hd.le,by linarith,hp,hm,rfl⟩
  have hr : SheetClass.IsElementary L
      (SheetMeasures.sheetLaw d
        (JetAxialLaw.law (AxialFlow.velocity (sign a) α γ s t x.2) 0 0 1 d 0 0)) :=
    ⟨d,_,hd.le,by linarith,JetAxialLaw.probability _ _ _ _ _ _ _,
      JetRemainderSheet.axial_moment hα.le hd hdmax γ s t x.2 a,rfl⟩
  have hcore : SheetClass.exponentialMoment
      (volume.withDensity (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x,v)))) ≤
      ENNReal.ofReal (JetCoreSheet.amplitude K α γ s t)*ENNReal.ofReal (4*L) := by
    calc
      _ ≤ SheetClass.exponentialMoment (ENNReal.ofReal (JetCoreSheet.amplitude K α γ s t) •
          SheetMeasures.sheetLaw d (JetAxialLaw.law (sign a) α γ s d t x.2)) :=
        SheetClass.exponentialMoment_mono (JetCoreSheet.measure_domination hK hα hγ hs hd ht η a x)
      _ = _ := SheetClass.exponentialMoment_smul _ _
      _ ≤ _ := mul_le_mul' le_rfl (SheetClass.elementary_exponentialMoment hc)
  have hrest : SheetClass.exponentialMoment
      (volume.withDensity (fun v => ENNReal.ofReal (JetRemainderSheet.remainder η K α γ s d t a x v))) ≤
      ENNReal.ofReal (JetRemainderSheet.amplitude η K α γ s d t a x)*ENNReal.ofReal (4*L) := by
    calc
      _ ≤ SheetClass.exponentialMoment (ENNReal.ofReal (JetRemainderSheet.amplitude η K α γ s d t a x) •
          SheetMeasures.sheetLaw d
            (JetAxialLaw.law (AxialFlow.velocity (sign a) α γ s t x.2) 0 0 1 d 0 0)) :=
        SheetClass.exponentialMoment_mono (JetRemainderSheet.measure_domination hK hs hd htmax η α γ a x)
      _ = _ := SheetClass.exponentialMoment_smul _ _
      _ ≤ _ := mul_le_mul' le_rfl (SheetClass.elementary_exponentialMoment hr)
  have hrc : 0 ≤ JetRemainderSheet.amplitude η K α γ s d t a x := by
    have he := JetSupersolution.epsilon_nonneg hK hs hd
    have hm := JetBarrierCollision.massScale_nonneg hK hs η α γ d t a x
    unfold JetRemainderSheet.amplitude
    positivity
  rw [measure_eq hK hs hd,SheetClass.exponentialMoment_add]
  apply (add_le_add hcore hrest).trans_eq
  rw [← add_mul,← ENNReal.ofReal_add (JetCoreSheet.amplitude_nonneg hK hs ht α γ)
    hrc,← ENNReal.ofReal_mul]
  · congr 1
    dsimp [amplitude,L]
    ring
  · exact add_nonneg (JetCoreSheet.amplitude_nonneg hK hs ht α γ)
      hrc

end BoltzmannNonuniqueness.JetEnvelopeGain

end

end

section

/-! # Arbitrary-power bounds for the complete escaped-barrier sum -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetSpatialBox
open BoltzmannNonuniqueness.JetLatticeTail

namespace BoltzmannNonuniqueness.JetEscapedTotal

def annulus (η K α γ s d₀ t : ℝ) (x v : Velocity) : ℝ≥0∞ :=
  ∑' a : Bool, ∑' n : Lattice, {n | outside η s t a x n}.indicator
    (fun n => ENNReal.ofReal (barrier η K α γ s (d₀ * s ^ 10) t a (shifted x n, v))) n

def total (s₀ η K α γ d₀ t : ℝ) (x v : Velocity) : ℝ≥0∞ :=
  ∑' j : ℕ, annulus η K α γ (jetScale s₀ η j) d₀ t x v

def coefficient (α K d₀ : ℝ) : ℝ :=
  2 * JetEscapedBarrier.coefficient α K d₀ * JetLatticeGaussian.constant ^ 3

theorem coefficient_nonneg {K d₀ : ℝ} (hK : 0 ≤ K) (hd₀ : 0 < d₀) (α : ℝ) :
    0 ≤ coefficient α K d₀ := by
  have hL : 0 ≤ JetLatticeGaussian.constant := by
    unfold JetLatticeGaussian.constant JetLatticeGaussian.exponential
    positivity
  unfold coefficient JetEscapedBarrier.coefficient JetGaussianEscape.constant
  have := JetThermalKernel.bound_pos
  positivity

theorem annulus_bound {η K α s d₀ t : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (hd₀ : 0 < d₀) (hwidth : d₀ * s ^ 10 ≤ 1 / 16) (ht : 0 < t) (htmax : t ≤ 1 / 32)
    (γ : ℝ) (x v : Velocity) (hx : ∀ k, |x k| ≤ 1) :
    annulus η K α γ s d₀ t x v ≤ ENNReal.ofReal (coefficient α K d₀ *
      JetEscapePower.tail (JetEscapedBarrier.rate η d₀ / 2) s t * Real.exp (-4 * ‖v‖ ^ 2)) := by
  have hc : 0 ≤ JetEscapedBarrier.coefficient α K d₀ := by
    unfold JetEscapedBarrier.coefficient JetGaussianEscape.constant
    have := JetThermalKernel.bound_pos
    positivity
  have ht0 := JetEscapePower.tail_nonneg hs.le (JetEscapedBarrier.rate η d₀ / 2) t
  have hL : 0 ≤ JetLatticeGaussian.constant ^ 3 := by
    unfold JetLatticeGaussian.constant JetLatticeGaussian.exponential
    positivity
  unfold annulus
  apply (ENNReal.tsum_le_tsum (fun a => JetEscapedCopies.copy_sum_bound hη hηmax hK hα hαmax
    hs hsmax hd₀ hwidth ht htmax γ a x v hx)).trans_eq
  simp only [tsum_fintype, Fintype.sum_bool]
  have hA : 0 ≤ JetEscapedBarrier.coefficient α K d₀ *
      JetEscapePower.tail (JetEscapedBarrier.rate η d₀ / 2) s t * Real.exp (-4 * ‖v‖ ^ 2) :=
    mul_nonneg (mul_nonneg hc ht0) (Real.exp_nonneg _)
  simp_rw [← ENNReal.ofReal_mul hA]
  rw [← ENNReal.ofReal_add (mul_nonneg hA hL) (mul_nonneg hA hL)]
  congr 1
  unfold coefficient
  ring

theorem scale_bound {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η) (j : ℕ) :
    jetScale s₀ η j ≤ s₀ := by
  have h := scale_antitone hs₀.le hη.le (show 0 ≤ j + 1 by omega)
  simpa only [jetScale, DatumBounds.scale, Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero, mul_one] using h

theorem annular_tail_summable {β s₀ η t : ℝ} (hβ : 0 < β) (hs₀ : 0 < s₀)
    (hη : 0 < η) (ht : 0 < t) :
    Summable (fun j : ℕ => JetEscapePower.tail β (jetScale s₀ η j) t) := by
  exact (summable_nat_add_iff 1).mpr (JetEscapePower.summable_tails hβ hs₀ hη ht)

theorem annular_tail_bound {β s₀ η t : ℝ} (hβ : 0 < β) (hs₀ : 0 < s₀)
    (hη : 0 < η) (ht : 0 < t) (m : ℕ) (hm : 31 < 16 * m) :
    (∑' j : ℕ, JetEscapePower.tail β (jetScale s₀ η j) t) ≤
      ((m.factorial : ℝ) / β ^ m * t ^ m) * ∑' j : ℕ, jetScale s₀ η j ^ (16 * m - 31) := by
  have hp : 0 < 16 * m - 31 := Nat.sub_pos_of_lt hm
  have hsp := DatumBounds.summable_scale_pow s₀ hη (16 * m - 31) hp
  have hs : Summable (fun j : ℕ => jetScale s₀ η j ^ (16 * m - 31)) := by
    change Summable (fun j : ℕ => DatumBounds.scale s₀ η (j + 1) ^ (16 * m - 31))
    exact (summable_nat_add_iff (f := fun j : ℕ => DatumBounds.scale s₀ η j ^ (16 * m - 31)) 1).mpr hsp
  calc
    _ ≤ ∑' j : ℕ, ((m.factorial : ℝ) / β ^ m * t ^ m) * jetScale s₀ η j ^ (16 * m - 31) :=
      (annular_tail_summable hβ hs₀ hη ht).tsum_le_tsum
        (fun j => JetEscapePower.tail_bound hβ (DatumBounds.scale_pos (η := η) hs₀ (j + 1)) ht m hm.le)
        (hs.mul_left _)
    _ = _ := tsum_mul_left


theorem total_amplitude_bound {s₀ η K α d₀ t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1 / 32)
    (γ : ℝ) (x v : Velocity) (hx : ∀ k, |x k| ≤ 1) :
    total s₀ η K α γ d₀ t x v ≤ ENNReal.ofReal (coefficient α K d₀ *
      (∑' j : ℕ, JetEscapePower.tail (JetEscapedBarrier.rate η d₀ / 2) (jetScale s₀ η j) t) *
        Real.exp (-4 * ‖v‖ ^ 2)) := by
  have hc := coefficient_nonneg hK hd₀ α
  have hs (j : ℕ) : 0 < jetScale s₀ η j := DatumBounds.scale_pos (η := η) hs₀ (j + 1)
  have hs' (j : ℕ) : jetScale s₀ η j ≤ 1 / 8 := (scale_bound hs₀ hη j).trans hsmax
  have hβ : 0 < JetEscapedBarrier.rate η d₀ / 2 := by
    exact div_pos (JetEscapedBarrier.rate_pos hη hd₀) (by norm_num)
  have htail := annular_tail_summable hβ hs₀ hη ht
  have hsum : Summable (fun j : ℕ => coefficient α K d₀ *
      JetEscapePower.tail (JetEscapedBarrier.rate η d₀ / 2) (jetScale s₀ η j) t * Real.exp (-4 * ‖v‖ ^ 2)) :=
    (htail.mul_left _).mul_right _
  unfold total
  apply (ENNReal.tsum_le_tsum (fun j => annulus_bound hη hηmax hK hα hαmax (hs j) (hs' j) hd₀
    (JetEnvelopeGain.thermal_width_le hd₀max (hs j).le (hs' j)) ht htmax γ x v hx)).trans_eq
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg
    (mul_nonneg hc (JetEscapePower.tail_nonneg (hs j).le _ t)) (Real.exp_nonneg _)) hsum]
  congr 1
  rw [tsum_mul_right, tsum_mul_left]

def powerConstant (s₀ η α K d₀ : ℝ) (m : ℕ) : ℝ :=
  coefficient α K d₀ * ((m.factorial : ℝ) / (JetEscapedBarrier.rate η d₀ / 2) ^ m) *
    ∑' j : ℕ, jetScale s₀ η j ^ (16 * m - 31)

theorem powerConstant_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (η α : ℝ) (m : ℕ) : 0 ≤ powerConstant s₀ η α K d₀ m := by
  have hr : 0 ≤ JetEscapedBarrier.rate η d₀ := by
    unfold JetEscapedBarrier.rate
    positivity
  unfold powerConstant
  apply mul_nonneg (mul_nonneg (coefficient_nonneg hK hd₀ α) (by positivity))
  exact tsum_nonneg (fun j => pow_nonneg (DatumBounds.scale_pos (η := η) hs₀ (j + 1)).le _)

theorem arbitrary_power {s₀ η K α d₀ t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1 / 32)
    (m : ℕ) (hm : 31 < 16 * m) (γ : ℝ) (x v : Velocity) (hx : ∀ k, |x k| ≤ 1) :
    total s₀ η K α γ d₀ t x v ≤
      ENNReal.ofReal (powerConstant s₀ η α K d₀ m * t ^ m * Real.exp (-4 * ‖v‖ ^ 2)) := by
  have hc := coefficient_nonneg hK hd₀ α
  have hβ : 0 < JetEscapedBarrier.rate η d₀ / 2 :=
    div_pos (JetEscapedBarrier.rate_pos hη hd₀) (by norm_num)
  apply (total_amplitude_bound hs₀ hsmax hη hηmax hK hα hαmax hd₀ hd₀max ht htmax γ x v hx).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ coefficient α K d₀ *
        (((m.factorial : ℝ) / (JetEscapedBarrier.rate η d₀ / 2) ^ m * t ^ m) *
          ∑' j : ℕ, jetScale s₀ η j ^ (16 * m - 31)) * Real.exp (-4 * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (annular_tail_bound hβ hs₀ hη ht m hm) hc)
        (Real.exp_nonneg _)
    _ = _ := by unfold powerConstant; ring

end BoltzmannNonuniqueness.JetEscapedTotal

end

end

section

/-! # Escaped sums for arbitrary retained cold colors

The comparison hypothesis here is a pointwise bound for a color family. It is
kept explicit for application to the solutions of the finite labeled system.
All constants are independent of the retained subset.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetSpatialBox
open BoltzmannNonuniqueness.JetLatticeTail

namespace BoltzmannNonuniqueness.JetEscapedEnvelope

theorem epsilon_eq {s : ℝ} (hs : 0 < s) (K d₀ : ℝ) :
    JetSupersolution.epsilon K s (d₀ * s ^ 10) =
      JetComparisonCoefficient.coefficient K * d₀ * s ^ 9 := by
  unfold JetSupersolution.epsilon
  field_simp

theorem epsilon_small {s₀ s K d₀ : ℝ} (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (hs : 0 < s) (hss : s ≤ s₀)
    (hsmall : JetComparisonCoefficient.coefficient K * d₀ * s₀ ^ 9 ≤ 1) :
    JetSupersolution.epsilon K s (d₀ * s ^ 10) ≤ 1 := by
  rw [epsilon_eq hs]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le hss 9)
    (mul_nonneg (zero_le_one.trans (JetComparisonCoefficient.coefficient_ge_one hK)) hd₀)).trans hsmall

def escapedSum (s₀ η t : ℝ) (x : Velocity)
    (S : ℕ → Bool → Lattice → Prop) (F : ℕ → Bool → Lattice → ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, ∑' a : Bool, ∑' n : Lattice,
    {n | S j a n ∧ outside η (jetScale s₀ η j) t a x n}.indicator
      (fun n => ENNReal.ofReal (F j a n)) n

theorem sum_le_twice {s₀ η K α γ d₀ t : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (ht : 0 < t) (htmax : t ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K * d₀ * s₀ ^ 9 ≤ 1)
    (S : ℕ → Bool → Lattice → Prop) (F : ℕ → Bool → Lattice → ℝ)
    (x v : Velocity)
    (hF : ∀ j a n, S j a n → F j a n ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η j) (d₀ * jetScale s₀ η j ^ 10) t a (shifted x n, v)) :
    escapedSum s₀ η t x S F ≤ 2 * JetEscapedTotal.total s₀ η K α γ d₀ t x v := by
  classical
  have hs (j : ℕ) : 0 < jetScale s₀ η j := DatumBounds.scale_pos (η := η) hs₀ (j + 1)
  calc
    _ ≤ ∑' j : ℕ, ∑' a : Bool, ∑' n : Lattice, (2 : ℝ≥0∞) *
        {n | outside η (jetScale s₀ η j) t a x n}.indicator
          (fun n => ENNReal.ofReal (JetBarrier.barrier η K α γ (jetScale s₀ η j)
            (d₀ * jetScale s₀ η j ^ 10) t a (shifted x n, v))) n := by
      apply ENNReal.tsum_le_tsum
      intro j
      apply ENNReal.tsum_le_tsum
      intro a
      apply ENNReal.tsum_le_tsum
      intro n
      by_cases hout : outside η (jetScale s₀ η j) t a x n
      · by_cases hS : S j a n
        · simp only [mem_ofPred_eq, hS, hout, and_self, indicator_of_mem]
          have hd : 0 < d₀ * jetScale s₀ η j ^ 10 := mul_pos hd₀ (pow_pos (hs j) _)
          have hb := (hF j a n hS).trans (JetSupersolution.le_twice_barrier hK (hs j) hd
            hα hγ ht htmax (epsilon_small hK hd₀.le (hs j)
              (JetEscapedTotal.scale_bound hs₀ hη j) hsmall) η a (shifted x n, v))
          simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using
            ENNReal.ofReal_le_ofReal hb
        · simp only [mem_ofPred_eq, hS, false_and, not_false_eq_true, indicator_of_notMem]
          exact bot_le
      · simp only [mem_ofPred_eq, hout, and_false, not_false_eq_true, indicator_of_notMem,
          mul_zero, le_refl]
    _ = _ := by
      simp_rw [ENNReal.tsum_mul_left]
      rfl

def constant (s₀ η α K d₀ : ℝ) (m : ℕ) : ℝ :=
  2 * JetEscapedTotal.powerConstant s₀ η α K d₀ m * tiltConstant

theorem constant_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (η α : ℝ) (m : ℕ) : 0 ≤ constant s₀ η α K d₀ m :=
  mul_nonneg (mul_nonneg (by norm_num) (JetEscapedTotal.powerConstant_nonneg hs₀ hK hd₀ η α m))
    tiltConstant_pos.le

theorem arbitrary_power {s₀ η K α γ d₀ t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (hγ : 0 ≤ γ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1 / 32)
    (hsmall : JetComparisonCoefficient.coefficient K * d₀ * s₀ ^ 9 ≤ 1)
    (m : ℕ) (hm : 31 < 16 * m) (q : ℝ)
    (S : ℕ → Bool → Lattice → Prop) (F : ℕ → Bool → Lattice → ℝ)
    (x v : Velocity) (hx : ∀ k, |x k| ≤ 1)
    (hF : ∀ j a n, S j a n → F j a n ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η j) (d₀ * jetScale s₀ η j ^ 10) t a (shifted x n, v)) :
    escapedSum s₀ η t x S F ≤ ENNReal.ofReal (constant s₀ η α K d₀ m * t ^ m * H q v) := by
  have hp := JetEscapedTotal.powerConstant_nonneg hs₀ hK hd₀ η α m
  have hg : Real.exp (-4 * ‖v‖ ^ 2) ≤ tiltConstant * H q v := by
    apply (Real.exp_le_exp.mpr (show -4 * ‖v‖ ^ 2 ≤ -2 * ‖v‖ ^ 2 by nlinarith [sq_nonneg ‖v‖])).trans
    exact JetGaussianEscape.gaussian_le_hot q v
  calc
    _ ≤ 2 * JetEscapedTotal.total s₀ η K α γ d₀ t x v :=
      sum_le_twice hs₀ hη hK hα hγ hd₀ ht (htmax.trans (by norm_num)) hsmall S F x v hF
    _ ≤ 2 * ENNReal.ofReal (JetEscapedTotal.powerConstant s₀ η α K d₀ m * t ^ m *
        Real.exp (-4 * ‖v‖ ^ 2)) := mul_le_mul' le_rfl (JetEscapedTotal.arbitrary_power
          hs₀ hsmax hη hηmax hK hα hαmax hd₀ hd₀max ht htmax m hm γ x v hx)
    _ = ENNReal.ofReal (2 * (JetEscapedTotal.powerConstant s₀ η α K d₀ m * t ^ m *
        Real.exp (-4 * ‖v‖ ^ 2))) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ 2 * (JetEscapedTotal.powerConstant s₀ η α K d₀ m * t ^ m * (tiltConstant * H q v)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (mul_nonneg hp (pow_nonneg ht.le _)))
            (by norm_num)
        _ = _ := by unfold constant; ring

def exponent (A : ℝ) : ℕ := ⌈A⌉₊ + 2

theorem exponent_large (A : ℝ) : 31 < 16 * exponent A := by
  unfold exponent
  omega

theorem le_exponent (A : ℝ) : A ≤ (exponent A : ℝ) := by
  have h := Nat.le_ceil A
  unfold exponent
  push_cast
  linarith

/-- The same constant works for every time, spatial point, and retained subset. -/
theorem real_power {s₀ η K α γ d₀ t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (hγ : 0 ≤ γ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1 / 32)
    (hsmall : JetComparisonCoefficient.coefficient K * d₀ * s₀ ^ 9 ≤ 1) (A q : ℝ)
    (S : ℕ → Bool → Lattice → Prop) (F : ℕ → Bool → Lattice → ℝ)
    (x v : Velocity) (hx : ∀ k, |x k| ≤ 1)
    (hF : ∀ j a n, S j a n → F j a n ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η j) (d₀ * jetScale s₀ η j ^ 10) t a (shifted x n, v)) :
    escapedSum s₀ η t x S F ≤
      ENNReal.ofReal (constant s₀ η α K d₀ (exponent A) * t ^ A * H q v) := by
  apply (arbitrary_power hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max ht htmax hsmall
    (exponent A) (exponent_large A) q S F x v hx hF).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (H_nonneg q v)
  apply mul_le_mul_of_nonneg_left _ (constant_nonneg hs₀ hK hd₀ η α _)
  simpa only [Real.rpow_natCast] using
    Real.rpow_le_rpow_of_exponent_ge ht (htmax.trans (by norm_num)) (le_exponent A)

end BoltzmannNonuniqueness.JetEscapedEnvelope

end

end

section

/-! # The real mixed-gain estimate for the main cold color -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetMainGain

def sheetConstant (α q : ℝ) : ℝ :=
  (SheetTotal.bound q (2 * Real.exp (16 * (1 + α) ^ 2))).toReal + 1

theorem sheetConstant_pos (α q : ℝ) : 0 < sheetConstant α q := by
  unfold sheetConstant
  positivity

theorem sheet_bound (α q : ℝ) :
    SheetTotal.bound q (2 * Real.exp (16 * (1 + α) ^ 2)) ≤ ENNReal.ofReal (sheetConstant α q) := by
  rw [sheetConstant, ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num),
    ENNReal.ofReal_toReal (SheetTotal.bound_lt_top _ _).ne]
  exact le_add_of_nonneg_right bot_le

def coefficient (K α γ q : ℝ) : ℝ :=
  (K * max 1 (α * γ)⁻¹ * JetGaussianProduct.coefficient + JetRemainderSheet.uniformConstant K) *
    sheetConstant α q

theorem numerator_nonneg {K : ℝ} (hK : 0 ≤ K) (α γ : ℝ) :
    0 ≤ K * max 1 (α * γ)⁻¹ * JetGaussianProduct.coefficient + JetRemainderSheet.uniformConstant K := by
  have hm : 0 ≤ max 1 (α * γ)⁻¹ := zero_le_one.trans (le_max_left _ _)
  have hJ := JetThermalKernel.bound_pos
  have hL := JetComparisonCoefficient.coefficient_ge_one hK
  unfold JetGaussianProduct.coefficient JetRemainderSheet.uniformConstant
  positivity

theorem coefficient_nonneg {K : ℝ} (hK : 0 ≤ K) (α γ q : ℝ) : 0 ≤ coefficient K α γ q :=
  mul_nonneg (numerator_nonneg hK α γ) (sheetConstant_pos α q).le

theorem amplitude_nonneg {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 ≤ t) (η α γ : ℝ) (a : Bool) (x : Space) :
    0 ≤ JetEnvelopeGain.amplitude η K α γ s d t a x := by
  have hc := JetCoreSheet.amplitude_nonneg hK hs ht α γ
  have hε := JetSupersolution.epsilon_nonneg hK hs hd
  have hm := JetBarrierCollision.massScale_nonneg hK hs η α γ d t a x
  unfold JetEnvelopeGain.amplitude JetRemainderSheet.amplitude
  positivity

theorem nonnegative_gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {K α γ s d₀ t q : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (ht : 0 < t) (htmax : t ≤ 1 / 32) (hq₁ : 1 < q) (hq₂ : q < 2)
    (η : ℝ) (a : Bool) (x : Space) :
    ∀ᵐ v : Velocity, nonnegativeGain
      (fun w => ENNReal.ofReal (JetSupersolution.U η K α γ s (d₀ * s ^ 10) t a (x, w)))
      (fun w => ENNReal.ofReal (H q w)) v ≤ ENNReal.ofReal (coefficient K α γ q / (s + t) * H q v) := by
  have hd : 0 < d₀ * s ^ 10 := by positivity
  have ht1 : t ≤ 1 := htmax.trans (by norm_num)
  have hA := JetEnvelopeGain.amplitude_bound (α := α) (γ := γ) hK hs hd ht ht1
    (JetEnvelopeGain.thermal_scale_small hd₀max hs hsmax ht.le htmax) η a x
  filter_upwards [JetEnvelopeGain.gain_bound hcarleman hK hα hγ hs hd
    (JetEnvelopeGain.thermal_width_le hd₀max hs.le hsmax) ht.le ht1 hq₁ hq₂ η a x] with v hv
  apply hv.trans
  calc
    _ ≤ ENNReal.ofReal (H q v) * (ENNReal.ofReal
        ((K * max 1 (α * γ)⁻¹ * JetGaussianProduct.coefficient + JetRemainderSheet.uniformConstant K) /
          (s + t)) * ENNReal.ofReal (sheetConstant α q)) :=
      mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal hA) (sheet_bound α q))
    _ = _ := by
      rw [← ENNReal.ofReal_mul (div_nonneg (numerator_nonneg hK α γ) (by positivity)),
        ← ENNReal.ofReal_mul (H_nonneg q v)]
      congr 1
      unfold coefficient
      ring

theorem gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {K α γ s d₀ t q : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (ht : 0 < t) (htmax : t ≤ 1 / 32) (hq₁ : 1 < q) (hq₂ : q < 2)
    (η : ℝ) (a : Bool) (x : Space) :
    ∀ᵐ v : Velocity,
      Integrable (MixedRealGain.integrand
        (fun w => JetSupersolution.U η K α γ s (d₀ * s ^ 10) t a (x, w)) (H q) v) gainPairMeasure ∧
      MixedRealGain.gain (fun w => JetSupersolution.U η K α γ s (d₀ * s ^ 10) t a (x, w)) (H q) v ≤
        coefficient K α γ q / (s + t) * H q v := by
  have hd : 0 < d₀ * s ^ 10 := by positivity
  have hfm := JetSupersolution.measurable_velocity hd η K α γ s t a x
  have hf := fun w => JetSupersolution.nonneg hK hs hd η α γ t a (x, w)
  filter_upwards [nonnegative_gain_bound hcarleman hK hα hγ hs hsmax hd₀ hd₀max ht htmax hq₁ hq₂ η a x]
    with v hv
  exact ⟨MixedRealGain.integrable_of_bound hfm (ChartKernel.measurable_H q) hf (H_nonneg q) v hv,
    MixedRealGain.gain_le_of_bound hfm (ChartKernel.measurable_H q) hf (H_nonneg q)
      (mul_nonneg (div_nonneg (coefficient_nonneg hK α γ q) (by positivity)) (H_nonneg q v)) v hv⟩

theorem dominated_gain (hcarleman : Published.GPV2009CarlemanInput)
    {K α γ s d₀ t q z : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (ht : 0 < t) (htmax : t ≤ 1 / 32) (hq₁ : 1 < q) (hq₂ : q < 2) (hz : 0 ≤ z)
    (η : ℝ) (a : Bool) (x : Space) {f h : Velocity → ℝ}
    (hfm : Measurable f) (hhm : Measurable h) (hf : ∀ w, 0 ≤ f w) (hh : ∀ w, 0 ≤ h w)
    (hfU : ∀ w, f w ≤ JetSupersolution.U η K α γ s (d₀ * s ^ 10) t a (x, w))
    (hhH : ∀ w, h w ≤ z * H q w) :
    ∀ᵐ v : Velocity, Integrable (MixedRealGain.integrand f h v) gainPairMeasure ∧
      MixedRealGain.gain f h v ≤ (z * coefficient K α γ q / (s + t)) * H q v := by
  filter_upwards [gain_bound hcarleman hK hα hγ hs hsmax hd₀ hd₀max ht htmax hq₁ hq₂ η a x] with v hv
  have hi := MixedRealGain.integrable_const_mul_right hv.1 z
  refine ⟨MixedRealGain.integrable_of_le hfm hhm hf hh hfU hhH v hi, ?_⟩
  calc
    _ ≤ MixedRealGain.gain
        (fun w => JetSupersolution.U η K α γ s (d₀ * s ^ 10) t a (x, w)) (fun w => z * H q w) v :=
      MixedRealGain.gain_mono hfm hhm hf hh hfU hhH v hi
    _ = z * MixedRealGain.gain
        (fun w => JetSupersolution.U η K α γ s (d₀ * s ^ 10) t a (x, w)) (H q) v :=
      MixedRealGain.gain_const_mul_right _ _ _ _
    _ ≤ z * (coefficient K α γ q / (s + t) * H q v) := mul_le_mul_of_nonneg_left hv.2 hz
    _ = _ := by ring

end BoltzmannNonuniqueness.JetMainGain

end

end

section

/-! # Annular mask error after integrating out the thermal variable -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

def maskError (r η s d μ t : ℝ) (a : Bool) (p : Transverse × (Transverse × ℝ)) : ℝ :=
  ((mask η s a).indicator (fun _ => (1:ℝ)) (r • (p.1-t • (d • p.2.1)))-
    (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1*
      (stripe s a).indicator (fun _ => (1:ℝ)) (r • (p.1-t • (d • p.2.1))))*
    JetThermalKernel.J (SheetMeasures.join p.2)

theorem maskError_measurable (r η s d μ t : ℝ) (a : Bool) :
    Measurable (maskError r η s d μ t a) := by
  have hm : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (mask η s a).indicator (fun _ => (1:ℝ)) (r • (p.1-t • (d • p.2.1)))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_mask η s a)).comp (by fun_prop)
  have hs : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (stripe s a).indicator (fun _ => (1:ℝ)) (r • (p.1-t • (d • p.2.1)))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_stripe s a)).comp (by fun_prop)
  have hc : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1) :=
    (measurable_const.indicator (measurableSet_scaleShell η μ)).comp measurable_fst
  exact (hm.sub (hc.mul hs)).mul
    ((JetThermalKernel.J_smooth.continuous.measurable.comp SheetMeasures.join.measurable).comp
      measurable_snd)

theorem maskError_abs_le (r η s d μ t : ℝ) (a : Bool) (p : Transverse × (Transverse × ℝ)) :
    |maskError r η s d μ t a p| ≤ 2*JetThermalKernel.J (SheetMeasures.join p.2) := by
  have hi (A : Set Transverse) (y : Transverse) : |A.indicator (fun _ => (1:ℝ)) y| ≤ 1 := by
    by_cases h : y ∈ A <;> simp [h]
  unfold maskError
  rw [abs_mul,abs_of_nonneg (JetThermalKernel.J_nonneg _)]
  apply mul_le_mul_of_nonneg_right _ (JetThermalKernel.J_nonneg _)
  apply (abs_sub _ _).trans
  have hp : |(scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1*
      (stripe s a).indicator (fun _ => (1:ℝ)) (r • (p.1-t • (d • p.2.1)))| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (hi _ _) (hi _ _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  linarith [hi (mask η s a) (r • (p.1-t • (d • p.2.1)))]

theorem maskError_integrable (r η s d μ t : ℝ) (a : Bool)
    (ν : Measure Transverse) [IsFiniteMeasure ν] :
    Integrable (maskError r η s d μ t a) (ν.prod ((volume : Measure Transverse).prod volume)) := by
  have hJ := (HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable).comp_snd ν
  apply (hJ.const_mul 2).mono' (maskError_measurable r η s d μ t a).aestronglyMeasurable
  filter_upwards [] with p
  exact maskError_abs_le r η s d μ t a p

theorem maskError_average_L1_le (r η s d μ t : ℝ) (a : Bool)
    (ν : Measure Transverse) [IsFiniteMeasure ν] :
    (∫ y, |∫ w, maskError r η s d μ t a (y,w)
      ∂(volume : Measure Transverse).prod volume| ∂ν) ≤
    ∫ p, |maskError r η s d μ t a p| ∂ν.prod ((volume : Measure Transverse).prod volume) := by
  have hi := maskError_integrable r η s d μ t a ν
  change (∫ y, ‖∫ w, maskError r η s d μ t a (y,w)
    ∂(volume : Measure Transverse).prod volume‖ ∂ν) ≤
    ∫ p, ‖maskError r η s d μ t a p‖ ∂ν.prod ((volume : Measure Transverse).prod volume)
  rw [integral_prod _ hi.norm]
  apply integral_mono hi.integral_prod_left.norm hi.integral_norm_prod_left
  intro y
  exact norm_integral_le_integral_norm _

theorem maskError_average_L1_tendsto {r s d : ℕ → ℝ} {μ : ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    (η t : ℝ) (a : Bool) (Ω : Set Transverse) (hΩ : volume Ω < ⊤) :
    Tendsto (fun n => ∫ y, |∫ w, maskError (r n) η (r n*s n) (d n) μ t a (y,w)
      ∂(volume : Measure Transverse).prod volume| ∂volume.restrict Ω) atTop (𝓝 0) := by
  let _ : IsFiniteMeasure ((volume : Measure Transverse).restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hΩ⟩
  have hb := spatial_mask_L1_tendsto hr hrlim hslim hdlim η t a Ω hΩ
  have he : Tendsto (fun n => ∫ p, |maskError (r n) η (r n*s n) (d n) μ t a p|
      ∂(volume.restrict Ω).prod ((volume : Measure Transverse).prod volume)) atTop (𝓝 0) := by
    simpa only [maskError,abs_mul,abs_of_nonneg (JetThermalKernel.J_nonneg _)] using hb
  exact squeeze_zero (fun n => integral_nonneg (fun y => abs_nonneg _))
    (fun n => maskError_average_L1_le (r n) η (r n*s n) (d n) μ t a _) he

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # Real velocity integrability and quantitative tails from the cold exponential bound -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.SheetClass

theorem weighted_integrable_of_exponentialMoment {f : Velocity → ℝ} {M : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v)
    (hb : exponentialMoment (volume.withDensity (fun v => ENNReal.ofReal (f v))) ≤ ENNReal.ofReal M) :
    Integrable (fun v => Real.exp (2*‖v‖^2)*f v) := by
  have hn : ∀ v, 0 ≤ Real.exp (2*‖v‖^2)*f v := fun v => mul_nonneg (Real.exp_pos _).le (hf v)
  refine ⟨(by fun_prop),?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ hn)).mpr
  rw [← exponentialMoment_density hfm]
  exact hb.trans_lt ENNReal.ofReal_lt_top

theorem weighted_integral_le {f : Velocity → ℝ} {M : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) (hM : 0 ≤ M)
    (hb : exponentialMoment (volume.withDensity (fun v => ENNReal.ofReal (f v))) ≤ ENNReal.ofReal M) :
    (∫ v, Real.exp (2*‖v‖^2)*f v) ≤ M := by
  have hi := weighted_integrable_of_exponentialMoment hfm hf hb
  apply (ENNReal.ofReal_le_ofReal_iff hM).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun v => mul_nonneg (Real.exp_pos _).le (hf v))),
    ← exponentialMoment_density hfm]
  exact hb

theorem density_integrable_of_exponentialMoment {f : Velocity → ℝ} {M : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v)
    (hb : exponentialMoment (volume.withDensity (fun v => ENNReal.ofReal (f v))) ≤ ENNReal.ofReal M) :
    Integrable f := by
  apply (weighted_integrable_of_exponentialMoment hfm hf hb).mono' hfm.aestronglyMeasurable
  filter_upwards [] with v
  rw [Real.norm_of_nonneg (hf v)]
  exact le_mul_of_one_le_left (hf v) (Real.one_le_exp (by positivity))

theorem density_mass_le {f : Velocity → ℝ} {M : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) (hM : 0 ≤ M)
    (hb : exponentialMoment (volume.withDensity (fun v => ENNReal.ofReal (f v))) ≤ ENNReal.ofReal M) :
    (∫ v, f v) ≤ M := by
  apply (integral_mono (density_integrable_of_exponentialMoment hfm hf hb)
    (weighted_integrable_of_exponentialMoment hfm hf hb) (fun v =>
      le_mul_of_one_le_left (hf v) (Real.one_le_exp (by positivity)))).trans
  exact weighted_integral_le hfm hf hM hb

theorem density_tail_le {f : Velocity → ℝ} {M R : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hb : exponentialMoment (volume.withDensity (fun v => ENNReal.ofReal (f v))) ≤ ENNReal.ofReal M) :
    (∫ v in {v : Velocity | R < ‖v‖}, f v) ≤ Real.exp (-2*R^2)*M := by
  let S := {v : Velocity | R < ‖v‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  have hi := density_integrable_of_exponentialMoment hfm hf hb
  have hw := weighted_integrable_of_exponentialMoment hfm hf hb
  rw [← integral_indicator hS]
  calc
    _ ≤ ∫ v, Real.exp (-2*R^2)*(Real.exp (2*‖v‖^2)*f v) := by
      apply integral_mono (hi.indicator hS) (hw.const_mul _)
      intro v
      by_cases hv : v ∈ S
      · rw [indicator_of_mem hv]
        have hs : R^2 ≤ ‖v‖^2 := (sq_le_sq₀ hR (norm_nonneg v)).mpr hv.le
        have he : 1 ≤ Real.exp (-2*R^2)*Real.exp (2*‖v‖^2) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith)
        nlinarith [mul_le_mul_of_nonneg_right he (hf v)]
      · rw [indicator_of_notMem hv]
        exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hf v))
    _ = Real.exp (-2*R^2)*(∫ v, Real.exp (2*‖v‖^2)*f v) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (weighted_integral_le hfm hf hM hb) (Real.exp_pos _).le

end BoltzmannNonuniqueness.SheetClass

end

end

section

/-! # Scale-uniform mass and Gaussian velocity tails below a cold supersolution -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetEnvelopeGain

def momentConstant (K α γ : ℝ) : ℝ :=
  (K*max 1 (α*γ)⁻¹*JetGaussianProduct.coefficient+JetRemainderSheet.uniformConstant K)*
    (8*Real.exp (16*(1+α)^2))

theorem momentConstant_nonneg {K : ℝ} (hK : 0 ≤ K) (α γ : ℝ) : 0 ≤ momentConstant K α γ :=
  mul_nonneg (JetMainGain.numerator_nonneg hK α γ) (by positivity)

theorem exponential_moment_uniform {K α γ s d₀ t : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (hsmax : s ≤ 1/8)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (η : ℝ) (a : Bool) (x : Space) :
    SheetClass.exponentialMoment (volume.withDensity (fun v =>
      ENNReal.ofReal (JetSupersolution.U η K α γ s (d₀*s^10) t a (x,v)))) ≤
        ENNReal.ofReal (momentConstant K α γ/(s+t)) := by
  have hd : 0 < d₀*s^10 := by positivity
  have hm := exponential_moment_le hK hα hγ hs hd (thermal_width_le hd₀max hs.le hsmax)
    ht.le (htmax.trans (by norm_num)) η a x
  apply hm.trans (ENNReal.ofReal_le_ofReal ?_)
  have ha := amplitude_bound (α := α) (γ := γ) hK hs hd ht (htmax.trans (by norm_num))
    (thermal_scale_small hd₀max hs hsmax ht.le htmax) η a x
  calc
    _ ≤ ((K*max 1 (α*γ)⁻¹*JetGaussianProduct.coefficient+JetRemainderSheet.uniformConstant K)/(s+t))*
        (8*Real.exp (16*(1+α)^2)) := mul_le_mul_of_nonneg_right ha (by positivity)
    _ = _ := by unfold momentConstant; ring

theorem dominated_exponential_moment {K α γ s d₀ t : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (hsmax : s ≤ 1/8)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (η : ℝ) (a : Bool) (x : Space) {f : Velocity → ℝ}
    (hf : ∀ v, f v ≤ JetSupersolution.U η K α γ s (d₀*s^10) t a (x,v)) :
    SheetClass.exponentialMoment (volume.withDensity (fun v => ENNReal.ofReal (f v))) ≤
      ENNReal.ofReal (momentConstant K α γ/(s+t)) :=
  (SheetClass.exponentialMoment_mono (withDensity_mono (ae_of_all _
    (fun v => ENNReal.ofReal_le_ofReal (hf v))))).trans
      (exponential_moment_uniform hK hα hγ hs hsmax hd₀ hd₀max ht htmax η a x)

theorem dominated_mass_tail {K α γ s d₀ t : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (hsmax : s ≤ 1/8)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (η : ℝ) (a : Bool) (x : Space) {f : Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v)
    (hfU : ∀ v, f v ≤ JetSupersolution.U η K α γ s (d₀*s^10) t a (x,v)) :
    Integrable f ∧ (∫ v, f v) ≤ momentConstant K α γ/(s+t) ∧
      ∀ R : ℝ, 0 ≤ R → (∫ v in {v : Velocity | R < ‖v‖}, f v) ≤
        Real.exp (-2*R^2)*(momentConstant K α γ/(s+t)) := by
  have hb := dominated_exponential_moment hK hα hγ hs hsmax hd₀ hd₀max ht htmax η a x hfU
  have hM : 0 ≤ momentConstant K α γ/(s+t) :=
    div_nonneg (momentConstant_nonneg hK α γ) (by positivity)
  exact ⟨SheetClass.density_integrable_of_exponentialMoment hfm hf hb,
    SheetClass.density_mass_le hfm hf hM hb,fun R hR => SheetClass.density_tail_le hfm hf hM hR hb⟩

end BoltzmannNonuniqueness.JetEnvelopeGain

end

end

end OAI
