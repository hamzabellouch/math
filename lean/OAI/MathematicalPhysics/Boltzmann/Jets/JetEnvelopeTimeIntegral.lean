import OAI.MathematicalPhysics.Boltzmann.Collision.AngularPairTests
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionMeasure
import OAI.MathematicalPhysics.Boltzmann.Collision.SheetIntervals
import OAI.MathematicalPhysics.Boltzmann.Jets.JetSupersolutions

namespace OAI

section

/-! # The transported core is dominated by an admissible Gaussian sheet -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetCoreMeasure
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetCoreSheet

def amplitude (K α γ s t : ℝ) : ℝ :=
  ((K * max 1 (α * γ)⁻¹) / (s + t)) * JetGaussianProduct.coefficient

theorem amplitude_nonneg {K s t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (ht : 0 ≤ t) (α γ : ℝ) :
    0 ≤ amplitude K α γ s t := by
  have := JetThermalKernel.bound_pos
  unfold amplitude JetGaussianProduct.coefficient
  positivity

theorem parameter_bound {K α γ s t : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (ht : 0 ≤ t)
    (η d : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) :
    JetCoreDensity.weight η K α γ s d t a x w ≤
      amplitude K α γ s t * JetGaussianProduct.density w := by
  apply (JetCoreDensity.weight_bound hK hα hγ hs ht η d a x w).trans
  calc
    _ ≤ ((K * max 1 (α * γ)⁻¹) / (s + t)) *
        (JetGaussianProduct.coefficient * JetGaussianProduct.density w) :=
      mul_le_mul_of_nonneg_left (JetGaussianProduct.kernel_bound w) (by positivity)
    _ = _ := by unfold amplitude; ring

theorem measure_domination {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t)
    (η : ℝ) (a : Bool) (x : Space) :
    volume.withDensity (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x, v))) ≤
      ENNReal.ofReal (amplitude K α γ s t) •
        SheetMeasures.sheetLaw d (JetAxialLaw.law (sign a) α γ s d t x.2) := by
  rw [← JetCoreDensity.measure_identity hα.le hγ.le hs hd ht,
    ← JetGaussianProduct.parameterLaw_map hα.le hγ.le hs hd ht]
  have hm := (velocity_measurePreserving hα.le hγ.le hs hd ht (sign a) x.2).measurable
  rw [← Measure.map_smul _ hm.aemeasurable]
  apply Measure.map_mono _ hm
  rw [JetGaussianProduct.parameterLaw_density]
  have hg : Measurable (fun w => ENNReal.ofReal (JetGaussianProduct.density w)) := by
    unfold JetGaussianProduct.density GaussianDiskMixture.gaussianDensity
    fun_prop
  rw [← withDensity_smul _ hg]
  apply withDensity_mono
  filter_upwards [] with w
  change ENNReal.ofReal (JetCoreDensity.weight η K α γ s d t a x w) ≤
    ENNReal.ofReal (amplitude K α γ s t) * ENNReal.ofReal (JetGaussianProduct.density w)
  rw [← ENNReal.ofReal_mul (amplitude_nonneg hK hs ht α γ)]
  exact ENNReal.ofReal_le_ofReal (parameter_bound hK hα hγ hs ht η d a x w)

theorem normalized_gain_bound {K α γ s d t q : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1 / 16) (ht : 0 ≤ t)
    (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (a : Bool) (x : Space)
    {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain
      (volume.withDensity (fun p => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x, p)))) q v ≤
      ENNReal.ofReal (amplitude K α γ s t) *
        SheetTotal.bound q (2 * Real.exp (16 * (|sign a| + α) ^ 2)) := by
  have hp := JetAxialLaw.probability (sign a) α γ s d t x.2
  have he : SheetClass.IsElementary (2 * Real.exp (16 * (|sign a| + α) ^ 2))
      (SheetMeasures.sheetLaw d (JetAxialLaw.law (sign a) α γ s d t x.2)) :=
    ⟨d, JetAxialLaw.law (sign a) α γ s d t x.2, hd.le, by linarith, hp,
      JetAxialLaw.moment hα.le hγ.le hs hd hdmax ht (sign a) x.2, rfl⟩
  apply (chartGain_mono_measure (measure_domination hK hα hγ hs hd ht η a x) _ v).trans
  rw [chartGain_smul_measure]
  exact mul_le_mul' le_rfl (SheetClass.elementary_bound hq₁ hq₂ he hv)


theorem gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {K α γ s d t q : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s)
    (hd : 0 < d) (hdmax : d ≤ 1 / 16) (ht : 0 ≤ t) (hq₁ : 1 < q) (hq₂ : q < 2)
    (η : ℝ) (a : Bool) (x : Space) :
    ∀ᵐ v : Velocity, nonnegativeGain
      (fun p => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x, p)))
      (fun p => ENNReal.ofReal (H q p)) v ≤
      ENNReal.ofReal (H q v) * (ENNReal.ofReal (amplitude K α γ s t) *
        SheetTotal.bound q (2 * Real.exp (16 * (|sign a| + α) ^ 2))) := by
  have hf : Measurable (fun p => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x, p))) :=
    ((JetFreeTransport.measurable_free η K α γ s d t a).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  apply nonnegativeGain_le_of_chartGain hcarleman hf ((measurable_H q).ennreal_ofReal)
  filter_upwards [SheetApplication.ae_transverse_ne_zero] with v hv
  rw [SheetApplication.gain_H_eq]
  exact mul_le_mul' le_rfl (normalized_gain_bound hK hα hγ hs hd hdmax ht hq₁ hq₂ η a x hv)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # The cold supersolution for every finite relative-speed cutoff -/

noncomputable section

open MeasureTheory Filter
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCutoffSupersolution

theorem ae_supersolution {K s d α γ : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hε : JetSupersolution.epsilon K s d ≤ 1)
    (η b : ℝ) (label : Bool) (p : JetPrototype.Phase) :
    ∀ᵐ t, 0 < t → t ≤ 1 →
      HasDerivAt (JetSupersolution.along η K α γ s d label p)
        (deriv (JetSupersolution.along η K α γ s d label p) t) t ∧
      CollisionCutoff.gain b
        (fun v => JetSupersolution.U η K α γ s d t label ((JetBarrier.flight t p).1, v)) p.2 ≤
          deriv (JetSupersolution.along η K α γ s d label p) t := by
  filter_upwards [JetSupersolution.ae_supersolution hK hs hd hα hγ hε η label p 0]
    with t ht htpos htmax
  obtain ⟨hu, hg⟩ := ht htpos htmax
  refine ⟨hu, ?_⟩
  have hm := JetBarrierCollision.integrable_gain hK hs hd htmax η α γ label (JetBarrier.flight t p).1 p.2
  have hi := GainOrder.integrable_of_le
    (JetSupersolution.measurable_velocity hd η K α γ s t label (JetBarrier.flight t p).1)
    (fun v => JetSupersolution.nonneg hK hs hd η α γ t label ((JetBarrier.flight t p).1, v))
    (fun v => JetSupersolution.le_twice_barrier hK hs hd hα hγ htpos htmax hε η label
      ((JetBarrier.flight t p).1, v)) p.2 (GainOrder.integrable_const_mul 2 p.2 hm)
  exact (CollisionCutoff.gain_le b
    (JetSupersolution.measurable_velocity hd η K α γ s t label (JetBarrier.flight t p).1)
    (fun v => JetSupersolution.nonneg hK hs hd η α γ t label ((JetBarrier.flight t p).1, v))
    p.2 0 hi).trans hg

end BoltzmannNonuniqueness.JetCutoffSupersolution

end

end

section

/-! # Integral cold supersolution, including the initial right trace -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetIntegralSupersolution

theorem integral_from_right_trace {u g : ℝ → ℝ} {l t : ℝ} (ht : 0 < t)
    (hu : ∀ a, 0 < a → a ≤ t → AbsolutelyContinuousOnInterval u a t)
    (hl : Tendsto u (𝓝[>] 0) (𝓝 l)) (hg : IntervalIntegrable g volume 0 t)
    (hd : ∀ᵐ r, r ∈ Ioc 0 t → g r ≤ deriv u r) :
    l + (∫ r in 0..t, g r) ≤ u t := by
  have hgsub (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ t) :
      IntervalIntegrable g volume a b := by
    apply hg.mono_set
    rw [uIcc_of_le hab, uIcc_of_le ht.le]
    intro r hr
    exact ⟨ha.trans hr.1, hr.2.trans hb⟩
  have hineq (a : ℝ) (ha : a ∈ Ioc 0 t) : u a + (∫ r in a..t, g r) ≤ u t := by
    have hac := hu a ha.1 ha.2
    have hbound : (∫ r in a..t, g r) ≤ ∫ r in a..t, deriv u r := by
      apply intervalIntegral.integral_mono_ae_restrict ha.2
        (hgsub a t ha.1.le ha.2 le_rfl) hac.intervalIntegrable_deriv
      filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Icc] with r hr hmem
      exact hr ⟨ha.1.trans_le hmem.1, hmem.2⟩
    rw [hac.integral_deriv_eq_sub] at hbound
    linarith
  have hp := (hg.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)).continuousOn
  rw [uIcc_of_le ht.le] at hp
  have hplim : Tendsto (fun a => ∫ r in 0..a, g r) (𝓝[>] 0) (𝓝 0) := by
    have h := (hp 0 ⟨le_rfl, ht.le⟩).tendsto
    rw [nhdsWithin_Icc_eq_nhdsGE ht] at h
    simpa only [intervalIntegral.integral_same] using
      h.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hlim : Tendsto (fun a => u a + ((∫ r in 0..t, g r) - ∫ r in 0..a, g r))
      (𝓝[>] 0) (𝓝 (l + ∫ r in 0..t, g r)) := by
    simpa only [sub_zero] using hl.add (tendsto_const_nhds.sub hplim)
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT ht] with a ha
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hgsub 0 a le_rfl ha.1.le ha.2.le) (hgsub a t ha.1.le ha.2.le le_rfl)
  have hb := hineq a ⟨ha.1, ha.2.le⟩
  linarith

/-- This is the integral supersolution used to dominate each positive Picard
iterate. Integrability of the gain is the only trajectory hypothesis. -/
theorem cutoff_integral_bound {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : JetSupersolution.epsilon K s d ≤ 1) (η b : ℝ) (label : Bool) (p : JetPrototype.Phase)
    (hgi : IntervalIntegrable (fun r => CollisionCutoff.gain b
      (fun v => JetSupersolution.U η K α γ s d r label ((JetBarrier.flight r p).1, v)) p.2) volume 0 t) :
    density η K α γ s d label p +
      (∫ r in 0..t, CollisionCutoff.gain b
        (fun v => JetSupersolution.U η K α γ s d r label ((JetBarrier.flight r p).1, v)) p.2) ≤
      JetSupersolution.along η K α γ s d label p t := by
  obtain ⟨l, hl, hlim⟩ := JetBarrierTrace.supersolution_right_limit hK hα hγ hs hd η label p
  have hb := integral_from_right_trace ht
    (fun a ha hat => JetBarrierTrace.supersolution_ac hα hγ hs ha hat η K d label p) hlim hgi
    (by
      filter_upwards [JetCutoffSupersolution.ae_supersolution hK hs hd hα hγ hε η b label p]
        with r hr hmem
      exact (hr hmem.1 (hmem.2.trans htmax)).2)
  exact (add_le_add hl le_rfl).trans hb

end BoltzmannNonuniqueness.JetIntegralSupersolution

end

end

section

/-! # Positive cold Picard iterates remain below the actual supersolution

The loss may be supplied by the full labeled iterate. No estimate for the hot
component is used. The convergence and measurability of the iteration are
separate parts of the local existence construction.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetPicardComparison

def attenuation (ν : ℝ → JetPrototype.Phase → ℝ) (a t : ℝ) (p : JetPrototype.Phase) : ℝ :=
  Real.exp (-(∫ r in a..t, ν r (JetBarrier.flight r p)))

theorem attenuation_nonneg (ν : ℝ → JetPrototype.Phase → ℝ) (a t : ℝ) (p : JetPrototype.Phase) :
    0 ≤ attenuation ν a t p := (Real.exp_pos _).le

theorem attenuation_le_one {ν : ℝ → JetPrototype.Phase → ℝ} {a t : ℝ}
    {p : JetPrototype.Phase}
    (hat : a ≤ t) (hν : ∀ r ∈ Icc a t, 0 ≤ ν r (JetBarrier.flight r p)) :
    attenuation ν a t p ≤ 1 := by
  have hi : 0 ≤ ∫ r in a..t, ν r (JetBarrier.flight r p) :=
    intervalIntegral.integral_nonneg hat hν
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hi)

def alongStep (η K α γ s d b : ℝ) (a : Bool) (ν : ℝ → JetPrototype.Phase → ℝ)
    (c : ℝ → JetPrototype.Phase → ℝ) (t : ℝ) (p : JetPrototype.Phase) : ℝ :=
  density η K α γ s d a p * attenuation ν 0 t p +
    ∫ r in 0..t, attenuation ν r t p * CollisionCutoff.gain b
      (fun v => c r ((JetBarrier.flight r p).1, v)) p.2

def step (η K α γ s d b : ℝ) (a : Bool) (ν : ℝ → JetPrototype.Phase → ℝ)
    (c : ℝ → JetPrototype.Phase → ℝ) (t : ℝ) (p : JetPrototype.Phase) : ℝ :=
  alongStep η K α γ s d b a ν c t (JetBarrier.flight (-t) p)

def picard (η K α γ s d b : ℝ) (a : Bool) (ν : ℕ → ℝ → JetPrototype.Phase → ℝ) :
    ℕ → ℝ → JetPrototype.Phase → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => step η K α γ s d b a (ν n) (picard η K α γ s d b a ν n)

theorem gain_nonneg {f : Velocity → ℝ} (hf : ∀ v, 0 ≤ f v) (b : ℝ) (v : Velocity) :
    0 ≤ CollisionCutoff.gain b f v := by
  apply integral_nonneg
  intro p
  exact mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _) (hf _)) (hf _)

theorem alongStep_nonneg {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (η α γ b : ℝ) (a : Bool) (ν : ℝ → JetPrototype.Phase → ℝ)
    {c : ℝ → JetPrototype.Phase → ℝ} (hc : ∀ r ∈ Icc 0 t, ∀ p, 0 ≤ c r p)
    (p : JetPrototype.Phase) : 0 ≤ alongStep η K α γ s d b a ν c t p := by
  apply add_nonneg (mul_nonneg (density_nonneg hK hs hd η α γ a p) (attenuation_nonneg _ _ _ _))
  apply intervalIntegral.integral_nonneg ht
  intro r hr
  exact mul_nonneg (attenuation_nonneg _ _ _ _) (gain_nonneg (fun v => hc r hr _) b p.2)

theorem picard_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (η α γ b : ℝ) (a : Bool) (ν : ℕ → ℝ → JetPrototype.Phase → ℝ) :
    ∀ n t, 0 ≤ t → ∀ p, 0 ≤ picard η K α γ s d b a ν n t p := by
  intro n
  induction n with
  | zero => intro t ht p; exact le_rfl
  | succ n ih =>
    intro t ht p
    exact alongStep_nonneg hK hs hd ht η α γ b a (ν n)
      (fun r hr q => ih r hr.1 q) (JetBarrier.flight (-t) p)

theorem cutoff_mono {K α γ s d r : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (hr : 0 < r) (hrmax : r ≤ 1)
    (hε : JetSupersolution.epsilon K s d ≤ 1) (η b : ℝ) (a : Bool) (x : Space)
    {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ v, 0 ≤ f v)
    (hU : ∀ v, f v ≤ JetSupersolution.U η K α γ s d r a (x, v)) (v : Velocity) :
    CollisionCutoff.gain b f v ≤ CollisionCutoff.gain b
      (fun w => JetSupersolution.U η K α γ s d r a (x, w)) v := by
  have hUm := JetSupersolution.measurable_velocity hd η K α γ s r a x
  have hUn := fun w => JetSupersolution.nonneg hK hs hd η α γ r a (x, w)
  have hUi := GainOrder.integrable_of_le hUm hUn
    (fun w => JetSupersolution.le_twice_barrier hK hs hd hα hγ hr hrmax hε η a (x, w)) v
    (GainOrder.integrable_const_mul 2 v (JetBarrierCollision.integrable_gain hK hs hd hrmax η α γ a x v))
  have hfi := GainOrder.integrable_of_le hm hf hU v hUi
  apply integral_mono (CollisionCutoff.integrable_gain b hm hf v hfi)
    (CollisionCutoff.integrable_gain b hUm hUn v hUi)
  intro p
  unfold CollisionCutoff.integrand
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hU _) (CollisionCutoff.kernel_nonneg _ _ _ _))
    (hU _) (hf _) (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _) (hUn _))

theorem alongStep_le {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : JetSupersolution.epsilon K s d ≤ 1) (η b : ℝ) (a : Bool)
    (ν : ℝ → JetPrototype.Phase → ℝ) (c : ℝ → JetPrototype.Phase → ℝ) (p : JetPrototype.Phase)
    (hν : ∀ r ∈ Icc 0 t, 0 ≤ ν r (JetBarrier.flight r p))
    (hcm : ∀ r ∈ Ioc 0 t, Measurable (fun v => c r ((JetBarrier.flight r p).1, v)))
    (hcn : ∀ r ∈ Ioc 0 t, ∀ v, 0 ≤ c r ((JetBarrier.flight r p).1, v))
    (hcU : ∀ r ∈ Ioc 0 t, ∀ v, c r ((JetBarrier.flight r p).1, v) ≤
      JetSupersolution.U η K α γ s d r a ((JetBarrier.flight r p).1, v))
    (hci : IntervalIntegrable (fun r => attenuation ν r t p * CollisionCutoff.gain b
      (fun v => c r ((JetBarrier.flight r p).1, v)) p.2) volume 0 t)
    (hUi : IntervalIntegrable (fun r => CollisionCutoff.gain b
      (fun v => JetSupersolution.U η K α γ s d r a ((JetBarrier.flight r p).1, v)) p.2) volume 0 t) :
    alongStep η K α γ s d b a ν c t p ≤ JetSupersolution.along η K α γ s d a p t := by
  have hint : (∫ r in 0..t, attenuation ν r t p * CollisionCutoff.gain b
      (fun v => c r ((JetBarrier.flight r p).1, v)) p.2) ≤
      ∫ r in 0..t, CollisionCutoff.gain b
        (fun v => JetSupersolution.U η K α γ s d r a ((JetBarrier.flight r p).1, v)) p.2 := by
    apply intervalIntegral.integral_mono_ae_restrict ht.le hci hUi
    have hzero : ∀ᵐ r : ℝ, r ≠ 0 := by
      apply ae_iff.mpr
      simp
    filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem measurableSet_Icc] with r hr hmem
    have hrpos : 0 < r := lt_of_le_of_ne hmem.1 hr.symm
    have hrc : r ∈ Ioc 0 t := ⟨hrpos, hmem.2⟩
    calc
      _ ≤ 1 * CollisionCutoff.gain b (fun v => c r ((JetBarrier.flight r p).1, v)) p.2 :=
        mul_le_mul_of_nonneg_right (attenuation_le_one hmem.2 (fun τ hτ => hν τ ⟨hmem.1.trans hτ.1, hτ.2⟩))
          (gain_nonneg (hcn r hrc) b p.2)
      _ ≤ _ := by
        rw [one_mul]
        exact cutoff_mono hK hα hγ hs hd hrpos (hmem.2.trans htmax) hε η b a _
          (hcm r hrc) (hcn r hrc) (hcU r hrc) p.2
  apply (add_le_add (mul_le_of_le_one_right (density_nonneg hK hs.le hd.le η α γ a p)
    (attenuation_le_one ht.le hν)) hint).trans
  exact JetIntegralSupersolution.cutoff_integral_bound hK hα hγ hs hd ht htmax hε η b a p hUi

/-- Every positive Picard iterate is controlled independently of the supplied
nonnegative loss. The hypotheses describe only measurability and finite
integrals of the actual iteration, not an assumed comparison principle. -/
theorem picard_le {K α γ s d T : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (hT : T ≤ 1) (hε : JetSupersolution.epsilon K s d ≤ 1)
    (η b : ℝ) (a : Bool) (ν : ℕ → ℝ → JetPrototype.Phase → ℝ)
    (hν : ∀ n r, r ∈ Icc 0 T → ∀ p, 0 ≤ ν n r p)
    (hcm : ∀ n r, r ∈ Ioc 0 T → ∀ x : Space,
      Measurable (fun v => picard η K α γ s d b a ν n r (x, v)))
    (hci : ∀ n t, t ∈ Ioc 0 T → ∀ p : JetPrototype.Phase,
      IntervalIntegrable (fun r => attenuation (ν n) r t p * CollisionCutoff.gain b
        (fun v => picard η K α γ s d b a ν n r ((JetBarrier.flight r p).1, v)) p.2) volume 0 t)
    (hUi : ∀ t, t ∈ Ioc 0 T → ∀ p : JetPrototype.Phase,
      IntervalIntegrable (fun r => CollisionCutoff.gain b
        (fun v => JetSupersolution.U η K α γ s d r a ((JetBarrier.flight r p).1, v)) p.2) volume 0 t) :
    ∀ n t, t ∈ Ioc 0 T → ∀ p,
      picard η K α γ s d b a ν n t p ≤ JetSupersolution.U η K α γ s d t a p := by
  intro n
  induction n with
  | zero =>
    intro t ht p
    exact JetSupersolution.nonneg hK hs hd η α γ t a p
  | succ n ih =>
    intro t ht p
    let p₀ := JetBarrier.flight (-t) p
    have hb := alongStep_le hK hα hγ hs hd ht.1 (ht.2.trans hT) hε η b a (ν n)
      (picard η K α γ s d b a ν n) p₀
      (fun r hr => hν n r ⟨hr.1, hr.2.trans ht.2⟩ _)
      (fun r hr => hcm n r ⟨hr.1, hr.2.trans ht.2⟩ _)
      (fun r hr v => picard_nonneg hK hs.le hd.le η α γ b a ν n r hr.1.le _)
      (fun r hr v => ih r ⟨hr.1, hr.2.trans ht.2⟩ _)
      (hci n t ht p₀) (hUi t ht p₀)
    simpa only [picard, step, p₀, JetSupersolution.along, JetFreeTransport.flight_neg] using hb

end BoltzmannNonuniqueness.JetPicardComparison

end

end

section

/-! # Finite time integrals of the cold-envelope gain -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetEnvelopeTimeIntegral

def positiveGain (η K α γ s d b : ℝ) (a : Bool) (p : JetPrototype.Phase) (r : ℝ) : ℝ :=
  CollisionCutoff.gain b (fun v => JetTimeRegularity.positiveU η K α γ s d a
    (r, ((JetBarrier.flight r p).1, v))) p.2

theorem positiveGain_eq {r : ℝ} (hr : 0 ≤ r) (η K α γ s d b : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    positiveGain η K α γ s d b a p r = CollisionCutoff.gain b
      (fun v => JetSupersolution.U η K α γ s d r a ((JetBarrier.flight r p).1, v)) p.2 := by
  unfold positiveGain
  congr 1
  funext v
  exact JetTimeRegularity.positiveU_eq hr _ _ _ _ _ _ _ _

theorem measurable_positiveGain {α γ s : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (η K d b : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    Measurable (positiveGain η K α γ s d b a p) := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  have hU := JetTimeRegularity.measurable_positiveU hα hγ hs η K d a
  have hL : Measurable (fun q : ℝ × (Velocity × Sphere) =>
      JetTimeRegularity.positiveU η K α γ s d a
        (q.1, ((JetBarrier.flight q.1 p).1, scatterLeft p.2 q.2.1 q.2.2))) := by
    apply hU.comp
    unfold JetBarrier.flight scatterLeft normalComponent VelocityWeight.transverse VelocityWeight.axial
    fun_prop
  have hR : Measurable (fun q : ℝ × (Velocity × Sphere) =>
      JetTimeRegularity.positiveU η K α γ s d a
        (q.1, ((JetBarrier.flight q.1 p).1, scatterRight p.2 q.2.1 q.2.2))) := by
    apply hU.comp
    unfold JetBarrier.flight scatterRight normalComponent VelocityWeight.transverse VelocityWeight.axial
    fun_prop
  have hk : Measurable (fun q : ℝ × (Velocity × Sphere) => CollisionCutoff.kernel b p.2 q.2.1 q.2.2) := by
    unfold CollisionCutoff.kernel
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    · unfold collisionKernel normalComponent
      fun_prop
    · exact measurable_const
  exact ((hk.mul hL).mul hR).stronglyMeasurable.integral_prod_right.measurable

theorem gain_integrable {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : JetSupersolution.epsilon K s d ≤ 1) (η b : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    IntervalIntegrable (fun r => CollisionCutoff.gain b
      (fun v => JetSupersolution.U η K α γ s d r a ((JetBarrier.flight r p).1, v)) p.2) volume 0 t := by
  have hb : IntegrableOn (fun _ : ℝ => JetEnvelopeBound.gainAmplitude K α s d p.2) (Ioc 0 t) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hi : IntegrableOn (positiveGain η K α γ s d b a p) (Ioc 0 t) := by
    apply hb.mono' (measurable_positiveGain hα hγ hs η K d b a p).aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_eq_abs, positiveGain_eq hr.1.le]
    rw [abs_of_nonneg (JetPicardComparison.gain_nonneg
      (fun v => JetSupersolution.nonneg hK hs hd η α γ r a ((JetBarrier.flight r p).1, v)) b p.2)]
    exact JetEnvelopeBound.cutoff_gain_bound hK hα hγ hs hd hr.1 (hr.2.trans htmax) hε η b a _ p.2
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr
  apply hi.congr_fun _ measurableSet_Ioc
  intro r hr
  exact positiveGain_eq hr.1.le η K α γ s d b a p

/-- The explicit supersolution integrability condition in the Picard comparison
is discharged. Only regularity of the iterates themselves remains to be supplied
by the local construction. -/
theorem picard_le {K α γ s d T : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (hT : T ≤ 1) (hε : JetSupersolution.epsilon K s d ≤ 1)
    (η b : ℝ) (a : Bool) (ν : ℕ → ℝ → JetPrototype.Phase → ℝ)
    (hν : ∀ n r, r ∈ Icc 0 T → ∀ p, 0 ≤ ν n r p)
    (hcm : ∀ n r, r ∈ Ioc 0 T → ∀ x : Space,
      Measurable (fun v => JetPicardComparison.picard η K α γ s d b a ν n r (x, v)))
    (hci : ∀ n t, t ∈ Ioc 0 T → ∀ p : JetPrototype.Phase,
      IntervalIntegrable (fun r => JetPicardComparison.attenuation (ν n) r t p * CollisionCutoff.gain b
        (fun v => JetPicardComparison.picard η K α γ s d b a ν n r
          ((JetBarrier.flight r p).1, v)) p.2) volume 0 t) :
    ∀ n t, t ∈ Ioc 0 T → ∀ p,
      JetPicardComparison.picard η K α γ s d b a ν n t p ≤ JetSupersolution.U η K α γ s d t a p :=
  JetPicardComparison.picard_le hK hα hγ hs hd hT hε η b a ν hν hcm hci
    (fun _t ht p => gain_integrable hK hα hγ hs hd ht.1 (ht.2.trans hT) hε η b a p)

end BoltzmannNonuniqueness.JetEnvelopeTimeIntegral

end

end

end OAI
