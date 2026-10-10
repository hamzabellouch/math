import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterraOffAxisAE
import OAI.MathematicalPhysics.Boltzmann.Branching.OffAxisBoxExhaustion
import OAI.MathematicalPhysics.Boltzmann.Collision.SheetKernelLimits
import OAI.MathematicalPhysics.Boltzmann.Jets.FreeCoreGainKernel
import OAI.MathematicalPhysics.Boltzmann.Jets.JetSupersolutions
import OAI.MathematicalPhysics.Boltzmann.Jets.JetPeriodicDatum

namespace OAI

section

/-! # Transferring normalized sheet regions to the actual free core -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem core_region_bound {K α γ s d t q : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t)
    (η : ℝ) (a : Bool) (x : JetPrototype.Space) (v : Velocity)
    (E : Set ChartKernel.Coordinates) {B : ℝ≥0∞}
    (hB : ChartKernel.normalizedMeasure
      (SheetMeasures.sheetLaw d (JetAxialLaw.law (JetPrototype.sign a) α γ s d t x.2)) q v E ≤ B) :
    ChartKernel.normalizedMeasure (coreKernel η K α γ s d a (t,x)) q v E ≤
      ENNReal.ofReal (amplitude K α γ s t)*B := by
  rw [coreKernel_apply]
  have h := ChartKernel.measure_mono_incoming
    (measure_domination hK hα hγ hs hd ht η a x)
    (fun ξ => ENNReal.ofReal (H q ξ/H q v)) v E
  rw [ChartKernel.measure_smul,Measure.smul_apply,smul_eq_mul] at h
  exact h.trans (mul_le_mul' le_rfl hB)

theorem inputKernel_region {η K α γ s d q : ℝ} (a : Bool)
    (p : ℝ × JetPrototype.Space) (v : Velocity) {E : Set Velocity} (hE : MeasurableSet E) :
    normalizedCoreKernel η K α γ s d q a (p,v) E =
      ChartKernel.normalizedMeasure (coreKernel η K α γ s d a p) q v
        ((fun y => PlaneChart.chart v y.1 y.2.1 y.2.2) ⁻¹' E) := by
  change (ChartKernel.inputMeasure _ _ (p,v)) E = _
  rw [ChartKernel.inputMeasure,Measure.map_apply (ChartKernel.measurable_point v) hE,
    ChartKernel.coordinateKernel_apply]

theorem core_tail_bound {K α γ s d t q : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1/16) (ht : 0 ≤ t)
    (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (a : Bool) (x : JetPrototype.Space)
    {v : Velocity} (hv : transverse v ≠ 0) (N : ℕ) :
    ChartKernel.normalizedMeasure (coreKernel η K α γ s d a (t,x)) q v
      (SheetTightness.tailRegion v N) ≤
      ENNReal.ofReal (amplitude K α γ s t)*
        SheetTightness.tailBound q (2*Real.exp (16*(|JetPrototype.sign a|+α)^2)) N := by
  let := JetAxialLaw.probability (JetPrototype.sign a) α γ s d t x.2
  apply core_region_bound hK hα hγ hs hd ht η a x v
  exact SheetTightness.normalized_tail_bound hq₁ hq₂ hd.le (by linarith) hv
    (JetAxialLaw.moment hα.le hγ.le hs hd hdmax ht (JetPrototype.sign a) x.2) N

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # The free-core gain kernel has the positive-slab mass bound -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

def growthConstant (K α γ q : ℝ) : ℝ :=
  (K * max 1 (α*γ)⁻¹) * JetGaussianProduct.coefficient *
    (SheetTotal.bound q (2*Real.exp (16*(1+α)^2))).toReal

theorem growthConstant_nonneg {K : ℝ} (hK : 0 ≤ K) (α γ q : ℝ) :
    0 ≤ growthConstant K α γ q := by
  have := JetThermalKernel.bound_pos
  unfold growthConstant JetGaussianProduct.coefficient
  positivity

theorem normalizedCoreKernel_time_bound {K α γ s d t q : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1/16)
    (ht : 0 < t) (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (a : Bool)
    (x : JetPrototype.Space) {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedCoreKernel η K α γ s d q a ((t,x),v) univ ≤
      ENNReal.ofReal (growthConstant K α γ q/t) := by
  apply (normalizedCoreKernel_bound hK hα hγ hs hd hdmax ht.le hq₁ hq₂ η a x hv).trans
  have hsign : |JetPrototype.sign a| = 1 := by cases a <;> norm_num [JetPrototype.sign]
  rw [hsign]
  let R := (SheetTotal.bound q (2*Real.exp (16*(1+α)^2))).toReal
  have hR : ENNReal.ofReal R = SheetTotal.bound q (2*Real.exp (16*(1+α)^2)) :=
    ENNReal.ofReal_toReal (SheetTotal.bound_lt_top _ _).ne
  rw [← hR,← ENNReal.ofReal_mul (amplitude_nonneg hK hs ht.le α γ)]
  apply ENNReal.ofReal_le_ofReal
  have hc : 0 ≤ (K*max 1 (α*γ)⁻¹)*JetGaussianProduct.coefficient := by
    have := JetThermalKernel.bound_pos
    unfold JetGaussianProduct.coefficient
    positivity
  calc
    amplitude K α γ s t*R =
        ((K*max 1 (α*γ)⁻¹)*JetGaussianProduct.coefficient)/(s+t)*R := by
          unfold amplitude
          ring
    _ ≤ ((K*max 1 (α*γ)⁻¹)*JetGaussianProduct.coefficient)/t*R :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left hc ht (by linarith)) ENNReal.toReal_nonneg
    _ = growthConstant K α γ q/t := by unfold growthConstant R; ring

theorem offAxisCoreKernel_time_bound {K α γ s d t q : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1/16)
    (ht : 0 < t) (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (a : Bool)
    (x : JetPrototype.Space) (v : Velocity) :
    ChartKernel.offAxis (normalizedCoreKernel η K α γ s d q a) ((t,x),v) univ ≤
      ENNReal.ofReal (growthConstant K α γ q/t) := by
  by_cases hv : transverse v = 0
  · rw [ChartKernel.offAxis_axis _ _ hv]
    exact bot_le
  · rw [ChartKernel.offAxis_apply _ _ hv]
    exact normalizedCoreKernel_time_bound hK hα hγ hs hd hdmax ht hq₁ hq₂ η a x hv

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Large-output and near-axis truncations for the actual free core -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem core_large_output {α q ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ {K γ s d t : ℝ}, 0 ≤ K → 0 < α → 0 < γ →
      0 < s → 0 < d → d ≤ 1/16 → 0 ≤ t → ∀ (η : ℝ) (a : Bool)
      (x : JetPrototype.Space) (v : Velocity), transverse v ≠ 0 → R < ‖v‖ →
      normalizedCoreKernel η K α γ s d q a ((t,x),v) univ ≤
        ENNReal.ofReal (amplitude K α γ s t)*ENNReal.ofReal ε := by
  obtain ⟨R,hR,hb⟩ := LargeOutput.uniform_large_output
    (L := 2*Real.exp (16*(1+α)^2)) hq₁ hq₂ hε
  refine ⟨R,hR,?_⟩
  intro K γ s d t hK hα hγ hs hd hdmax ht η a x v hv hvR
  rw [normalizedCoreKernel,ChartKernel.inputKernel_mass,ChartKernel.normalized_total_eq]
  apply core_region_bound hK hα hγ hs hd ht η a x v
  let hp := JetAxialLaw.probability (JetPrototype.sign a) α γ s d t x.2
  have hm := JetAxialLaw.moment hα.le hγ.le hs hd hdmax ht (JetPrototype.sign a) x.2
  have hsign : |JetPrototype.sign a| = 1 := by cases a <;> norm_num [JetPrototype.sign]
  rw [hsign] at hm
  exact hb d _ hp hd.le (by linarith) hm v hv hvR

theorem core_axis_input {α q δ ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ {K γ s d t : ℝ}, 0 ≤ K → 0 < α → 0 < γ →
      0 < s → 0 < d → d ≤ 1/16 → 0 ≤ t → ∀ (η : ℝ) (a : Bool)
      (x : JetPrototype.Space) (v : Velocity), transverse v ≠ 0 → ‖transverse v‖ ≤ r →
      ChartKernel.normalizedMeasure (coreKernel η K α γ s d a (t,x)) q v
        (AxisInput.away v δ) ≤ ENNReal.ofReal (amplitude K α γ s t)*ENNReal.ofReal ε := by
  obtain ⟨r,hr,hb⟩ := AxisInput.uniform_axis_input
    (L := 2*Real.exp (16*(1+α)^2)) hq₁ hq₂ hδ hε
  refine ⟨r,hr,?_⟩
  intro K γ s d t hK hα hγ hs hd hdmax ht η a x v hv hvr
  apply core_region_bound hK hα hγ hs hd ht η a x v
  let hp := JetAxialLaw.probability (JetPrototype.sign a) α γ s d t x.2
  have hm := JetAxialLaw.moment hα.le hγ.le hs hd hdmax ht (JetPrototype.sign a) x.2
  have hsign : |JetPrototype.sign a| = 1 := by cases a <;> norm_num [JetPrototype.sign]
  rw [hsign] at hm
  exact hb d _ hp hd.le (by linarith) hm v hv hvr

theorem core_axis_mismatch {α q δ ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ {K γ s d t : ℝ}, 0 ≤ K → 0 < α → 0 < γ →
      0 < s → 0 < d → d ≤ 1/16 → 0 ≤ t → ∀ (η : ℝ) (a : Bool)
      (x : JetPrototype.Space) (v : Velocity), transverse v ≠ 0 → ‖transverse v‖ ≤ r →
      ChartKernel.normalizedMeasure (coreKernel η K α γ s d a (t,x)) q v
        (AxisMismatch.incoming v δ ×ˢ univ) ≤
          ENNReal.ofReal (amplitude K α γ s t)*ENNReal.ofReal ε := by
  obtain ⟨r,hr,hb⟩ := AxisMismatch.uniform_axis_mismatch
    (L := 2*Real.exp (16*(1+α)^2)) hq₁ hq₂ hδ hε
  refine ⟨r,hr,?_⟩
  intro K γ s d t hK hα hγ hs hd hdmax ht η a x v hv hvr
  apply core_region_bound hK hα hγ hs hd ht η a x v
  let hp := JetAxialLaw.probability (JetPrototype.sign a) α γ s d t x.2
  have hm := JetAxialLaw.moment hα.le hγ.le hs hd hdmax ht (JetPrototype.sign a) x.2
  have hsign : |JetPrototype.sign a| = 1 := by cases a <;> norm_num [JetPrototype.sign]
  rw [hsign] at hm
  exact hb d _ hp hd.le (by linarith) hm v hv hvr

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Axial interval and small-input estimates for the actual free core -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem core_axial_interval {α q ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (u w : ℝ), 0 < w-u → w-u ≤ δ →
      ∀ {K γ s d t : ℝ}, 0 ≤ K → 0 < α → 0 < γ → 0 < s →
      0 < d → d ≤ 1/16 → 0 ≤ t → ∀ (η : ℝ) (a : Bool)
      (x : JetPrototype.Space) (v : Velocity), transverse v ≠ 0 →
      ChartKernel.normalizedMeasure (coreKernel η K α γ s d a (t,x)) q v
        (AxialModulus.axialRegion v u w) ≤
        ENNReal.ofReal (amplitude K α γ s t)*ENNReal.ofReal ε := by
  obtain ⟨δ,hδ,hb⟩ := AxialModulus.uniform_axial_modulus
    (L := 2*Real.exp (16*(1+α)^2)) hq₁ hq₂ hε
  refine ⟨δ,hδ,?_⟩
  intro u w huw hwδ K γ s d t hK hα hγ hs hd hdmax ht η a x v hv
  apply core_region_bound hK hα hγ hs hd ht η a x v
  let hp := JetAxialLaw.probability (JetPrototype.sign a) α γ s d t x.2
  have hm := JetAxialLaw.moment hα.le hγ.le hs hd hdmax ht (JetPrototype.sign a) x.2
  have hsign : |JetPrototype.sign a| = 1 := by cases a <;> norm_num [JetPrototype.sign]
  rw [hsign] at hm
  exact hb u w huw hwδ d _ hp hd.le (by linarith) hm v hv

theorem core_small_input {α q r ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hr : 0 < r) (hε : 0 < ε) :
    ∃ δ θ : ℝ, 0 < δ ∧ 0 < θ ∧ ∀ {K γ s d t : ℝ}, 0 ≤ K → 0 < α →
      0 < γ → 0 < s → 0 < d → d ≤ 1/16 → d ≤ θ → 0 ≤ t →
      ∀ (η : ℝ) (a : Bool) (x : JetPrototype.Space) (v : Velocity),
      r ≤ ‖transverse v‖ →
      ChartKernel.normalizedMeasure (coreKernel η K α γ s d a (t,x)) q v
        (SmallInputLimit.smallRegion v δ) ≤
        ENNReal.ofReal (amplitude K α γ s t)*ENNReal.ofReal ε := by
  obtain ⟨δ,θ,hδ,hθ,hb⟩ := SmallInputLimit.uniform_small_input
    (L := 2*Real.exp (16*(1+α)^2)) hq₁ hq₂ hr hε
  refine ⟨δ,θ,hδ,hθ,?_⟩
  intro K γ s d t hK hα hγ hs hd hdmax hdθ ht η a x v hv
  apply core_region_bound hK hα hγ hs hd ht η a x v
  let hp := JetAxialLaw.probability (JetPrototype.sign a) α γ s d t x.2
  have hm := JetAxialLaw.moment hα.le hγ.le hs hd hdmax ht (JetPrototype.sign a) x.2
  have hsign : |JetPrototype.sign a| = 1 := by cases a <;> norm_num [JetPrototype.sign]
  rw [hsign] at hm
  exact hb d _ hp hd.le (le_min hdθ (by linarith)) hm v hv

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # The actual free-core kernel in the coordinates of positive iteration -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCoreSheet

def kineticColdKernel (η K α γ s d : ℝ) (a : Bool) : Kernel SpaceTime Velocity :=
  (coreKernel η K α γ s d a).comap
    (fun z => (z.1,JetPeriodicDatum.spatialMap z.2))
    (measurable_fst.prodMk (JetPeriodicDatum.spatialMap_measurePreserving.measurable.comp measurable_snd))

instance kineticColdKernel_sFinite (η K α γ s d : ℝ) (a : Bool) :
    IsSFiniteKernel (kineticColdKernel η K α γ s d a) := by
  unfold kineticColdKernel
  infer_instance

def kineticFreeKernel (η K α γ s d q : ℝ) (a : Bool) : Kernel KineticPhase Velocity :=
  ChartKernel.offAxis (ChartKernel.inputKernel (kineticColdKernel η K α γ s d a) q)

instance kineticFreeKernel_sFinite (η K α γ s d q : ℝ) (a : Bool) :
    IsSFiniteKernel (kineticFreeKernel η K α γ s d q a) := by
  unfold kineticFreeKernel
  infer_instance

theorem kineticColdKernel_apply (η K α γ s d : ℝ) (a : Bool) (z : SpaceTime) :
    kineticColdKernel η K α γ s d a z = volume.withDensity (fun v =>
      ENNReal.ofReal (JetFreeTransport.free η K α γ s d z.1 a
        (JetPeriodicDatum.spatialMap z.2,v))) := by
  change coreKernel η K α γ s d a (z.1,JetPeriodicDatum.spatialMap z.2) = _
  exact coreKernel_apply _ _ _ _ _ _ _ _

theorem input_kineticColdKernel (η K α γ s d q : ℝ) (a : Bool) (z : KineticPhase) :
    ChartKernel.inputKernel (kineticColdKernel η K α γ s d a) q z =
      normalizedCoreKernel η K α γ s d q a ((z.1.1,JetPeriodicDatum.spatialMap z.1.2),z.2) := by
  change (ChartKernel.coordinateKernel _ q z).map _ =
    (ChartKernel.coordinateKernel _ q ((z.1.1,JetPeriodicDatum.spatialMap z.1.2),z.2)).map _
  rw [ChartKernel.coordinateKernel_apply,ChartKernel.coordinateKernel_apply]
  rfl

theorem kineticFreeKernel_bound {K α γ s d q : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1/16)
    (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (a : Bool)
    (z : KineticPhase) (ht : 0 < z.1.1) :
    kineticFreeKernel η K α γ s d q a z univ ≤
      ENNReal.ofReal (growthConstant K α γ q/z.1.1) := by
  by_cases hv : VelocityWeight.transverse z.2 = 0
  · rw [kineticFreeKernel,ChartKernel.offAxis_axis _ _ hv]
    exact bot_le
  · rw [kineticFreeKernel,ChartKernel.offAxis_apply _ _ hv,input_kineticColdKernel]
    exact normalizedCoreKernel_time_bound hK hα hγ hs hd hdmax ht hq₁ hq₂ η a _ hv

theorem iterate_kineticFreeKernel_bound {K α γ s d q a T B : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d)
    (hdmax : d ≤ 1/16) (hq₁ : 1 < q) (hq₂ : q < 2) (ha : 0 < a) (hB : 0 ≤ B)
    (η : ℝ) (sign : Bool) {f : KineticPhase → ℝ≥0∞}
    (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ ENNReal.ofReal B)
    (n : ℕ) (z : KineticPhase) (hz : z.1.1 ∈ Icc a T) :
    PositiveIteration.iterate a (kineticFreeKernel η K α γ s d q sign) f n z ≤
      ENNReal.ofReal (B*(growthConstant K α γ q*Real.log (z.1.1/a))^n) := by
  apply PositiveIteration.iterate_bound ha (growthConstant_nonneg hK α γ q) hB _
    (fun w hw => kineticFreeKernel_bound hK hα hγ hs hd hdmax hq₁ hq₂ η sign w
      (ha.trans_le hw.1)) hf n z hz

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Actual compact thermal support gives a uniform axial speed error -/

noncomputable section

open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.JetFreeTransport

theorem free_axial_speed_error {α γ s d t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t)
    (η K : ℝ) (a : Bool) (x : JetPrototype.Space) (p : Velocity)
    (hf : free η K α γ s d t a (x,p) ≠ 0) :
    |axial p-velocity (JetPrototype.sign a) α γ s t x.2| < d := by
  let z := x.2+(-t)*axial p
  have hthermal : JetThermalLaw.density d (JetPrototype.center α γ s a z) p ≠ 0 := by
    intro hz
    apply hf
    change JetPrototype.spatial η K γ s a
      (x.1+(-t) • transverse p,z) * JetThermalLaw.density d (JetPrototype.center α γ s a z) p = 0
    rw [hz,mul_zero]
  have hn : ‖p-JetPrototype.center α γ s a z‖ < d := by
    exact lt_of_not_ge (fun h => hthermal (JetThermalLaw.density_zero hd _ _ h))
  have hc : |axial p-profile (JetPrototype.sign a) α γ s z| ≤
      ‖p-JetPrototype.center α γ s a z‖ := by
    have hc := PiLp.norm_apply_le (p-JetPrototype.center α γ s a z) (Fin.last 2)
    change |axial (p-JetPrototype.center α γ s a z)| ≤ _ at hc
    rw [PlaneChart.axial_sub,JetPrototype.center,PlaneChart.axial_join] at hc
    exact hc
  have he := thermal_velocity_error (σ := JetPrototype.sign a) (z := x.2)
    (p := axial p) (δ := axial p-profile (JetPrototype.sign a) α γ s z)
    hα hγ hs ht (by dsimp only [z]; rw [neg_mul,← sub_eq_add_neg]; ring)
  exact he.trans_lt (hc.trans_lt hn)

end BoltzmannNonuniqueness.JetFreeTransport

end

end

section

/-! # Endpoint representative invariance for the actual free-core iterates -/

noncomputable section

open MeasureTheory ProbabilityTheory
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCoreSheet

def kineticCoreDensity (η K α γ s d : ℝ) (sign : Bool) (z : KineticPhase) : ℝ≥0∞ :=
  ENNReal.ofReal (JetFreeTransport.free η K α γ s d z.1.1 sign
    (JetPeriodicDatum.spatialMap z.1.2,z.2))

theorem kineticCoreDensity_measurable (η K α γ s d : ℝ) (sign : Bool) :
    Measurable (kineticCoreDensity η K α γ s d sign) := by
  change Measurable (fun z : KineticPhase => ENNReal.ofReal
    (JetFreeTransport.free η K α γ s d z.1.1 sign (JetPeriodicDatum.spatialMap z.1.2,z.2)))
  let f : KineticPhase → (ℝ × JetPrototype.Space) × Velocity :=
    fun z => ((z.1.1,JetPeriodicDatum.spatialMap z.1.2),z.2)
  have hf : Measurable f :=
    (measurable_fst.fst.prodMk
      (JetPeriodicDatum.spatialMap_measurePreserving.measurable.comp measurable_fst.snd)).prodMk
      measurable_snd
  have h := (JetFreeTransport.measurable_uncurried_free η K α γ s d sign).ennreal_ofReal.comp hf
  simpa only [Function.comp_def,f] using h

theorem iterate_kineticFree_congr_ae_at (hcarleman : Published.GPV2009CarlemanInput)
    (η K α γ s d q a t : ℝ) (sign : Bool)
    {f g : KineticPhase → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[((volume : Measure ℝ).prod volume).prod volume] g) (n : ℕ) :
    (fun p : Velocity × Velocity =>
      PositiveIteration.iterate a (kineticFreeKernel η K α γ s d q sign) f (n+1) ((t,p.1),p.2))
      =ᵐ[volume]
    (fun p => PositiveIteration.iterate a (kineticFreeKernel η K α γ s d q sign)
      g (n+1) ((t,p.1),p.2)) :=
  PositiveIteration.iterate_offAxis_congr_ae_at hcarleman a q t _
    (kineticCoreDensity_measurable η K α γ s d sign)
    (kineticColdKernel_apply η K α γ s d sign) hf hg hfg n

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # The actual core has small total gain when its cold speed is axially separated -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem core_restrict_mismatch {α γ s d t δ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t)
    (η K : ℝ) (a : Bool) (x : JetPrototype.Space) (v : Velocity)
    (hgap : δ+d ≤ |axial v-velocity (JetPrototype.sign a) α γ s t x.2|) :
    (coreKernel η K α γ s d a (t,x)).restrict (AxisMismatch.incoming v δ) =
      coreKernel η K α γ s d a (t,x) := by
  rw [coreKernel_apply]
  apply Measure.restrict_eq_self_of_ae_mem
  apply (ae_withDensity_iff (show Measurable (fun p =>
    ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x,p))) from
      ((JetFreeTransport.measurable_free η K α γ s d t a).comp
        (measurable_const.prodMk measurable_id)).ennreal_ofReal)).mpr
  apply ae_of_all
  intro p hp
  have hfp : JetFreeTransport.free η K α γ s d t a (x,p) ≠ 0 := by
    intro hf
    exact hp (by rw [hf,ENNReal.ofReal_zero])
  have he := JetFreeTransport.free_axial_speed_error hα hγ hs hd ht η K a x p hfp
  have htri := abs_sub_le (axial v) (axial p)
    (velocity (JetPrototype.sign a) α γ s t x.2)
  change δ ≤ |axial (v-p)|
  rw [PlaneChart.axial_sub]
  linarith

theorem core_total_eq_mismatch {α γ s d t δ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t)
    (η K q : ℝ) (a : Bool) (x : JetPrototype.Space) (v : Velocity)
    (hgap : δ+d ≤ |axial v-velocity (JetPrototype.sign a) α γ s t x.2|) :
    normalizedCoreKernel η K α γ s d q a ((t,x),v) univ =
      ChartKernel.normalizedMeasure (coreKernel η K α γ s d a (t,x)) q v
        (AxisMismatch.incoming v δ ×ˢ univ) := by
  rw [normalizedCoreKernel,ChartKernel.inputKernel_mass,ChartKernel.normalized_total_eq]
  have h := ChartKernel.normalized_restrict_incoming (coreKernel η K α γ s d a (t,x))
    q v (AxisMismatch.measurableSet_incoming v δ)
  rw [core_restrict_mismatch hα hγ hs hd ht η K a x v hgap] at h
  have he := congrArg (fun μ : Measure ChartKernel.Coordinates => μ univ) h
  simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter] using he

/-- The near-axis estimate controls the whole core kernel,
provided its implicit cold speed stays farther away than the thermal width. -/
theorem core_mass_small_of_speed_gap {α q δ ε : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ {K γ s d t : ℝ}, 0 ≤ K → 0 < α → 0 < γ →
      0 < s → 0 < d → d ≤ 1/16 → 0 ≤ t → ∀ (η : ℝ) (a : Bool)
      (x : JetPrototype.Space) (v : Velocity), transverse v ≠ 0 → ‖transverse v‖ ≤ r →
      δ+d ≤ |axial v-velocity (JetPrototype.sign a) α γ s t x.2| →
      normalizedCoreKernel η K α γ s d q a ((t,x),v) univ ≤
        ENNReal.ofReal (amplitude K α γ s t)*ENNReal.ofReal ε := by
  obtain ⟨r,hr,hb⟩ := core_axis_mismatch (α := α) hq₁ hq₂ hδ hε
  refine ⟨r,hr,?_⟩
  intro K γ s d t hK hα hγ hs hd hdmax ht η a x v hv hvr hgap
  rw [core_total_eq_mismatch hα.le hγ.le hs hd ht η K q a x v hgap]
  exact hb hK hα hγ hs hd hdmax ht η a x v hv hvr

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
