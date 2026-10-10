import OAI.MathematicalPhysics.Boltzmann.Branching.DilatedCoreDensity
import OAI.MathematicalPhysics.Boltzmann.Branching.MainCoreScaleWindow
import OAI.MathematicalPhysics.Boltzmann.Branching.TranslatedCoreKernel
import OAI.MathematicalPhysics.Boltzmann.Jets.FreeCoreSharpBound

namespace OAI

section

/-! # The selected main free core and its uniform positive gain bound -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum

def selectedColdKernel (r s₀ η K α γ d₀ : ℝ) (N : ℕ) : Kernel SpaceTime Velocity :=
  mainCoreKernel s₀ η r N (copyColdKernel r s₀ η K α γ d₀)

instance selectedColdKernel_sFinite (r s₀ η K α γ d₀ : ℝ) (N : ℕ) :
    IsSFiniteKernel (selectedColdKernel r s₀ η K α γ d₀ N) := by
  unfold selectedColdKernel
  infer_instance

def selectedFreeKernel (r s₀ η K α γ d₀ q : ℝ) (N : ℕ) : Kernel KineticPhase Velocity :=
  ChartKernel.offAxis (ChartKernel.inputKernel (selectedColdKernel r s₀ η K α γ d₀ N) q)

instance selectedFreeKernel_sFinite (r s₀ η K α γ d₀ q : ℝ) (N : ℕ) :
    IsSFiniteKernel (selectedFreeKernel r s₀ η K α γ d₀ q N) := by
  unfold selectedFreeKernel
  infer_instance

theorem selectedFreeKernel_bound {r s₀ η K α γ d₀ q : ℝ} (hr : 0 < r)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (N : ℕ) (z : KineticPhase) (ht : 0 < z.1.1) :
    selectedFreeKernel r s₀ η K α γ d₀ q N z univ ≤
      ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/z.1.1) := by
  by_cases hv : VelocityWeight.transverse z.2 = 0
  · rw [selectedFreeKernel,ChartKernel.offAxis_axis _ _ hv]
    exact bot_le
  · rw [selectedFreeKernel,ChartKernel.offAxis_apply _ _ hv]
    by_cases hm : ∃ i : Label, z.1 ∈ mainCoreRegion s₀ η r N i
    · obtain ⟨i,hi⟩ := hm
      have he := mainCoreKernel_eq hs₀ hsmax hη hηmax (copyColdKernel r s₀ η K α γ d₀) hi
      have hk := ChartKernel.inputKernel_congr_base (selectedColdKernel r s₀ η K α γ d₀ N)
        (copyColdKernel r s₀ η K α γ d₀ i) he q z.2
      have hb := copyFreeKernel_bound hr hs₀ hsmax hη.le hK hα hγ hd₀ hdmax hq₁ hq₂ i z ht
      rw [copyFreeKernel,ChartKernel.offAxis_apply _ _ hv] at hb
      exact (congrArg (fun μ : Measure Velocity => μ univ) hk).le.trans hb
    · have he := mainCoreKernel_eq_zero s₀ η r N (copyColdKernel r s₀ η K α γ d₀)
        z.1 (by simpa only [not_exists] using hm)
      rw [ChartKernel.inputKernel_mass]
      change normalizedChartGain (mainCoreKernel s₀ η r N _ z.1) q z.2 ≤ _
      rw [he]
      simp only [normalizedChartGain,chartGain,lintegral_zero_measure,mul_zero]
      exact bot_le

def positiveMainKernel (r s₀ η K α γ d₀ q : ℝ) (N : ℕ) : Kernel KineticPhase Velocity :=
  selectedFreeKernel r s₀ η K α γ d₀ q N + selectedFreeKernel r s₀ η K α γ d₀ q N

instance positiveMainKernel_sFinite (r s₀ η K α γ d₀ q : ℝ) (N : ℕ) :
    IsSFiniteKernel (positiveMainKernel r s₀ η K α γ d₀ q N) := by
  unfold positiveMainKernel
  infer_instance

theorem positiveMainKernel_bound {r s₀ η K α γ d₀ q : ℝ} (hr : 0 < r)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (N : ℕ) (z : KineticPhase) (ht : 0 < z.1.1) :
    positiveMainKernel r s₀ η K α γ d₀ q N z univ ≤
      ENNReal.ofReal ((2*JetCoreSheet.growthConstant K α γ q)/z.1.1) := by
  have h := selectedFreeKernel_bound hr hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂ N z ht
  change (selectedFreeKernel r s₀ η K α γ d₀ q N z +
    selectedFreeKernel r s₀ η K α γ d₀ q N z) univ ≤ _
  rw [Measure.add_apply]
  apply (add_le_add h h).trans_eq
  rw [← ENNReal.ofReal_add (div_nonneg (JetCoreSheet.growthConstant_nonneg hK α γ q) ht.le)
    (div_nonneg (JetCoreSheet.growthConstant_nonneg hK α γ q) ht.le)]
  congr 1
  ring

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The selected positive kernel retains the smallest cap scale -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem copyFreeKernel_scale_time_bound {r s₀ η K α γ d₀ q : ℝ} (hr : 0 < r)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (i : Label) (z : KineticPhase) (ht : 0 ≤ z.1.1) :
    copyFreeKernel r s₀ η K α γ d₀ q i z univ ≤
      ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/
        (z.1.1+JetGeometry.jetScale s₀ η i.annulus/r)) := by
  have hs : 0 < JetGeometry.jetScale s₀ η i.annulus := DatumBounds.scale_pos hs₀ _
  have hsle : JetGeometry.jetScale s₀ η i.annulus ≤ 1/8 := by
    have h := JetGeometry.scale_antitone hs₀.le hη (Nat.zero_le (i.annulus+1))
    have hle : DatumBounds.scale s₀ η (i.annulus+1) ≤ s₀ := by
      simpa only [DatumBounds.scale,Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] using h
    exact hle.trans hsmax
  rw [copyFreeKernel_eq]
  exact JetCoreSheet.dilatedFreeKernel_scale_time_bound hr hK hα hγ hs (by positivity)
    (JetEnvelopeGain.thermal_width_le hdmax hs.le hsle) hq₁ hq₂ η i.positive _ ht

theorem selectedFreeKernel_scale_time_bound {r s₀ η K α γ d₀ q : ℝ} (hr : 0 < r)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (N : ℕ) (z : KineticPhase) (ht : 0 ≤ z.1.1) :
    selectedFreeKernel r s₀ η K α γ d₀ q N z univ ≤
      ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/
        (z.1.1+JetGeometry.jetScale s₀ η N/r)) := by
  by_cases hv : VelocityWeight.transverse z.2 = 0
  · rw [selectedFreeKernel,ChartKernel.offAxis_axis _ _ hv]
    exact bot_le
  · rw [selectedFreeKernel,ChartKernel.offAxis_apply _ _ hv]
    by_cases hm : ∃ i, z.1 ∈ mainCoreRegion s₀ η r N i
    · obtain ⟨i,hi⟩ := hm
      have he := mainCoreKernel_eq hs₀ hsmax hη hηmax (copyColdKernel r s₀ η K α γ d₀) hi
      have hk := ChartKernel.inputKernel_congr_base (selectedColdKernel r s₀ η K α γ d₀ N)
        (copyColdKernel r s₀ η K α γ d₀ i) he q z.2
      have hb := copyFreeKernel_scale_time_bound hr hs₀ hsmax hη.le hK hα hγ hd₀ hdmax hq₁ hq₂ i z ht
      rw [copyFreeKernel,ChartKernel.offAxis_apply _ _ hv] at hb
      apply ((congrArg (fun μ : Measure Velocity => μ univ) hk).le.trans hb).trans
      apply ENNReal.ofReal_le_ofReal
      have hs : 0 < JetGeometry.jetScale s₀ η N := DatumBounds.scale_pos hs₀ _
      have hiN : JetGeometry.jetScale s₀ η N ≤ JetGeometry.jetScale s₀ η i.annulus :=
        JetGeometry.scale_antitone hs₀.le hη.le (Nat.add_le_add_right hi.1.le 1)
      exact div_le_div_of_nonneg_left (JetCoreSheet.growthConstant_nonneg hK α γ q)
        (add_pos_of_nonneg_of_pos ht (div_pos hs hr))
        (add_le_add le_rfl (div_le_div_of_nonneg_right hiN hr.le))
    · have he := mainCoreKernel_eq_zero s₀ η r N (copyColdKernel r s₀ η K α γ d₀)
        z.1 (by simpa only [not_exists] using hm)
      rw [ChartKernel.inputKernel_mass]
      change normalizedChartGain (mainCoreKernel s₀ η r N _ z.1) q z.2 ≤ _
      rw [he]
      simp only [normalizedChartGain,chartGain,lintegral_zero_measure,mul_zero]
      exact bot_le

theorem positiveMainKernel_scale_time_bound {r s₀ η K α γ d₀ q : ℝ} (hr : 0 < r)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (N : ℕ) (z : KineticPhase) (ht : 0 ≤ z.1.1) :
    positiveMainKernel r s₀ η K α γ d₀ q N z univ ≤
      ENNReal.ofReal (2*JetCoreSheet.growthConstant K α γ q/
        (z.1.1+JetGeometry.jetScale s₀ η N/r)) := by
  have hb := selectedFreeKernel_scale_time_bound hr hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂ N z ht
  change ((selectedFreeKernel r s₀ η K α γ d₀ q N z)+
    (selectedFreeKernel r s₀ η K α γ d₀ q N z)) univ ≤ _
  rw [Measure.add_apply]
  apply (add_le_add hb hb).trans_eq
  have hs : 0 < JetGeometry.jetScale s₀ η N := DatumBounds.scale_pos hs₀ _
  have hn : 0 ≤ JetCoreSheet.growthConstant K α γ q/(z.1.1+JetGeometry.jetScale s₀ η N/r) :=
    div_nonneg (JetCoreSheet.growthConstant_nonneg hK α γ q)
      (add_nonneg ht (div_nonneg hs.le hr.le))
  rw [← ENNReal.ofReal_add hn hn]
  congr 1
  ring

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A jointly measurable density of the selected main free core -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum

def copyCoreDensity (r s₀ η K α γ d₀ : ℝ) (i : Label) (z : KineticPhase) : ℝ≥0∞ :=
  JetCoreSheet.dilatedCoreDensity r η K α γ (JetGeometry.jetScale s₀ η i.annulus)
    (d₀*JetGeometry.jetScale s₀ η i.annulus^10) i.positive
    ((z.1.1,z.1.2-r⁻¹ • latticeVector i.lattice),z.2)

theorem copyCoreDensity_measurable (r s₀ η K α γ d₀ : ℝ) (i : Label) :
    Measurable (copyCoreDensity r s₀ η K α γ d₀ i) := by
  unfold copyCoreDensity
  exact (JetCoreSheet.dilatedCoreDensity_measurable _ _ _ _ _ _ _ _).comp (by fun_prop)

theorem copyColdKernel_density (r s₀ η K α γ d₀ : ℝ) (i : Label) (x : SpaceTime) :
    copyColdKernel r s₀ η K α γ d₀ i x =
      volume.withDensity (fun v => copyCoreDensity r s₀ η K α γ d₀ i (x,v)) := by
  change JetCoreSheet.dilatedColdKernel r η K α γ (JetGeometry.jetScale s₀ η i.annulus)
    (d₀*JetGeometry.jetScale s₀ η i.annulus^10) i.positive
    (x.1,x.2-r⁻¹ • latticeVector i.lattice) = _
  exact JetCoreSheet.dilatedColdKernel_density _ _ _ _ _ _ _ _ _

def selectedCoreDensity (r s₀ η K α γ d₀ : ℝ) (N : ℕ) (z : KineticPhase) : ℝ≥0∞ := by
  classical
  exact ∑' i : Label, if z.1 ∈ mainCoreRegion s₀ η r N i
    then copyCoreDensity r s₀ η K α γ d₀ i z else 0

theorem selectedCoreDensity_measurable (r s₀ η K α γ d₀ : ℝ) (N : ℕ) :
    Measurable (selectedCoreDensity r s₀ η K α γ d₀ N) := by
  classical
  apply Measurable.tsum
  intro i
  exact (copyCoreDensity_measurable r s₀ η K α γ d₀ i).ite
    ((measurableSet_mainCoreRegion s₀ η r N i).preimage measurable_fst) measurable_const

theorem selectedColdKernel_density (r s₀ η K α γ d₀ : ℝ) (N : ℕ) (x : SpaceTime) :
    selectedColdKernel r s₀ η K α γ d₀ N x =
      volume.withDensity (fun v => selectedCoreDensity r s₀ η K α γ d₀ N (x,v)) := by
  classical
  rw [selectedColdKernel,mainCoreKernel,Kernel.sum_apply]
  have h (i : Label) : Measurable (fun v : Velocity =>
      if x ∈ mainCoreRegion s₀ η r N i then copyCoreDensity r s₀ η K α γ d₀ i (x,v) else 0) := by
    split_ifs
    · exact (copyCoreDensity_measurable r s₀ η K α γ d₀ i).comp
        (measurable_const.prodMk measurable_id)
    · exact measurable_const
  have he (i : Label) :
      (Kernel.piecewise (measurableSet_mainCoreRegion s₀ η r N i)
        (copyColdKernel r s₀ η K α γ d₀ i) 0) x =
      volume.withDensity (fun v => if x ∈ mainCoreRegion s₀ η r N i
        then copyCoreDensity r s₀ η K α γ d₀ i (x,v) else 0) := by
    rw [Kernel.piecewise_apply]
    split_ifs
    · exact copyColdKernel_density r s₀ η K α γ d₀ i x
    · simp
  simp_rw [he]
  rw [← withDensity_tsum h]
  congr 1
  funext v
  exact Pi.tsum_apply (Pi.summable.mpr (fun _ => ENNReal.summable))

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Pointwise identification of the selected free kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.ChartKernel

theorem inputKernel_eq_zero_of_base {X : Type*} [MeasurableSpace X]
    (K : Kernel X Velocity) [IsSFiniteKernel K] {x : X} (hx : K x = 0)
    (q : ℝ) (v : Velocity) : inputKernel K q (x,v) = 0 := by
  change (coordinateKernel K q (x,v)).map _ = 0
  rw [coordinateKernel_apply]
  simp [normalizedMeasure,measure,hx]

end BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem selectedFreeKernel_eq_copy {s₀ η r K α γ d₀ q : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    {i : Label} {z : Published.KineticPhase} (hi : z.1 ∈ mainCoreRegion s₀ η r N i) :
    selectedFreeKernel r s₀ η K α γ d₀ q N z = copyFreeKernel r s₀ η K α γ d₀ q i z := by
  by_cases hv : transverse z.2 = 0
  · rw [selectedFreeKernel,copyFreeKernel,ChartKernel.offAxis_axis _ _ hv,
      ChartKernel.offAxis_axis _ _ hv]
  · rw [selectedFreeKernel,copyFreeKernel,ChartKernel.offAxis_apply _ _ hv,
      ChartKernel.offAxis_apply _ _ hv]
    exact ChartKernel.inputKernel_congr_base _ _
      (mainCoreKernel_eq hs₀ hsmax hη hηmax _ hi) q z.2

theorem selectedFreeKernel_eq_zero {s₀ η r K α γ d₀ q : ℝ} {N : ℕ}
    {z : Published.KineticPhase} (hz : ∀ i, z.1 ∉ mainCoreRegion s₀ η r N i) :
    selectedFreeKernel r s₀ η K α γ d₀ q N z = 0 := by
  by_cases hv : transverse z.2 = 0
  · rw [selectedFreeKernel,ChartKernel.offAxis_axis _ _ hv]
  · rw [selectedFreeKernel,ChartKernel.offAxis_apply _ _ hv]
    exact ChartKernel.inputKernel_eq_zero_of_base _
      (mainCoreKernel_eq_zero s₀ η r N _ z.1 hz) q z.2

theorem selectedFreeKernel_zero_or_copy {s₀ η r K α γ d₀ q : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (z : Published.KineticPhase) :
    selectedFreeKernel r s₀ η K α γ d₀ q N z = 0 ∨
      ∃ i : Label, z.1 ∈ mainCoreRegion s₀ η r N i ∧
        selectedFreeKernel r s₀ η K α γ d₀ q N z = copyFreeKernel r s₀ η K α γ d₀ q i z := by
  by_cases hz : ∃ i, z.1 ∈ mainCoreRegion s₀ η r N i
  · obtain ⟨i,hi⟩ := hz
    exact Or.inr ⟨i,hi,selectedFreeKernel_eq_copy hs₀ hsmax hη hηmax hi⟩
  · exact Or.inl (selectedFreeKernel_eq_zero (not_exists.mp hz))

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
