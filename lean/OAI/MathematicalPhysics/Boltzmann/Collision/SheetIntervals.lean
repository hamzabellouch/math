import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformGain

namespace OAI

section

/-!
# Summing the normalized sheet kernel

The Gaussian shell estimate yields a finite constant independent of the
transverse width, the axial law, and the output velocity off the axis.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.SheetTotal

def shellTerm (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ 2 * Real.exp (-(3 / 32) * ((n : ℝ) + 1) ^ 2)

theorem shellTerm_nonneg (n : ℕ) : 0 ≤ shellTerm n := by
  unfold shellTerm
  positivity

theorem summable_shellTerm : Summable shellTerm := by
  have hbase : Summable (fun n : ℕ =>
      (n : ℝ) ^ 2 * Real.exp (-(3 / 32) * (n : ℝ) ^ 2)) := by
    apply (Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num : (0 : ℝ) < 3 / 32)).of_nonneg_of_le
    · intro n
      positivity
    · intro n
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Real.exp_le_exp.mpr
      have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        exact_mod_cast (show n ≤ n ^ 2 by simpa only [pow_two] using Nat.le_mul_self n)
      nlinarith
  convert! hbase.comp_injective Nat.succ_injective using 1
  funext n
  simp only [Function.comp_def, Nat.cast_succ]
  rfl

def bound (q L : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal tiltConstant * ENNReal.ofReal (4 * L) * ballBound q 2 +
    ∑' n : ℕ, ENNReal.ofReal (shellConstant q L * shellTerm n)

theorem bound_lt_top (q L : ℝ) : bound q L < ∞ := by
  unfold bound ballBound
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
      (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
  · exact (summable_shellTerm.mul_left (shellConstant q L)).tsum_ofReal_lt_top

theorem cover_by_shells (v : Velocity) :
    (univ : Set Coordinates) ⊆ ballRegion v 2 ∪ ⋃ n : ℕ, shell v ((n : ℝ) + 1) := by
  intro y _
  by_cases hr : radius v y ≤ 2
  · apply Or.inl
    exact le_trans (le_add_of_nonneg_left (norm_nonneg y.1)) hr
  · apply Or.inr
    have hr₂ : 2 < radius v y := lt_of_not_ge hr
    let n := Nat.floor (radius v y / 2)
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    have hn : (n : ℝ) ≤ radius v y / 2 := Nat.floor_le (by linarith)
    have hn' : radius v y / 2 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    constructor <;> linarith

/-- Uniform finiteness and the complete gain bound for an elementary sheet. -/
theorem normalized_total_bound {q d L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) {v : Velocity} (hv : transverse v ≠ 0)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρ : AxialMoment ρ L) :
    normalizedChartGain (sheetLaw d ρ) q v ≤ bound q L := by
  rw [normalized_total_eq]
  calc
    _ ≤ normalizedMeasure (sheetLaw d ρ) q v
        (ballRegion v 2 ∪ ⋃ n : ℕ, shell v ((n : ℝ) + 1)) :=
      measure_mono (cover_by_shells v)
    _ ≤ normalizedMeasure (sheetLaw d ρ) q v (ballRegion v 2) +
        ∑' n : ℕ, normalizedMeasure (sheetLaw d ρ) q v (shell v ((n : ℝ) + 1)) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_le _))
    _ ≤ bound q L := by
      apply add_le_add (normalized_ball_bound hq₁ hq₂ hd hdmax (by norm_num) hv hρ)
      apply ENNReal.tsum_le_tsum
      intro n
      simpa only [shellTerm, mul_assoc] using
        normalized_shell_bound hq₁ hq₂ hd hdmax
          (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) n]) hv hρ

theorem normalized_total_lt_top {q d L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) {v : Velocity} (hv : transverse v ≠ 0)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρ : AxialMoment ρ L) :
    normalizedChartGain (sheetLaw d ρ) q v < ∞ :=
  (normalized_total_bound hq₁ hq₂ hd hdmax hv hρ).trans_lt (bound_lt_top q L)

end BoltzmannNonuniqueness.SheetTotal

end

end

section

/-!
# Probability mixtures and domination by sheets

Elementary sheets are the actual Gaussian/atomic transverse product laws.
The uniform estimate survives probability mixing and measure domination.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.SheetClass

def fiber (h : Velocity → ℝ≥0∞) (v p : Velocity) : ℝ≥0∞ :=
  ∫⁻ zs : ℝ × ℝ, density h v (p, zs) ∂(volume.prod volume)

theorem measurable_fiber {h : Velocity → ℝ≥0∞} (hh : Measurable h) (v : Velocity) :
    Measurable (fiber h v) := (measurable_density hh v).lintegral_prod_right'

theorem gain_eq_lintegral_fiber (c : Measure Velocity) {h : Velocity → ℝ≥0∞}
    (hh : Measurable h) (v : Velocity) :
    chartGain c h v = ∫⁻ p, fiber h v p ∂c := by
  rw [total_eq c hh v, ChartKernel.measure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_prod _ (measurable_density hh v).aemeasurable]
  rfl

theorem gain_bind {ι : Type*} [MeasurableSpace ι] (ν : Measure ι)
    {M : ι → Measure Velocity} (hM : Measurable M)
    {h : Velocity → ℝ≥0∞} (hh : Measurable h) (v : Velocity) :
    chartGain (ν.bind M) h v = ∫⁻ i, chartGain (M i) h v ∂ν := by
  rw [gain_eq_lintegral_fiber _ hh v,
    Measure.lintegral_bind hM.aemeasurable (measurable_fiber hh v).aemeasurable]
  simp_rw [← gain_eq_lintegral_fiber _ hh v]

/-- The elementary class allows both zero transverse width and arbitrary axial atoms. -/
def IsElementary (L : ℝ) (c : Measure Velocity) : Prop :=
  ∃ (d : ℝ) (ρ : Measure ℝ), 0 ≤ d ∧ d ≤ 1 / 8 ∧ IsProbabilityMeasure ρ ∧
    AxialMoment ρ L ∧ c = sheetLaw d ρ

theorem elementary_bound {L q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    {c : Measure Velocity} (hc : IsElementary L c)
    {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain c q v ≤ SheetTotal.bound q L := by
  obtain ⟨d, ρ, hd, hdmax, hprob, hρ, rfl⟩ := hc
  exact SheetTotal.normalized_total_bound hq₁ hq₂ hd hdmax hv hρ

theorem mixture_bound {ι : Type*} [MeasurableSpace ι] {ν : Measure ι}
    [IsProbabilityMeasure ν] {M : ι → Measure Velocity} (hM : Measurable M)
    {q L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hc : ∀ᵐ i ∂ν, IsElementary L (M i)) {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain (ν.bind M) q v ≤ SheetTotal.bound q L := by
  unfold normalizedChartGain
  rw [gain_bind ν hM ((measurable_H q).div_const _ |>.ennreal_ofReal) v]
  calc
    _ ≤ ∫⁻ _ : ι, SheetTotal.bound q L ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hc] with i hi
      exact elementary_bound hq₁ hq₂ hi hv
    _ = _ := by simp

theorem domination_bound {ι : Type*} [MeasurableSpace ι] {ν : Measure ι}
    [IsProbabilityMeasure ν] {M : ι → Measure Velocity} (hM : Measurable M)
    {q L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hc : ∀ᵐ i ∂ν, IsElementary L (M i)) {v : Velocity} (hv : transverse v ≠ 0)
    {c : Measure Velocity} {A : ℝ≥0∞} (hdom : c ≤ A • ν.bind M) :
    normalizedChartGain c q v ≤ A * SheetTotal.bound q L := by
  apply (chartGain_mono_measure hdom _ v).trans
  rw [chartGain_smul_measure]
  exact mul_le_mul' le_rfl (mixture_bound hM hq₁ hq₂ hc hv)

end BoltzmannNonuniqueness.SheetClass

end

end

section

/-!
# Transfer of the sheet estimate to the original gain

The only external hypothesis is the precisely stated published Carleman
identity. The sheet estimate itself has been proved from the geometric
slice and Gaussian-tail bounds.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.SheetClass

namespace BoltzmannNonuniqueness.SheetApplication

theorem gain_const_mul_right (c : Measure Velocity) (h : Velocity → ℝ≥0∞)
    (v : Velocity) {a : ℝ≥0∞} (ha : a ≠ ∞) :
    chartGain c (fun ξ => a * h ξ) v = a * chartGain c h v := by
  unfold chartGain
  simp_rw [lintegral_const_mul' a _ ha]
  have he : ∀ p : Velocity,
      ENNReal.ofReal (‖PlaneChart.normal v p‖⁻¹) *
          (a * ∫⁻ z : ℝ, ∫⁻ s : ℝ, h (PlaneChart.chart v p z s)) =
        a * (ENNReal.ofReal (‖PlaneChart.normal v p‖⁻¹) *
          ∫⁻ z : ℝ, ∫⁻ s : ℝ, h (PlaneChart.chart v p z s)) := by
    intro p
    ac_rfl
  simp_rw [he]
  rw [lintegral_const_mul' a _ ha]
  ac_rfl

theorem gain_H_eq (c : Measure Velocity) (q : ℝ) (v : Velocity) :
    chartGain c (fun ξ => ENNReal.ofReal (H q ξ)) v =
      ENNReal.ofReal (H q v) * normalizedChartGain c q v := by
  have he : (fun ξ => ENNReal.ofReal (H q ξ)) =
      (fun ξ => ENNReal.ofReal (H q v) * ENNReal.ofReal (H q ξ / H q v)) := by
    funext ξ
    rw [← ENNReal.ofReal_mul (H_nonneg q v)]
    congr 1
    field_simp [(H_pos q v).ne']
  rw [he, gain_const_mul_right c _ v ENNReal.ofReal_ne_top]
  rfl

theorem ae_transverse_ne_zero : ∀ᵐ v : Velocity ∂volume, transverse v ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  have he : {v : Velocity | transverse v = 0} =
      split ⁻¹' ((univ : Set ℝ) ×ˢ ({0} : Set Transverse)) := by
    ext v
    simp only [mem_preimage, split_apply, mem_prod, mem_univ, mem_singleton_iff, true_and]
    rfl
  rw [he, split_measurePreserving.measure_preimage
    (MeasurableSet.univ.prod (measurableSet_singleton 0)).nullMeasurableSet]
  rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- The original nonnegative hard-sphere gain obeys the sheet domination bound,
conditionally only on the published Carleman identity. -/
theorem nonnegativeGain_sheet_bound
    (hcarleman : Published.GPV2009CarlemanInput)
    {ι : Type*} [MeasurableSpace ι] {ν : Measure ι} [IsProbabilityMeasure ν]
    {M : ι → Measure Velocity} (hM : Measurable M)
    {q L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hc : ∀ᵐ i ∂ν, IsElementary L (M i))
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) {A : ℝ≥0∞}
    (hdom : volume.withDensity f ≤ A • ν.bind M) :
    ∀ᵐ v : Velocity ∂volume,
      nonnegativeGain f (fun ξ => ENNReal.ofReal (H q ξ)) v ≤
        ENNReal.ofReal (H q v) * (A * SheetTotal.bound q L) := by
  apply nonnegativeGain_le_of_chartGain hcarleman hf (measurable_H q |>.ennreal_ofReal)
  filter_upwards [ae_transverse_ne_zero] with v hv
  rw [gain_H_eq]
  exact mul_le_mul' le_rfl (domination_bound hM hq₁ hq₂ hc hv hdom)

end BoltzmannNonuniqueness.SheetApplication

end

end

section

/-!
# Uniform removal of the kernel's velocity tails

The bound and its limit do not depend on the elementary sheet or the
outgoing velocity. They give the first tightness assertion in Section 3.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain
open BoltzmannNonuniqueness.SheetTotal

namespace BoltzmannNonuniqueness.SheetTightness

def tailRegion (v : Velocity) (N : ℕ) : Set Coordinates :=
  {y | 2 * ((N : ℝ) + 1) < radius v y}

def tailBound (q L : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (shellConstant q L * shellTerm (k + N))

theorem tendsto_tailBound (q L : ℝ) : Tendsto (tailBound q L) atTop (𝓝 0) :=
  ENNReal.tendsto_sum_nat_add _
    (summable_shellTerm.mul_left (shellConstant q L)).tsum_ofReal_ne_top

theorem measurableSet_tailRegion (v : Velocity) (N : ℕ) :
    MeasurableSet (tailRegion v N) :=
  measurableSet_lt measurable_const (measurable_radius v)

theorem cover_tail (v : Velocity) (N : ℕ) :
    tailRegion v N ⊆ ⋃ k : ℕ, shell v (((k + N : ℕ) : ℝ) + 1) := by
  intro y hy
  have hr : 2 < radius v y := by
    have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    change 2 * ((N : ℝ) + 1) < radius v y at hy
    linarith
  let n := Nat.floor (radius v y / 2)
  have hn₀ : N ≤ n := (Nat.le_floor_iff (by linarith : 0 ≤ radius v y / 2)).mpr (by
    change 2 * ((N : ℝ) + 1) < radius v y at hy
    linarith)
  have hn : (n : ℝ) ≤ radius v y / 2 := Nat.floor_le (by linarith)
  have hn' : radius v y / 2 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  apply mem_iUnion.mpr
  refine ⟨n - N, ?_⟩
  rw [Nat.sub_add_cancel hn₀]
  constructor <;> linarith

theorem normalized_tail_bound {q d L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) {v : Velocity} (hv : transverse v ≠ 0)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρ : AxialMoment ρ L) (N : ℕ) :
    normalizedMeasure (sheetLaw d ρ) q v (tailRegion v N) ≤ tailBound q L N := by
  apply (measure_mono (cover_tail v N)).trans
  apply (measure_iUnion_le _).trans
  apply ENNReal.tsum_le_tsum
  intro k
  simpa only [shellTerm, mul_assoc] using normalized_shell_bound hq₁ hq₂ hd hdmax
    (show (1 : ℝ) ≤ ((k + N : ℕ) : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) (k + N)])
    hv hρ

/-- A single truncation works for every width, axial law and off-axis output. -/
theorem uniform_tail {q L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (d : ℝ) (ρ : Measure ℝ) (_ : IsProbabilityMeasure ρ)
      (_ : 0 ≤ d) (_ : d ≤ 1 / 8) (_ : AxialMoment ρ L)
      (v : Velocity) (_ : transverse v ≠ 0),
      normalizedMeasure (sheetLaw d ρ) q v (tailRegion v n) ≤ ε := by
  have he : ∀ᶠ n in atTop, tailBound q L n < ε :=
    (tendsto_tailBound q L).eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, fun n hn d ρ hprob hd hdmax hρ v hv => ?_⟩
  exact (normalized_tail_bound hq₁ hq₂ hd hdmax hv hρ n).trans (hN n hn).le

end BoltzmannNonuniqueness.SheetTightness

end

end

section

/-!
# Axial interval bounds for the full sheet kernel

The chart coordinate is shifted by the outgoing axial velocity. The interval
restriction below is therefore exactly a restriction on the incoming axial
velocity, and its bound is uniform over all axial probability laws.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.SheetIntervals

def intervalRegion (v : Velocity) (R a b : ℝ) : Set Coordinates :=
  ballRegion v R ∩ {y | y.2.1 ∈ Ioc (a - axial v) (b - axial v)}

theorem mem_intervalRegion (v : Velocity) (R a b : ℝ) (y : Coordinates) :
    y ∈ intervalRegion v R a b ↔
      ‖PlaneChart.chart v y.1 y.2.1 y.2.2 - v‖ ≤ R ∧
        axial (PlaneChart.chart v y.1 y.2.1 y.2.2) ∈ Ioc a b := by
  simp only [intervalRegion, ballRegion, mem_inter_iff, mem_ofPred_eq, mem_Ioc,
    PlaneChart.axial_chart]
  constructor <;> rintro ⟨hR, ha, hb⟩ <;> exact ⟨hR, by linarith, by linarith⟩

theorem measurableSet_intervalRegion (v : Velocity) (R a b : ℝ) :
    MeasurableSet (intervalRegion v R a b) :=
  (measurableSet_ballRegion v R).inter
    (measurableSet_Ioc.preimage (measurable_fst.comp measurable_snd))

def intervalFiber (q : ℝ) (v p : Velocity) (R a b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖PlaneChart.normal v p‖⁻¹) *
    ∫⁻ z in Ioc (a - axial v) (b - axial v), ∫⁻ s : ℝ,
      if ‖PlaneChart.chart v p z s - v‖ ≤ R then
        weightRatio q v (PlaneChart.chart v p z s) else 0

theorem intervalFiber_le_slice {R : ℝ} (hR : 0 ≤ R) (q : ℝ)
    (v : Velocity) (p : Transverse × ℝ) (a b : ℝ) :
    intervalFiber q v (SheetMeasures.join p) R a b ≤
      normalizedBallSlice q (transverse v) (axial v) p.1 p.2 R
        (a - axial v) (b - axial v) := by
  classical
  by_cases hp : RegularTransverse (transverse v) p.1
  · have hw : 0 < transverseWeight q (transverse v) := transverseWeight_pos q _
    have hcoef : ENNReal.ofReal (‖transverse v - p.1‖⁻¹) *
        ENNReal.ofReal ((transverseWeight q (transverse v))⁻¹) =
      ENNReal.ofReal (1 / (transverseWeight q (transverse v) * ‖transverse v - p.1‖)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp only [one_div, mul_inv_rev]
    have hpoint : ∀ z s : ℝ,
        (if ‖PlaneChart.chart v (SheetMeasures.join p) z s - v‖ ≤ R then
          weightRatio q v (PlaneChart.chart v (SheetMeasures.join p) z s) else 0) =
        ENNReal.ofReal ((transverseWeight q (transverse v))⁻¹) *
          (ballLineRegion (direction (transverse v - p.1)) (transverse v)
            (sliceOffset (transverse v) p.1 - (axial v - p.2) / ‖transverse v - p.1‖ * z) z R).indicator
          (fun s => ENNReal.ofReal (TransverseLine.lineWeight q (direction (transverse v - p.1))
            (sliceOffset (transverse v) p.1 - (axial v - p.2) / ‖transverse v - p.1‖ * z) s)) s := by
      intro z s
      by_cases hm : s ∈ ballLineRegion (direction (transverse v - p.1)) (transverse v)
          (sliceOffset (transverse v) p.1 - (axial v - p.2) / ‖transverse v - p.1‖ * z) z R
      · have hc := (chart_ball_join hR v p z s).mpr hm
        rw [ite_eq_left hc, indicator_of_mem hm]
        unfold weightRatio
        rw [chart_weight_join, W_eq_transverseWeight, div_eq_mul_inv, mul_comm,
          ENNReal.ofReal_mul (inv_nonneg.mpr hw.le)]
      · have hc := mt (chart_ball_join hR v p z s).mp hm
        simp only [ite_eq_right hc, indicator_of_notMem hm, mul_zero]
    have hm : ∀ z : ℝ, MeasurableSet (ballLineRegion (direction (transverse v - p.1))
        (transverse v) (sliceOffset (transverse v) p.1 -
          (axial v - p.2) / ‖transverse v - p.1‖ * z) z R) := by
      intro z
      unfold ballLineRegion TransverseLine.line
      apply measurableSet_le <;> fun_prop
    unfold intervalFiber
    simp_rw [normal_join, hpoint, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_indicator (hm _)]
    rw [← mul_assoc, hcoef]
    rw [normalizedBallSlice, ite_eq_left hp]
    rfl
  · rw [normalizedBallSlice, ite_eq_right hp]
    exact le_top

theorem interval_gain_eq (c : Measure Velocity) (q : ℝ) (v : Velocity) (R a b : ℝ) :
    chartRegionGain c (weightRatio q v) v (intervalRegion v R a b) =
      2 * ∫⁻ p, intervalFiber q v p R a b ∂c := by
  classical
  unfold chartRegionGain intervalFiber
  congr 1
  apply lintegral_congr
  intro p
  congr 1
  rw [← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ Ioc (a - axial v) (b - axial v)
  · rw [indicator_of_mem hz]
    rcases hz with ⟨hza, hzb⟩
    apply lintegral_congr
    intro s
    by_cases hb : ‖PlaneChart.chart v p z s - v‖ ≤ R
    · simp [intervalRegion, ballRegion, indicator, hza, hzb, hb]
    · simp [intervalRegion, ballRegion, indicator, hb]
  · rw [indicator_of_notMem hz]
    have hz' : ¬(a - axial v < z ∧ z ≤ b - axial v) := hz
    simp [intervalRegion, indicator, hz']

def intervalBound (q R ell : ℝ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal (geometricConstant q * (R * ell + R ^ (q - 1) * ell ^ (2 - q)))

theorem weight_interval_bound {q d R a b : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hR : 0 < R) (hab : a < b) {v : Velocity} (hv : transverse v ≠ 0)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    chartRegionGain (sheetLaw d ρ) (weightRatio q v) v (intervalRegion v R a b) ≤
      intervalBound q R (b - a) := by
  have hs : (∫⁻ p, normalizedBallSlice q (transverse v) (axial v) p.1 p.2 R
      (a - axial v) (b - axial v) ∂(transverseLaw d).prod ρ) ≤
        ENNReal.ofReal (geometricConstant q *
          (R * (b - a) + R ^ (q - 1) * (b - a) ^ (2 - q))) := by
    have he : b - axial v - (a - axial v) = b - a := by ring
    rw [← he]
    apply geometric_interval_of_kernel_bound hq₁ hq₂ (by linarith) hR hv
    · obtain rfl | hdpos := hd.eq_or_lt
      · simpa only [transverseLaw, ite_true] using ae_regularTransverse_atom hv
      · simpa only [transverseLaw, ite_eq_right hdpos.ne'] using ae_regularTransverse_gaussian hv d
    · obtain rfl | hdpos := hd.eq_or_lt
      · simpa only [transverseLaw, ite_true] using atom_extendedKernel_lintegral_le q hv
      · simpa only [transverseLaw, ite_eq_right hdpos.ne'] using
          gaussian_extendedKernel_lintegral_le hq₁ hq₂ hdpos hv
  rw [interval_gain_eq, sheetLaw, lintegral_map_equiv]
  exact mul_le_mul' le_rfl ((lintegral_mono (fun p => intervalFiber_le_slice hR.le q v p a b)).trans hs)

theorem weight_interval_measure_bound {q d R a b : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hR : 0 < R) (hab : a < b) {v : Velocity} (hv : transverse v ≠ 0)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    ChartKernel.measure (sheetLaw d ρ) (weightRatio q v) v (intervalRegion v R a b) ≤
      intervalBound q R (b - a) := by
  rw [← region_eq_measure _ (measurable_weightRatio q v) v (measurableSet_intervalRegion v R a b)]
  exact weight_interval_bound hq₁ hq₂ hd hR hab hv ρ

/-- The axial interval bound includes the complete ratio `H(ξ)/H(v)`. -/
theorem normalized_interval_bound {q d R L a b : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 0 < R) (hab : a < b)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (intervalRegion v R a b) ≤
      ENNReal.ofReal tiltConstant * ENNReal.ofReal (4 * L) * intervalBound q R (b - a) := by
  have h := normalized_restriction_le (sheetLaw d ρ) q v
    (measurableSet_intervalRegion v R a b) (measurableSet_intervalRegion v R a b)
    (Subset.refl _) (B := 1) (by norm_num)
    (fun _ _ => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  simp only [mul_one] at h
  have ht := (measure_mono_incoming (tiltedSheet_le_probability hd hdmax hρ)
    (weightRatio q v) v) (intervalRegion v R a b)
  rw [measure_smul, Measure.smul_apply, smul_eq_mul] at ht
  have hb := ht.trans (mul_le_mul' le_rfl (weight_interval_measure_bound hq₁ hq₂
    (by positivity : 0 ≤ 2 * d) hR hab hv (axialProbability ρ hρ)))
  exact h.trans ((mul_le_mul' le_rfl hb).trans_eq (mul_assoc _ _ _).symm)

theorem intervalBound_mono {q R ell₁ ell₂ : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hR : 0 ≤ R)
    (hell₁ : 0 ≤ ell₁) (hell : ell₁ ≤ ell₂) :
    intervalBound q R ell₁ ≤ intervalBound q R ell₂ := by
  unfold intervalBound
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (geometricConstant_pos hq₁ hq₂).le
  exact add_le_add (mul_le_mul_of_nonneg_left hell hR)
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hell₁ hell (by linarith))
      (Real.rpow_nonneg hR _))

theorem intervalBound_tendsto_zero {q : ℝ} (hq : q < 2) (R : ℝ) :
    Filter.Tendsto (intervalBound q R) (nhds 0) (nhds 0) := by
  have hp := Real.continuous_rpow_const (show 0 ≤ 2 - q by linarith)
  have hc : Continuous (fun ell : ℝ => geometricConstant q *
      (R * ell + R ^ (q - 1) * ell ^ (2 - q))) := by fun_prop
  have hz : geometricConstant q * (R * 0 + R ^ (q - 1) * (0 : ℝ) ^ (2 - q)) = 0 := by
    rw [Real.zero_rpow (by linarith : 2 - q ≠ 0)]
    ring
  have h := (ENNReal.continuous_ofReal.comp hc).tendsto 0
  simp only [Function.comp_apply] at h
  rw [hz, ENNReal.ofReal_zero] at h
  change Filter.Tendsto (fun ell : ℝ => 2 * ENNReal.ofReal (geometricConstant q *
    (R * ell + R ^ (q - 1) * ell ^ (2 - q)))) (nhds 0) (nhds 0)
  simpa only [mul_zero, Function.comp_apply] using
    (ENNReal.Tendsto.const_mul (a := 2) h (Or.inr (by norm_num)))

end BoltzmannNonuniqueness.SheetIntervals

end

end

end OAI
