import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace InvariantRotation.EndpointIntervalBounds

theorem withDensity_le_smul_of_ae_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {f : Ω → ℝ≥0∞} {C : ℝ≥0∞}
    (hf : ∀ᵐ x ∂μ, f x ≤ C) : μ.withDensity f ≤ C • μ := by
  rw [← withDensity_const]
  exact withDensity_mono hf

theorem measureReal_le_mul_of_le_smul {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} {C : ℝ} (hC : 0 ≤ C)
    (hdom : ν ≤ ENNReal.ofReal C • μ) (A : Set Ω) (hA : μ A ≠ ∞) :
    ν.real A ≤ C * μ.real A := by
  have hb : ν A ≤ ENNReal.ofReal C * μ A := by
    simpa only [Measure.smul_apply, smul_eq_mul] using hdom A
  have hfinite : ENNReal.ofReal C * μ A ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA
  have hreal := ENNReal.toReal_mono hfinite hb
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using hreal

theorem intervalMeasure_lower_tail_le {d : ℝ} (hd : 0 ≤ d) :
    (volume.restrict (Ico (0 : ℝ) 1)).real (Iic d) ≤ d := by
  rw [measureReal_restrict_apply measurableSet_Iic]
  calc
    volume.real (Iic d ∩ Ico 0 1) ≤ volume.real (Icc 0 d) :=
      measureReal_mono (fun x hx => ⟨hx.2.1, hx.1⟩) (by simp)
    _ = d := by rw [Real.volume_real_Icc_of_le hd]; ring

theorem intervalMeasure_upper_tail_le {d : ℝ} (hd : 0 ≤ d) :
    (volume.restrict (Ico (0 : ℝ) 1)).real (Ici (1 - d)) ≤ d := by
  rw [measureReal_restrict_apply measurableSet_Ici]
  calc
    volume.real (Ici (1 - d) ∩ Ico 0 1) ≤ volume.real (Icc (1 - d) 1) :=
      measureReal_mono (fun x hx => ⟨hx.1, hx.2.2.le⟩) (by simp)
    _ = d := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring

theorem lower_endpoint_loss_le {ν : Measure ℝ} {C d : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdom : ν ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    ν.real (Iic d) ≤ C * d := by
  refine (measureReal_le_mul_of_le_smul hC hdom (Iic d) ?_).trans
    (mul_le_mul_of_nonneg_left (intervalMeasure_lower_tail_le hd) hC)
  rw [Measure.restrict_apply measurableSet_Iic]
  exact (measure_mono (show Iic d ∩ Ico (0 : ℝ) 1 ⊆ Ico 0 1 from inter_subset_right)
    |>.trans_lt (by simp)).ne

theorem upper_endpoint_loss_le {ν : Measure ℝ} {C d : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdom : ν ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    ν.real (Ici (1 - d)) ≤ C * d := by
  refine (measureReal_le_mul_of_le_smul hC hdom (Ici (1 - d)) ?_).trans
    (mul_le_mul_of_nonneg_left (intervalMeasure_upper_tail_le hd) hC)
  rw [Measure.restrict_apply measurableSet_Ici]
  exact (measure_mono inter_subset_right |>.trans_lt (by simp)).ne

theorem endpoint_function_lower_loss_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} (hX : Measurable X) {C d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdom : μ.map X ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    μ.real {ω | X ω ≤ d} ≤ C * d := by
  have h := lower_endpoint_loss_le hC hd hdom
  have heq : X ⁻¹' Iic d = {ω | X ω ≤ d} := by ext ω; simp
  simpa only [measureReal_def, Measure.map_apply hX measurableSet_Iic, heq] using h

theorem endpoint_function_upper_loss_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} (hX : Measurable X) {C d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdom : μ.map X ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    μ.real {ω | 1 - d ≤ X ω} ≤ C * d := by
  have h := upper_endpoint_loss_le hC hd hdom
  have heq : X ⁻¹' Ici (1 - d) = {ω | 1 - d ≤ X ω} := by ext ω; simp
  simpa only [measureReal_def, Measure.map_apply hX measurableSet_Ici, heq] using h

theorem endpoint_pair_loss_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    {C d : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdomX : μ.map X ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1))
    (hdomY : μ.map Y ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    μ.real {ω | 1 - d ≤ X ω ∨ Y ω ≤ d} ≤ 2 * C * d := by
  have hXb := endpoint_function_upper_loss_le μ hX hC hd hdomX
  have hYb := endpoint_function_lower_loss_le μ hY hC hd hdomY
  have h := (measureReal_union_le {ω | 1 - d ≤ X ω} {ω | Y ω ≤ d}).trans
    (add_le_add hXb hYb)
  have heq : {ω | 1 - d ≤ X ω} ∪ {ω | Y ω ≤ d} =
      {ω | 1 - d ≤ X ω ∨ Y ω ≤ d} := by ext ω; simp
  rw [heq] at h
  linarith

theorem measureReal_iUnion_le_tsum_budget {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : ι → Set Ω) {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    (hE : ∀ i, μ.real (E i) ≤ b i) :
    μ.real (⋃ i, E i) ≤ ∑' i, b i := by
  have hE' : ∀ i, μ (E i) ≤ ENNReal.ofReal (b i) := by
    intro i
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (E i))]
    exact ENNReal.ofReal_le_ofReal (hE i)
  have hbound : μ (⋃ i, E i) ≤ ENNReal.ofReal (∑' i, b i) := calc
    _ ≤ ∑' i, μ (E i) := measure_iUnion_le E
    _ ≤ ∑' i, ENNReal.ofReal (b i) := ENNReal.tsum_le_tsum hE'
    _ = _ := (ENNReal.ofReal_tsum_of_nonneg hb hs).symm
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa only [measureReal_def, ENNReal.toReal_ofReal (tsum_nonneg hb)] using hreal

theorem countable_endpoint_pair_loss_le {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    {X Y : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {C : ℝ} {d : ι → ℝ} (hC : 0 ≤ C) (hd : ∀ i, 0 ≤ d i) (hs : Summable d)
    (hdomX : ∀ i, μ.map (X i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1))
    (hdomY : ∀ i, μ.map (Y i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    μ.real (⋃ i, {ω | 1 - d i ≤ X i ω ∨ Y i ω ≤ d i}) ≤ 2 * C * ∑' i, d i := by
  have h := measureReal_iUnion_le_tsum_budget μ
    (fun i => {ω | 1 - d i ≤ X i ω ∨ Y i ω ≤ d i})
    (b := fun i => 2 * C * d i) (fun i => mul_nonneg (mul_nonneg (by norm_num) hC) (hd i)) (hs.mul_left (2 * C))
    (fun i => endpoint_pair_loss_le μ (hX i) (hY i) hC (hd i) (hdomX i) (hdomY i))
  simpa only [tsum_mul_left] using h

theorem blocked_future_endpoint_loss_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    {K : ℕ → ℝ} (hK : ∀ s, 0 < K s) (hs : Summable (fun s => 1 / K s))
    {X Y : (s : ℕ) → Fin (m s) → Ω → ℝ}
    (hX : ∀ s i, Measurable (X s i)) (hY : ∀ s i, Measurable (Y s i))
    {C a W : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hW : 0 ≤ W)
    (hdomX : ∀ s i, μ.map (X s i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1))
    (hdomY : ∀ s i, μ.map (Y s i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    μ.real (⋃ s, ⋃ i : Fin (m s),
      {ω | 1 - a * W / ((m s : ℝ) * K s) ≤ X s i ω ∨
        Y s i ω ≤ a * W / ((m s : ℝ) * K s)}) ≤
      (2 * C * a * W) * ∑' s, 1 / K s := by
  let E : ℕ → Set Ω := fun s => ⋃ i : Fin (m s),
    {ω | 1 - a * W / ((m s : ℝ) * K s) ≤ X s i ω ∨
      Y s i ω ≤ a * W / ((m s : ℝ) * K s)}
  have hblock (s : ℕ) : μ.real (E s) ≤ (2 * C * a * W) * (1 / K s) := by
    have hmR : (0 : ℝ) < m s := by exact_mod_cast hm s
    have hd : 0 ≤ a * W / ((m s : ℝ) * K s) :=
      div_nonneg (mul_nonneg ha hW) (mul_nonneg hmR.le (hK s).le)
    calc
      μ.real (E s) ≤ ∑ i : Fin (m s), μ.real
          {ω | 1 - a * W / ((m s : ℝ) * K s) ≤ X s i ω ∨
            Y s i ω ≤ a * W / ((m s : ℝ) * K s)} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : Fin (m s), 2 * C * (a * W / ((m s : ℝ) * K s)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact endpoint_pair_loss_le μ (hX s i) (hY s i) hC hd (hdomX s i) (hdomY s i)
      _ = (2 * C * a * W) * (1 / K s) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have hcoef : 0 ≤ 2 * C * a * W := by positivity
  have h := measureReal_iUnion_le_tsum_budget μ E
    (b := fun s => (2 * C * a * W) * (1 / K s))
    (fun s => mul_nonneg hcoef (one_div_nonneg.mpr (hK s).le))
    (hs.mul_left (2 * C * a * W)) hblock
  simpa only [E, tsum_mul_left] using h

end InvariantRotation.EndpointIntervalBounds

end OAI
