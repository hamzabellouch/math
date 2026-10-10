import OAI.Probability.SLE.Mass.MassCompensatorVariance
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace OAI

/-! The compensator error at a selected grid endpoint. The endpoint may
depend on the whole path; the maximal bound does not require it to be a
discrete stopping time. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma centeredMassPartialSum_selected_bound
    (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (hD : ∀ i, MemLp (D i) 2 P)
    (hDm : ∀ i, StronglyMeasurable[ℱ (i+1)] (D i))
    (N : ℕ) (J : Ω → ℕ) (hJ : ∀ ω, J ω ≤ N) (ε : ℝ) (hε : 0 < ε) :
    ENNReal.ofReal (ε^2) * P {ω | ε ≤ |centeredMassPartialSum P ℱ D (J ω) ω|} ≤
      ENNReal.ofReal (∫ ω, ∑ i ∈ Finset.range N, D i ω^2 ∂P) := by
  have hs : {ω | ε ≤ |centeredMassPartialSum P ℱ D (J ω) ω|} ⊆
      {ω | ε^2 ≤ (Finset.range (N+1)).sup' Finset.nonempty_range_add_one
        (fun j => centeredMassPartialSum P ℱ D j ω^2)} := by
    intro ω hω
    change ε^2 ≤ _
    apply Finset.le_sup'_of_le (fun j => centeredMassPartialSum P ℱ D j ω^2)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hJ ω)))
    have hh := mul_self_le_mul_self hε.le hω
    simpa only [sq_abs,← pow_two] using hh
  have hb := centeredMassPartialSum_maximal_error P ℱ D hD hDm
    (NNReal.mk (ε^2) (sq_nonneg ε)) N
  have hb' : ENNReal.ofReal (ε^2) * P {ω | ε^2 ≤
      (Finset.range (N+1)).sup' Finset.nonempty_range_add_one
        (fun j => centeredMassPartialSum P ℱ D j ω^2)} ≤
      ENNReal.ofReal (∫ ω, ∑ i ∈ Finset.range N, D i ω^2 ∂P) := by
    simpa only [ENNReal.ofReal_eq_coe_nnreal (sq_nonneg ε),NNReal.coe_mk] using hb
  exact (mul_le_mul_of_nonneg_left (measure_mono hs)
    (show 0 ≤ ENNReal.ofReal (ε^2) from zero_le)).trans hb'

/-- Vanishing expected quadratic increments imply that the centered
compensator vanishes in probability at every bounded selected index. -/
theorem centeredMassPartialSum_selected_tendstoInMeasure
    (ℱ : ℕ → Filtration ℕ mΩ) (D : ℕ → ℕ → Ω → ℝ)
    (hD : ∀ n i, MemLp (D n i) 2 P)
    (hDm : ∀ n i, StronglyMeasurable[ℱ n (i+1)] (D n i))
    (N : ℕ → ℕ) (J : ℕ → Ω → ℕ) (hJ : ∀ n ω, J n ω ≤ N n)
    (hE : Tendsto (fun n => ∫ ω, ∑ i ∈ Finset.range (N n), D n i ω^2 ∂P)
      atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => centeredMassPartialSum P (ℱ n) (D n) (J n ω) ω)
      atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let c : ℝ≥0∞ := ENNReal.ofReal (ε^2)
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hε)).ne'
  have hcT : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hb (n : ℕ) : P {ω | ε ≤ |centeredMassPartialSum P (ℱ n) (D n) (J n ω) ω|} ≤
      c⁻¹*ENNReal.ofReal (∫ ω, ∑ i ∈ Finset.range (N n), D n i ω^2 ∂P) := by
    calc
      _ = c⁻¹*(c*P {ω | ε ≤ |centeredMassPartialSum P (ℱ n) (D n) (J n ω) ω|}) := by
        rw [← mul_assoc,ENNReal.inv_mul_cancel hc0 hcT,one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (centeredMassPartialSum_selected_bound P (ℱ n) (D n) (hD n) (hDm n)
          (N n) (J n) (hJ n) ε hε) (show 0 ≤ c⁻¹ from zero_le)
  have ht : Tendsto (fun n => c⁻¹*ENNReal.ofReal
      (∫ ω, ∑ i ∈ Finset.range (N n), D n i ω^2 ∂P)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero,mul_zero] using
      ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hE)
        (Or.inr (ENNReal.inv_ne_top.mpr hc0))
  simpa only [Pi.zero_apply,sub_zero,Real.norm_eq_abs] using
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => bot_le) hb

end SLEExactGauge

end

end OAI
