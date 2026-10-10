import OAI.Analysis.LipschitzHilbert.Geometry.TransverseBoxDecay
import OAI.Analysis.LipschitzHilbert.Estimates.TileLatticeEnvelope
import OAI.Analysis.LipschitzHilbert.Estimates.VariationSum

namespace OAI

/-! Summable weights for the fixed-box variation estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

def boxVariationWeight (p : ℤ × ℤ) : ℝ :=
  lineEnvelope 0 1 1 p.1 * lineEnvelope 0 1 1 p.2

theorem boxVariationWeight_pos (p : ℤ × ℤ) : 0 < boxVariationWeight p := by
  unfold boxVariationWeight lineEnvelope
  positivity

theorem boxVariationWeight_sum {ι : Type*} [Fintype ι]
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index) :
    (∑ i, boxVariationWeight (index i)) ≤ (4 * Real.pi) ^ 2 := by
  have h := injective_tile_lattice_overlap index hinj 0 0 1 1 0 0 (by norm_num)
    (by norm_num) (by norm_num : 1 ≤ (1 : ℕ)) (by norm_num : 1 ≤ (1 : ℕ))
  have heq (k : ℤ) : lineEnvelope (0 + 1 * k) 1 1 0 = lineEnvelope 0 1 1 k := by
    simp [lineEnvelope]
  simpa only [heq, boxVariationWeight] using h

theorem ennreal_le_of_positive_real_weight {X : ℝ≥0∞} {c B : ℝ} (hc : 0 < c)
    (h : ENNReal.ofReal c * X ≤ ENNReal.ofReal B) : X ≤ ENNReal.ofReal (B / c) := by
  have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  have hcancel : (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal c = 1 := by
    rw [mul_comm, ENNReal.mul_inv_cancel hc0 ENNReal.ofReal_ne_top]
  calc
    X = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * X) := by rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal B := mul_le_mul_right h _
    _ = ENNReal.ofReal (B / c) := by rw [ENNReal.ofReal_div_of_pos hc, div_eq_mul_inv, mul_comm]

theorem box_variation_decay_bound (p : ℤ × ℤ) {X : ℝ≥0∞} {M : ℝ} (hM : 0 ≤ M)
    (h : ENNReal.ofReal (((1 + |(p.1 : ℝ)|) ^ 2 / 8) ^ 2) * X ≤
      ENNReal.ofReal (M * (((1 + |(p.2 : ℝ)|) ^ 2 / 8) ^ 2)⁻¹)) :
    X ≤ ENNReal.ofReal (4096 * M * boxVariationWeight p ^ 2) := by
  apply (ennreal_le_of_positive_real_weight (by positivity) h).trans
  apply ENNReal.ofReal_le_ofReal
  have h1 := box_decay_le_line_envelope (p.1 : ℝ)
  have h2 := box_decay_le_line_envelope (p.2 : ℝ)
  have hprod := mul_le_mul h1 h2 (by positivity) (by positivity)
  have hm := mul_le_mul_of_nonneg_left hprod hM
  convert hm using 1
  · ring
  · dsimp [boxVariationWeight]
    ring

theorem lintegral_sum_box_variation {Ω ι E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure Ω) (F : ι → ℕ → Ω → E)
    (hF : ∀ i n, Measurable (F i n)) (N : ℕ)
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index) {M : ℝ} (hM : 0 ≤ M)
    (hbox : ∀ i, ENNReal.ofReal (((1 + |((index i).1 : ℝ)|) ^ 2 / 8) ^ 2) *
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F i n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
      ENNReal.ofReal (M * (((1 + |((index i).2 : ℝ)|) ^ 2 / 8) ^ 2)⁻¹)) :
    (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => ∑ i, F i n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
      ENNReal.ofReal ((4 * Real.pi) ^ 4 * (4096 * M)) := by
  have henergy (i : ι) : (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
      (fun n => F i n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
        ENNReal.ofReal (4096 * M) * ENNReal.ofReal (boxVariationWeight (index i) ^ 2) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hM)]
    exact box_variation_decay_bound _ hM (hbox i)
  have h := lintegral_cubicVariation_sum_of_weighted_energy μ F hF N
    (fun i => boxVariationWeight (index i)) (fun i => boxVariationWeight_pos (index i))
    (ENNReal.ofReal (4096 * M)) (boxVariationWeight_sum index hinj) henergy
  convert h using 1
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  ring

end LipschitzHilbert

end

end OAI
