import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalTruncatedRepresentation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter

theorem real_smul_double_difference (a b r : ℝ) (u v : ℂ) :
    (a - b) • (r • (u - v)) = a • (r • (u - v)) + b • (r • (v - u)) := by
  simp only [RCLike.real_smul_eq_coe_mul, map_sub]
  ring

theorem bounded_kernel_height_integrable {d : ℕ}
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (w : Ambient d → ℝ) (hwm : Measurable w) (hw : Integrable w ν)
    (g : Ambient d → ℂ) (hgm : Measurable g) (B : ℝ) (hB : 0 ≤ B) (hg : ∀ x, ‖g x‖ ≤ B)
    (k : Ambient d × Ambient d → ℝ) (hkm : Measurable k)
    (C : ℝ) (hk : ∀ q, |k q| ≤ C) :
    Integrable (fun q : Ambient d × Ambient d => w q.1 • (k q • (g q.1 - g q.2))) (ν.prod ν) := by
  have hdom := (hw.norm.mul_prod (integrable_const (μ := ν) (1 : ℝ))).mul_const (2 * C * B)
  have hm : Measurable (fun q : Ambient d × Ambient d => w q.1 • (k q • (g q.1 - g q.2))) := by
    simp_rw [RCLike.real_smul_eq_coe_mul]
    exact (Complex.continuous_ofReal.measurable.comp (hwm.comp measurable_fst)).mul
      ((Complex.continuous_ofReal.measurable.comp hkm).mul
        ((hgm.comp measurable_fst).sub (hgm.comp measurable_snd)))
  apply hdom.mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro q
  have hd : ‖g q.1 - g q.2‖ ≤ 2 * B := by
    have hh := norm_sub_le (g q.1) (g q.2)
    linarith [hg q.1, hg q.2]
  simp only [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal, Real.norm_eq_abs, mul_one]
  calc
    _ ≤ |w q.1| * (C * (2 * B)) := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hd (abs_nonneg (k q))).trans
        (mul_le_mul_of_nonneg_right (hk q) (mul_nonneg (by norm_num) hB))) (abs_nonneg _)
    _ = _ := by ring

theorem finite_symmetric_height_kernel_pairing {d : ℕ}
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (w : Ambient d → ℝ) (hwm : Measurable w) (hw : Integrable w ν)
    (g : Ambient d → ℂ) (hgm : Measurable g) (B : ℝ) (hB : 0 ≤ B) (hg : ∀ x, ‖g x‖ ≤ B)
    (k : Ambient d × Ambient d → ℝ) (hkm : Measurable k)
    (C : ℝ) (hk : ∀ q, |k q| ≤ C) (hsym : ∀ q, k q.swap = k q) :
    Integrable (fun q : Ambient d × Ambient d =>
      (w q.1 - w q.2) • (k q • (g q.1 - g q.2))) (ν.prod ν) ∧
    (1 / 2 : ℝ) • (∫ q : Ambient d × Ambient d,
      (w q.1 - w q.2) • (k q • (g q.1 - g q.2)) ∂ν.prod ν) =
        ∫ x, w x • (∫ y, k (x, y) • (g x - g y) ∂ν) ∂ν := by
  let H := fun q : Ambient d × Ambient d => w q.1 • (k q • (g q.1 - g q.2))
  have hH : Integrable H (ν.prod ν) := bounded_kernel_height_integrable
    ν w hwm hw g hgm B hB hg k hkm C hk
  have hswap : Integrable (fun q : Ambient d × Ambient d => H q.swap) (ν.prod ν) := hH.swap
  have heq : (fun q : Ambient d × Ambient d =>
      (w q.1 - w q.2) • (k q • (g q.1 - g q.2))) = fun q => H q + H q.swap := by
    funext q
    dsimp only [H, Prod.swap]
    rw [show k (q.2, q.1) = k q from hsym q]
    exact real_smul_double_difference (w q.1) (w q.2) (k q) (g q.1) (g q.2)
  rw [heq]
  refine ⟨hH.add hswap, ?_⟩
  rw [integral_add hH hswap, integral_prod_swap]
  have hhalf : (1 / 2 : ℝ) • ((∫ q, H q ∂ν.prod ν) + (∫ q, H q ∂ν.prod ν)) =
      ∫ q, H q ∂ν.prod ν := by
    norm_num [RCLike.real_smul_eq_coe_mul]
    ring
  rw [hhalf, integral_prod H hH]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  exact integral_smul (w x) (fun y => k (x, y) • (g x - g y))

end

end RieszRectifiability

end OAI
