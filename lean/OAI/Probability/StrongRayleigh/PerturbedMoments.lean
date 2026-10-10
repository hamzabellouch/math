import Mathlib

namespace OAI

universe u_1

noncomputable section

open MeasureTheory Filter
open scoped MeasureTheory

namespace Problem336AdditiveD139
namespace PerturbedMoments

lemma abs_square_add_sub_square_le (q r b : ℝ) (hb : 0 ≤ b) (hr : |r| ≤ b) :
    |(q + r) ^ 2 - q ^ 2| ≤ 2 * b * |q| + b ^ 2 := by
  calc
    |(q + r) ^ 2 - q ^ 2| = |2 * q * r + r ^ 2| := by congr 1; ring
    _ ≤ |2 * q * r| + |r ^ 2| := abs_add_le _ _
    _ = 2 * |q| * |r| + |r| ^ 2 := by simp [abs_mul, abs_pow]
    _ ≤ 2 * b * |q| + b ^ 2 := by
      have h₁ := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 * |q|)
      have h₂ := sq_le_sq₀ (abs_nonneg r) hb |>.2 hr
      nlinarith

lemma abs_add_cube_le (q r b : ℝ) (hb : 0 ≤ b) (hr : |r| ≤ b) :
    |q + r| ^ 3 ≤ 4 * (|q| ^ 3 + b ^ 3) := by
  have hsum : |q + r| ≤ |q| + b := (abs_add_le q r).trans (by gcongr)
  have hpow := pow_le_pow_left₀ (abs_nonneg (q + r)) hsum 3
  have haux := mul_nonneg (add_nonneg (abs_nonneg q) hb) (sq_nonneg (|q| - b))
  nlinarith

variable {Ω : Type u_1} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}

theorem integrable_square_add [IsFiniteMeasure μ]
    {Q R : Ω → ℝ} (b : ℝ) (hb : 0 ≤ b) (hQ : Integrable Q μ)
    (hQ₂ : Integrable (fun ω => Q ω ^ 2) μ)
    (hRm : AEStronglyMeasurable R μ) (hR : ∀ᵐ ω ∂μ, |R ω| ≤ b) :
    Integrable (fun ω => (Q ω + R ω) ^ 2) μ := by
  refine (hQ₂.add ((hQ.abs.const_mul (2 * b)).add (integrable_const (b ^ 2)))).mono'
    ((hQ.aestronglyMeasurable.add hRm).pow 2) ?_
  filter_upwards [hR] with ω hω
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Q ω + R ω))]
  have h := abs_square_add_sub_square_le (Q ω) (R ω) b hb hω
  have h' := le_abs_self ((Q ω + R ω) ^ 2 - Q ω ^ 2)
  dsimp
  linarith

theorem integrable_abs_cube_add [IsFiniteMeasure μ]
    {Q R : Ω → ℝ} (b : ℝ) (hb : 0 ≤ b)
    (hQm : AEStronglyMeasurable Q μ)
    (hQ₃ : Integrable (fun ω => |Q ω| ^ 3) μ)
    (hRm : AEStronglyMeasurable R μ) (hR : ∀ᵐ ω ∂μ, |R ω| ≤ b) :
    Integrable (fun ω => |Q ω + R ω| ^ 3) μ := by
  refine ((hQ₃.add (integrable_const (b ^ 3))).const_mul 4).mono'
    (by
      convert (hQm.add hRm).norm.pow 3 using 1) ?_
  filter_upwards [hR] with ω hω
  simpa only [Real.norm_eq_abs, Pi.add_apply, abs_of_nonneg (by positivity : 0 ≤ |Q ω + R ω| ^ 3)]
    using abs_add_cube_le (Q ω) (R ω) b hb hω

theorem abs_condExp_le_affine [IsFiniteMeasure μ]
    (hm : m ≤ m₀) {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (a b : ℝ) (hbound : ∀ᵐ ω ∂μ, |f ω| ≤ a * g ω + b) :
    ∀ᵐ ω ∂μ, |μ[f | m] ω| ≤ a * μ[g | m] ω + b := by
  have habs := abs_condExp_ae_le_condExp_abs (μ := μ) (m := m) f
  have hmono := condExp_mono (m := m) hf.abs
    ((hg.const_mul a).add (integrable_const b)) hbound
  have hadd := condExp_add (hg.const_mul a) (integrable_const b) m
  have hmul := condExp_smul (μ := μ) a g m
  filter_upwards [habs, hmono, hadd, hmul] with ω hω₁ hω₂ hω₃ hω₄
  have hconst : μ[(fun _ : Ω => b) | m] ω = b := by rw [condExp_const hm]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hω₁ hω₂ hω₃ hω₄
  change μ[(fun ω => a * g ω + b) | m] ω =
    μ[(fun ω => a * g ω) | m] ω + μ[(fun _ : Ω => b) | m] ω at hω₃
  change μ[(fun ω => a * g ω) | m] ω = a * μ[g | m] ω at hω₄
  calc
    |μ[f | m] ω| ≤ μ[(fun ω => |f ω|) | m] ω := hω₁
    _ ≤ μ[(fun ω => a * g ω + b) | m] ω := hω₂
    _ = a * μ[g | m] ω + b := by rw [hω₃, hω₄, hconst]

theorem condExp_square_perturbation [IsFiniteMeasure μ]
    (hm : m ≤ m₀) {Q R : Ω → ℝ} (b : ℝ) (hb : 0 ≤ b)
    (hQ : Integrable Q μ) (hQ₂ : Integrable (fun ω => Q ω ^ 2) μ)
    (hD₂ : Integrable (fun ω => (Q ω + R ω) ^ 2) μ)
    (hR : ∀ᵐ ω ∂μ, |R ω| ≤ b) :
    ∀ᵐ ω ∂μ,
      |μ[(fun ω => (Q ω + R ω) ^ 2) | m] ω - μ[(fun ω => Q ω ^ 2) | m] ω| ≤
        2 * b * μ[(fun ω => |Q ω|) | m] ω + b ^ 2 := by
  have hbound := abs_condExp_le_affine hm (hD₂.sub hQ₂) hQ.abs (2 * b) (b ^ 2)
    (hR.mono fun ω hω => abs_square_add_sub_square_le (Q ω) (R ω) b hb hω)
  have hsub := condExp_sub hD₂ hQ₂ m
  filter_upwards [hbound, hsub] with ω hω hω'
  simpa only [Pi.sub_apply, hω'] using hω

theorem condExp_abs_cube_perturbation [IsFiniteMeasure μ]
    (hm : m ≤ m₀) {Q R : Ω → ℝ} (b : ℝ) (hb : 0 ≤ b)
    (hQ₃ : Integrable (fun ω => |Q ω| ^ 3) μ)
    (hD₃ : Integrable (fun ω => |Q ω + R ω| ^ 3) μ)
    (hR : ∀ᵐ ω ∂μ, |R ω| ≤ b) :
    ∀ᵐ ω ∂μ,
      μ[(fun ω => |Q ω + R ω| ^ 3) | m] ω ≤
        4 * (μ[(fun ω => |Q ω| ^ 3) | m] ω + b ^ 3) := by
  have hbound : ∀ᵐ ω ∂μ, |(|Q ω + R ω| ^ 3)| ≤ 4 * |Q ω| ^ 3 + 4 * b ^ 3 := by
    filter_upwards [hR] with ω hω
    rw [abs_of_nonneg (by positivity)]
    nlinarith [abs_add_cube_le (Q ω) (R ω) b hb hω]
  have h := abs_condExp_le_affine hm hD₃ hQ₃ 4 (4 * b ^ 3) hbound
  filter_upwards [h] with ω hω
  exact (le_abs_self _).trans (hω.trans_eq (by ring))

theorem condExp_square_perturbation_error [IsFiniteMeasure μ]
    (hm : m ≤ m₀) {Q R : Ω → ℝ} (b : ℝ) (hb : 0 ≤ b)
    (hQ : Integrable Q μ) (hQ₂ : Integrable (fun ω => Q ω ^ 2) μ)
    (hRm : AEStronglyMeasurable R μ) (hR : ∀ᵐ ω ∂μ, |R ω| ≤ b)
    (v ε : ℝ) (hv : ∀ᵐ ω ∂μ, |μ[(fun ω => Q ω ^ 2) | m] ω - v| ≤ ε) :
    ∀ᵐ ω ∂μ,
      |μ[(fun ω => (Q ω + R ω) ^ 2) | m] ω - v| ≤
        ε + 2 * b * μ[(fun ω => |Q ω|) | m] ω + b ^ 2 := by
  have h := condExp_square_perturbation hm b hb hQ hQ₂
    (integrable_square_add b hb hQ hQ₂ hRm hR) hR
  filter_upwards [h, hv] with ω hω hvω
  have htri := abs_sub_le
    (μ[(fun ω => (Q ω + R ω) ^ 2) | m] ω)
    (μ[(fun ω => Q ω ^ 2) | m] ω) v
  linarith

theorem integral_square_perturbation [IsProbabilityMeasure μ]
    {Q R : Ω → ℝ} (b : ℝ) (hb : 0 ≤ b)
    (hQ : Integrable Q μ) (hQ₂ : Integrable (fun ω => Q ω ^ 2) μ)
    (hRm : AEStronglyMeasurable R μ) (hR : ∀ᵐ ω ∂μ, |R ω| ≤ b) :
    |(∫ ω, (Q ω + R ω) ^ 2 ∂μ) - ∫ ω, Q ω ^ 2 ∂μ| ≤
      2 * b * (∫ ω, |Q ω| ∂μ) + b ^ 2 := by
  have h := condExp_square_perturbation (m := ⊥) bot_le b hb hQ hQ₂
    (integrable_square_add b hb hQ hQ₂ hRm hR) hR
  obtain ⟨ω, hω⟩ := h.exists
  simpa only [condExp_bot] using hω

theorem integral_abs_cube_perturbation [IsProbabilityMeasure μ]
    {Q R : Ω → ℝ} (b : ℝ) (hb : 0 ≤ b)
    (hQm : AEStronglyMeasurable Q μ)
    (hQ₃ : Integrable (fun ω => |Q ω| ^ 3) μ)
    (hRm : AEStronglyMeasurable R μ) (hR : ∀ᵐ ω ∂μ, |R ω| ≤ b) :
    (∫ ω, |Q ω + R ω| ^ 3 ∂μ) ≤ 4 * ((∫ ω, |Q ω| ^ 3 ∂μ) + b ^ 3) := by
  have h := condExp_abs_cube_perturbation (m := ⊥) bot_le b hb hQ₃
    (integrable_abs_cube_add b hb hQm hQ₃ hRm hR) hR
  obtain ⟨ω, hω⟩ := h.exists
  simpa only [condExp_bot] using hω

end PerturbedMoments
end Problem336AdditiveD139

end

end OAI
