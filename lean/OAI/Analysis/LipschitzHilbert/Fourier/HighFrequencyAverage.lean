import OAI.Analysis.LipschitzHilbert.Trees.LineGridPrimitive
import OAI.Analysis.LipschitzHilbert.Estimates.SeparatedSampling

namespace OAI

/-! The high-frequency cell-average bound from a band-scale primitive. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.FiniteLineGrid

theorem primitive_average_energy (g : FiniteLineGrid) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hd : Continuous (deriv A))
    (hA2 : MemLp A 2 volume) (hd2 : MemLp (deriv A) 2 volume)
    {level : ℕ} (hl : level ≤ g.depth) {δ : ℝ} (hδ : 0 < δ)
    (hδmesh : δ ≤ g.meshWidth level) :
    (∫ x, |g.average g.lineMeasure (deriv A) level x| ^ 2 ∂g.lineMeasure) ≤
      (8 / (g.meshWidth level * δ)) * (∫ x, A x ^ 2) +
        (8 * δ / g.meshWidth level) * ∫ x, deriv A x ^ 2 := by
  simp only [sq_abs]
  let sample := fun i : Fin (g.branching ^ level + 1) =>
    g.origin + g.meshWidth level * i.val
  have hsep (i j : Fin (g.branching ^ level + 1)) (hij : i < j) :
      sample i + δ ≤ sample j := by
    have hn : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (show i.val + 1 ≤ j.val by omega)
    have hm := mul_le_mul_of_nonneg_left hn (g.meshWidth_pos level).le
    dsimp [sample]
    nlinarith
  have hs := separated_sample_sum A hA hA2 hd2 (g.branching ^ level + 1) sample hδ hsep
  have hav := g.average_deriv_energy A hA hd hl
  simp only [sq_abs] at hav
  calc
    _ ≤ 4 * (g.meshWidth level)⁻¹ * ∑ i, A (sample i) ^ 2 := hav
    _ ≤ 4 * (g.meshWidth level)⁻¹ *
        ((2 / δ) * (∫ x, A x ^ 2) + 2 * δ * ∫ x, deriv A x ^ 2) :=
      mul_le_mul_of_nonneg_left hs
        (mul_nonneg (by norm_num) (inv_nonneg.mpr (g.meshWidth_pos level).le))
    _ = _ := by field_simp; ring

/-- Inserting the primitive's band-scale L² estimate yields the small
ratio of band scale to mesh scale. -/
theorem primitive_average_decay (g : FiniteLineGrid) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hd : Continuous (deriv A))
    (hA2 : MemLp A 2 volume) (hd2 : MemLp (deriv A) 2 volume)
    {level : ℕ} (hl : level ≤ g.depth) {δ : ℝ} (hδ : 0 < δ)
    (hδmesh : δ ≤ g.meshWidth level) {C : ℝ}
    (hprimitive : (∫ x, A x ^ 2) ≤ C * δ ^ 2 * ∫ x, deriv A x ^ 2) :
    (∫ x, |g.average g.lineMeasure (deriv A) level x| ^ 2 ∂g.lineMeasure) ≤
      (8 * (C + 1) * δ / g.meshWidth level) * ∫ x, deriv A x ^ 2 := by
  have h := g.primitive_average_energy A hA hd hA2 hd2 hl hδ hδmesh
  have hfactor : 0 ≤ 8 / (g.meshWidth level * δ) :=
    div_nonneg (by norm_num) (mul_pos (g.meshWidth_pos level) hδ).le
  calc
    _ ≤ (8 / (g.meshWidth level * δ)) * (C * δ ^ 2 * ∫ x, deriv A x ^ 2) +
        (8 * δ / g.meshWidth level) * ∫ x, deriv A x ^ 2 :=
      h.trans (add_le_add (mul_le_mul_of_nonneg_left hprimitive hfactor) le_rfl)
    _ = _ := by field_simp

end LipschitzHilbert.FiniteLineGrid

end

end OAI
