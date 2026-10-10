import OAI.Analysis.LipschitzHilbert.Trees.LineGridPoincare
import OAI.Analysis.LipschitzHilbert.Estimates.VariationPerturbation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! Cell averages of a derivative are boundary differences. This is the
high-frequency half of the manuscript's dyadic comparison. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.FiniteLineGrid

theorem average_deriv_eq (g : FiniteLineGrid) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hd : Continuous (deriv A)) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level)
    {x : ℝ} (hx : x ∈ g.cell level i) :
    g.average g.lineMeasure (deriv A) level x =
      (A (g.origin + g.meshWidth level * (i + 1)) -
        A (g.origin + g.meshWidth level * i)) / g.meshWidth level := by
  have hint : Integrable (deriv A) g.lineMeasure :=
    (hd.continuousOn.integrableOn_Icc :
      IntegrableOn (deriv A) (Icc g.origin (g.origin + g.width)) volume).mono_set Ico_subset_Icc_self
  rw [g.average_eq_cell_mean (deriv A) hint hl hi hx]
  congr 1
  let a := g.origin + g.meshWidth level * i
  let b := g.origin + g.meshWidth level * (i + 1)
  have hab : a ≤ b := by dsimp [a,b]; nlinarith [g.meshWidth_pos level]
  change (∫ y in Ico a b, deriv A y) = A b - A a
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact intervalIntegral.integral_deriv_eq_sub (fun y _ => hA y) (hd.intervalIntegrable a b)

theorem average_deriv_cell_energy (g : FiniteLineGrid) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hd : Continuous (deriv A)) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level) :
    (∫ x in g.cell level i, |g.average g.lineMeasure (deriv A) level x| ^ 2) =
      (g.meshWidth level)⁻¹ *
        (A (g.origin + g.meshWidth level * (i + 1)) -
          A (g.origin + g.meshWidth level * i)) ^ 2 := by
  have heq := setIntegral_congr_fun (μ := volume) (s := g.cell level i) measurableSet_Ico
    (fun x hx => congrArg (fun t : ℝ => |t| ^ 2) (g.average_deriv_eq A hA hd hl hi hx))
  rw [heq, setIntegral_const, smul_eq_mul]
  have hmass : volume.real (g.cell level i) = g.meshWidth level := by
    rw [measureReal_def, cell, Real.volume_Ico]
    have he : g.origin + g.meshWidth level * (i + 1) -
        (g.origin + g.meshWidth level * i) = g.meshWidth level := by ring
    rw [he, ENNReal.toReal_ofReal (g.meshWidth_pos level).le]
  rw [hmass, sq_abs]
  field_simp [(g.meshWidth_pos level).ne']

/-- Each sample is charged by at most two adjacent cells, giving the
exact boundary-sampling reduction used for high-frequency bands. -/
theorem average_deriv_energy (g : FiniteLineGrid) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hd : Continuous (deriv A))
    {level : ℕ} (hl : level ≤ g.depth) :
    (∫ x, |g.average g.lineMeasure (deriv A) level x| ^ 2 ∂g.lineMeasure) ≤
      4 * (g.meshWidth level)⁻¹ * ∑ i : Fin (g.branching ^ level + 1),
        |A (g.origin + g.meshWidth level * i.val)| ^ 2 := by
  let boundary := fun i : ℕ => A (g.origin + g.meshWidth level * i)
  have hcellint (i : Fin (g.branching ^ level)) :
      IntegrableOn (fun x => |g.average g.lineMeasure (deriv A) level x| ^ 2)
        (g.cell level i.val) volume := by
    apply (integrableOn_const (C := |(boundary (i.val + 1) - boundary i.val) /
      g.meshWidth level| ^ 2) (by simp [Real.volume_Ico])).congr_fun _ measurableSet_Ico
    intro x hx
    dsimp only
    rw [g.average_deriv_eq A hA hd hl i.isLt hx]
    simp only [boundary, Nat.cast_add, Nat.cast_one]
  have hpart := integral_iUnion_fintype
    (s := fun i : Fin (g.branching ^ level) => g.cell level i.val)
    (fun _ => measurableSet_Ico) (g.cells_disjoint hl) hcellint
  rw [g.cells_cover_root hl] at hpart
  change (∫ x in g.root, |g.average g.lineMeasure (deriv A) level x| ^ 2) ≤ _
  rw [hpart]
  simp_rw [g.average_deriv_cell_energy A hA hd hl (Fin.isLt _)]
  rw [← Finset.mul_sum]
  have hsum := monotone_partition_square_sum boundary (g.branching ^ level) id monotone_id
  simp only [id_eq, Fin.val_succ, Fin.val_castSucc, Real.norm_eq_abs] at hsum
  have hmul := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (g.meshWidth_pos level).le)
  simpa only [boundary, sq_abs, Nat.cast_add, Nat.cast_one,
    mul_left_comm (g.meshWidth level)⁻¹ 4, mul_assoc] using hmul

end LipschitzHilbert.FiniteLineGrid

end

end OAI
