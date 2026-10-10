import OAI.Analysis.LipschitzHilbert.Trees.LineGridPoincare
import OAI.Analysis.LipschitzHilbert.Estimates.MeanOscillation

namespace OAI

/-! Mean oscillation on the actual line cells controls every martingale
jump by the branching factor. This supplies the overshoot bound in the
dyadic stopping proof of John--Nirenberg. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert.FiniteLineGrid

def cellMean (g : FiniteLineGrid) (f : ℝ → ℝ) (level i : ℕ) : ℝ :=
  (g.meshWidth level)⁻¹ * ∫ x in g.cell level i, f x

def HasMeanOscillationBound (g : FiniteLineGrid) (f : ℝ → ℝ) (A : ℝ) : Prop :=
  ∀ level i, level ≤ g.depth → i < g.branching ^ level →
    (∫ x in g.cell level i, |f x - g.cellMean f level i|) ≤ A * g.meshWidth level

instance cellMeasure_finite (g : FiniteLineGrid) (level i : ℕ) :
    IsFiniteMeasure (volume.restrict (g.cell level i)) := ⟨by
  rw [Measure.restrict_apply_univ, cell, Real.volume_Ico]
  exact ENNReal.ofReal_lt_top⟩

theorem cell_mass (g : FiniteLineGrid) (level i : ℕ) :
    (volume.restrict (g.cell level i)).real univ = g.meshWidth level := by
  rw [measureReal_def, Measure.restrict_apply_univ, cell, Real.volume_Ico]
  have heq : g.origin + g.meshWidth level * (i + 1) -
      (g.origin + g.meshWidth level * i) = g.meshWidth level := by ring
  rw [heq, ENNReal.toReal_ofReal (g.meshWidth_pos level).le]

theorem cellMean_eq_integralAverage (g : FiniteLineGrid) (f : ℝ → ℝ) (level i : ℕ) :
    g.cellMean f level i = integralAverage (volume.restrict (g.cell level i)) f := by
  simp only [integralAverage, g.cell_mass, cellMean, smul_eq_mul]

theorem cellMean_sub_constant_le (g : FiniteLineGrid) (f : ℝ → ℝ)
    {level i : ℕ} (hf : IntegrableOn f (g.cell level i)) (c : ℝ) :
    |g.cellMean f level i - c| ≤
      (g.meshWidth level)⁻¹ * ∫ x in g.cell level i, |f x - c| := by
  rw [g.cellMean_eq_integralAverage]
  simpa only [Real.norm_eq_abs, g.cell_mass] using
    norm_average_sub_le (volume.restrict (g.cell level i)) f hf
      (by rw [g.cell_mass]; exact g.meshWidth_pos level) c

theorem cell_subset_parent (g : FiniteLineGrid) {level i : ℕ}
    (hl : level + 1 ≤ g.depth) (hi : i < g.branching ^ (level + 1)) :
    g.cell (level + 1) i ⊆ g.cell level (i / g.branching) := by
  intro x hx
  have hr := g.cell_subset_root (level + 1) hi hx
  have hix := (g.index_eq_iff_mem_cell hl hr i).mpr hx
  have hp := congrArg Fin.val (g.index_parent (by omega : level < g.depth) x)
  change (g.index level x).val = (g.index (level + 1) x).val / g.branching at hp
  rw [hix] at hp
  exact (g.index_eq_iff_mem_cell (by omega) hr (i / g.branching)).mp hp

theorem parent_index_lt (g : FiniteLineGrid) {level i : ℕ}
    (hi : i < g.branching ^ (level + 1)) : i / g.branching < g.branching ^ level := by
  apply (Nat.div_lt_iff_lt_mul g.branching_pos).mpr
  simpa only [pow_succ] using hi

theorem meshWidth_succ (g : FiniteLineGrid) (level : ℕ) :
    g.meshWidth (level + 1) = g.meshWidth level / g.branching := by
  simp only [meshWidth, pow_succ, div_div]

theorem cellMean_parent_jump (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {level i : ℕ} (hl : level + 1 ≤ g.depth) (hi : i < g.branching ^ (level + 1)) :
    |g.cellMean f (level + 1) i - g.cellMean f level (i / g.branching)| ≤
      g.branching * A := by
  have hip := g.parent_index_lt hi
  have hsub := g.cell_subset_parent hl hi
  have hfp : IntegrableOn f (g.cell level (i / g.branching)) :=
    hf.mono_measure (Measure.restrict_mono_set volume (g.cell_subset_root level hip))
  have hfc := hfp.mono_set hsub
  have hnorm : IntegrableOn (fun x => |f x - g.cellMean f level (i / g.branching)|)
      (g.cell level (i / g.branching)) := by
    simpa only [IntegrableOn, Real.norm_eq_abs, Pi.sub_apply] using
      (hfp.sub (integrable_const _)).norm
  have hmono : (∫ x in g.cell (level + 1) i, |f x - g.cellMean f level (i / g.branching)|) ≤
      ∫ x in g.cell level (i / g.branching), |f x - g.cellMean f level (i / g.branching)| :=
    setIntegral_mono_set hnorm (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hsub hx)
  calc
    _ ≤ (g.meshWidth (level + 1))⁻¹ *
        ∫ x in g.cell (level + 1) i, |f x - g.cellMean f level (i / g.branching)| :=
      g.cellMean_sub_constant_le f hfc _
    _ ≤ (g.meshWidth (level + 1))⁻¹ * (A * g.meshWidth level) :=
      mul_le_mul_of_nonneg_left (hmono.trans (hA level (i / g.branching) (by omega) hip))
        (inv_nonneg.mpr (g.meshWidth_pos _).le)
    _ = _ := by rw [g.meshWidth_succ]; field_simp [(g.meshWidth_pos level).ne']

theorem average_eq_cellMean (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level)
    {x : ℝ} (hx : x ∈ g.cell level i) :
    g.average g.lineMeasure f level x = g.cellMean f level i := by
  rw [g.average_eq_cell_mean f hf hl hi hx, cellMean, div_eq_mul_inv, mul_comm]

theorem average_jump_le (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {level : ℕ} (hl : level < g.depth) {x : ℝ} (hx : x ∈ g.root) :
    |g.average g.lineMeasure f (level + 1) x - g.average g.lineMeasure f level x| ≤
      g.branching * A := by
  let i := (g.index (level + 1) x).val
  have hi : i < g.branching ^ (level + 1) := g.index_lt_level (by omega) x
  have hxc : x ∈ g.cell (level + 1) i :=
    (g.index_eq_iff_mem_cell (by omega) hx i).mp rfl
  rw [g.average_eq_cellMean f hf (by omega) hi hxc,
    g.average_eq_cellMean f hf (by omega) (g.parent_index_lt hi)
      (g.cell_subset_parent (by omega) hi hxc)]
  exact g.cellMean_parent_jump f hf hA (by omega) hi

theorem average_jump_le_everywhere (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {level : ℕ} (hl : level < g.depth) (x : ℝ) :
    |g.average g.lineMeasure f (level + 1) x - g.average g.lineMeasure f level x| ≤
      g.branching * A := by
  by_cases hx : x ∈ g.root
  · exact g.average_jump_le f hf hA hl hx
  · have ho : g.origin ∈ g.root := ⟨le_rfl, by linarith [g.width_pos]⟩
    have hidx (n : ℕ) : g.index n x = g.index n g.origin := by
      apply Fin.ext
      simp only [index, rawIndex, ite_eq_right hx, ite_eq_left ho, sub_self,
        zero_div, zero_mul, Nat.floor_zero]
    rw [g.average_constant g.lineMeasure f (level + 1) (hidx _),
      g.average_constant g.lineMeasure f level (hidx _)]
    exact g.average_jump_le f hf hA hl ho

end LipschitzHilbert.FiniteLineGrid

end

end OAI
