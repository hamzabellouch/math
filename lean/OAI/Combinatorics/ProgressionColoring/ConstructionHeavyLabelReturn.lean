import OAI.Combinatorics.ProgressionColoring.ConstructionModel
import OAI.Combinatorics.ProgressionColoring.HeavyLabelReturn

namespace OAI

/-!
# Heavy returns at the selected construction parameters

The occurrence set and multiplicity here use the actual full-label word. The
geometric parameter inequalities are supplied by the independently proved
eventual `GeometryScales` statement.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

variable {k : ℕ}

def labelOccurrences (s : Data k) (hk : 3 ≤ k) (a d : Group s)
    (beta : Label s hk) : Finset ℕ :=
  labelFiber k (fun j => fullLabel s hk (a + j • d)) beta

@[simp] theorem mem_labelOccurrences {s : Data k} {hk : 3 ≤ k} {a d : Group s}
    {beta : Label s hk} {j : ℕ} :
    j ∈ labelOccurrences s hk a d beta ↔ j < k ∧ fullLabel s hk (a + j • d) = beta :=
  mem_labelFiber

open scoped Classical in
/-- The natural occurrence set has exactly the ordinary word multiplicity. -/
theorem card_labelOccurrences (s : Data k) (hk : 3 ≤ k) (a d : Group s)
    (beta : Label s hk) :
    (labelOccurrences s hk a d beta).card =
      (Finset.univ.filter (fun j : Fin k => fullLabelWord s hk (a, d) j = beta)).card := by
  unfold labelOccurrences
  refine (card_labelFiber k (fun j => fullLabel s hk (a + j • d)) beta).trans ?_
  apply congrArg (Finset.card : Finset (Fin k) → ℕ)
  apply Finset.ext
  intro j
  constructor
  · intro hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [fullLabelWord, nsmul_eq_mul] using
      ((@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).mp hi).2
  · intro hi
    apply (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [fullLabelWord, nsmul_eq_mul] using (Finset.mem_filter.mp hi).2

theorem uniformWidth_le_two_mesh_H (s : Data k) (hk : 3 ≤ k) :
    1 / (uniformCount k : ℝ) ≤ 2 * (mesh s hk).H := by
  rw [uniformWidth_eq, mesh_H]
  have hl : (0 : ℝ) < lambda k := by exact_mod_cast lambda_pos k
  have hl1 : (1 : ℝ) ≤ lambda k := by exact_mod_cast Nat.succ_le_of_lt (lambda_pos k)
  have hH : 0 ≤ meshScale k := (meshScale_pos (by omega : 0 < k)).le
  have hd : meshScale k / (lambda k : ℝ) ≤ meshScale k :=
    (div_le_iff₀ hl).2 (by nlinarith)
  linarith

theorem dilation_uniformWidth (s : Data k) (hk : 3 ≤ k) :
    (lambda k : ℝ) * (1 / (uniformCount k : ℝ)) = (mesh s hk).H := by
  rw [uniformWidth_eq, mesh_H]
  have hl : (lambda k : ℝ) ≠ 0 := by exact_mod_cast lambda_ne_zero k
  field_simp [hl]

/-- A heavy label in the selected construction has the proved actual return.
All scalar return inequalities are instantiated from `GeometryScales`. -/
theorem exists_selected_heavy_label_return (s : Data k) (hk : 3 ≤ k)
    (hg : GeometryScales k) (a d : Group s) (beta : Label s hk)
    (hheavy : k < cutoff k * (labelOccurrences s hk a d beta).card) :
    ∃ j h, IsHeavyLabelReturn (mesh s hk) s.q (dimension k) (lambda k)
      (uniformCount k) k (cutoff k) (uniformCount_pos hk) a d beta j h := by
  have hM : 0 < cutoff k := cutoff_pos (by omega)
  have hscale : 2 * cutoff k ≤ k := by exact_mod_cast hg.two_cutoff_le_length
  apply exists_heavy_label_return (mesh s hk) s.pos (uniformCount_pos hk)
    hM hscale a d beta
  · exact hheavy
  · exact uniformWidth_le_two_mesh_H s hk
  · exact dilation_uniformWidth s hk
  · exact hg.affine_box
  · exact hg.return_error

open scoped Classical in
/-- The same endpoint with heaviness stated as the full-label word's literal
`Fin k` multiplicity, matching the outer-coloring family. -/
theorem exists_selected_heavy_label_return_of_word (s : Data k) (hk : 3 ≤ k)
    (hg : GeometryScales k) (a d : Group s) (beta : Label s hk)
    (hheavy : k < cutoff k *
      (Finset.univ.filter (fun j : Fin k => fullLabelWord s hk (a, d) j = beta)).card) :
    ∃ j h, IsHeavyLabelReturn (mesh s hk) s.q (dimension k) (lambda k)
      (uniformCount k) k (cutoff k) (uniformCount_pos hk) a d beta j h := by
  apply exists_selected_heavy_label_return s hk hg a d beta
  simpa only [card_labelOccurrences] using hheavy

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
