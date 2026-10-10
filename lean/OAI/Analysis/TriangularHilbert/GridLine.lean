import OAI.Analysis.TriangularHilbert.Quantization

namespace OAI

universe uE

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

def gridLine (D : Finset ℤ) (h : ℝ) {E : Type uE} [AddCommMonoid E] (f : D → E) (x : ℝ) : E :=
  ∑ i : D, (gridCell h i).indicator (fun _ => f i) x

lemma gridLine_eq {D : Finset ℤ} {h : ℝ} (hh : 0 < h) {E : Type uE} [AddCommMonoid E]
    (f : D → E) (x : ℝ) : gridLine D h f x =
      if hi : gridIndex h x ∈ D then f ⟨gridIndex h x,hi⟩ else 0 := by
  classical
  unfold gridLine
  simp_rw [Set.indicator_apply,gridCell_mem_iff hh]
  split_ifs with hi
  · rw [Finset.sum_eq_single (⟨gridIndex h x,hi⟩:D)]
    · simp
    · intro i _ hi'
      have hne : gridIndex h x ≠ (i:ℤ) := by intro he; exact hi' (Subtype.ext he.symm)
      simp only [hne,ite_false]
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    have hne : gridIndex h x ≠ (i:ℤ) := by intro he; exact hi (he ▸ i.property)
    simp only [hne,ite_false]

lemma gridLine_sampled {E : Type uE} [AddCommMonoid E] (f : ℝ → E) {h M : ℝ}
    (hh : 0 < h) (hf : ∀ x, f x ≠ 0 → |x| ≤ M) (x : ℝ) :
    gridLine (sampleIndices h M) h (fun i => f (h*(i:ℤ))) x = f (gridPoint h x) := by
  rw [gridLine_eq hh]
  split_ifs with hi
  · rfl
  · symm
    by_contra hn
    exact hi ((mem_sampleIndices hh M _).mpr (hf _ hn))

lemma integral_gridLine (D : Finset ℤ) (h : ℝ) {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : D → E) (hh : 0 ≤ h) :
    (∫ x : ℝ, gridLine D h f x) = ∑ i, h • f i := by
  have hi (i : D) : Integrable ((gridCell h i).indicator (fun _ : ℝ => f i)) :=
    IntegrableOn.integrable_indicator
      (integrableOn_const (μ := volume) (s := gridCell h i) (C := f i)
        (by rw [volume_gridCell]; finiteness)) measurableSet_Ico
  unfold gridLine
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (show MeasurableSet (gridCell h i) from measurableSet_Ico),setIntegral_const,measureReal_def,volume_gridCell,
    ENNReal.toReal_ofReal hh]

lemma integral_sampled_line {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) {h M : ℝ} (hh : 0 < h) (hf : ∀ x, f x ≠ 0 → |x| ≤ M) :
    (∫ x : ℝ, f (gridPoint h x)) = ∑ i : sampleIndices h M, h • f (h*(i:ℤ)) := by
  have he : (fun x => f (gridPoint h x)) = gridLine (sampleIndices h M) h (fun i => f (h*(i:ℤ))) :=
    funext (fun x => (gridLine_sampled f hh hf x).symm)
  rw [he,integral_gridLine _ _ _ hh.le]
end
end TriangularHilbert
end

end OAI
