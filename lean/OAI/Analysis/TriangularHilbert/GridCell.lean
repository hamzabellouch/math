import OAI.Analysis.TriangularHilbert.HardScalar

namespace OAI

universe uE uF

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

def gridCell (h : ℝ) (i : ℤ) : Set ℝ := Set.Ico (h*i) (h*(i+1))
def gridIndex (h x : ℝ) : ℤ := ⌊x/h⌋
def gridPoint (h x : ℝ) : ℝ := h*gridIndex h x

lemma gridCell_mem_iff {h x : ℝ} (hh : 0 < h) (i : ℤ) :
    x ∈ gridCell h i ↔ gridIndex h x = i := by
  unfold gridCell gridIndex
  rw [Int.floor_eq_iff]
  simp only [Set.mem_Ico]
  constructor
  · intro hx
    exact ⟨(le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hx.1),
      (div_lt_iff₀ hh).mpr (by simpa only [mul_comm] using hx.2)⟩
  · intro hx
    exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hh).mp hx.1,
      by simpa only [mul_comm] using (div_lt_iff₀ hh).mp hx.2⟩

lemma gridPoint_le {h : ℝ} (hh : 0 < h) (x : ℝ) : gridPoint h x ≤ x := by
  exact ((gridCell_mem_iff hh (gridIndex h x)).mpr rfl).1

lemma gridPoint_lt_add {h : ℝ} (hh : 0 < h) (x : ℝ) : x < gridPoint h x+h := by
  have hh' := ((gridCell_mem_iff hh (gridIndex h x)).mpr rfl).2
  dsimp [gridCell,gridPoint] at *
  linarith only [hh']

lemma abs_gridPoint_sub_lt {h : ℝ} (hh : 0 < h) (x : ℝ) : |gridPoint h x-x| < h := by
  rw [abs_of_nonpos (sub_nonpos.mpr (gridPoint_le hh x))]
  linarith only [gridPoint_lt_add hh x]

lemma volume_gridCell (h : ℝ) (i : ℤ) : volume (gridCell h i) = ENNReal.ofReal h := by
  rw [gridCell,Real.volume_Ico]
  congr 1
  ring

def gridRect (h : ℝ) (i j : ℤ) : Set (ℝ×ℝ) := gridCell h i ×ˢ gridCell h j

def gridLift (D : Finset ℤ) (h : ℝ) {E : Type uE} [AddCommMonoid E] (f : D → D → E) (z : ℝ×ℝ) : E :=
  ∑ i : D, ∑ j : D, (gridRect h i j).indicator (fun _ => f i j) z

lemma gridRect_mem_iff {h : ℝ} (hh : 0 < h) (z : ℝ×ℝ) (i j : ℤ) :
    z ∈ gridRect h i j ↔ gridIndex h z.1 = i ∧ gridIndex h z.2 = j := by
  exact and_congr (gridCell_mem_iff hh i) (gridCell_mem_iff hh j)

lemma gridLift_eq {D : Finset ℤ} {h : ℝ} (hh : 0 < h) {E : Type uE} [AddCommMonoid E]
    (f : D → D → E) (z : ℝ×ℝ) : gridLift D h f z =
      if hi : gridIndex h z.1 ∈ D then if hj : gridIndex h z.2 ∈ D then
        f ⟨gridIndex h z.1,hi⟩ ⟨gridIndex h z.2,hj⟩ else 0 else 0 := by
  classical
  unfold gridLift
  simp_rw [Set.indicator_apply,gridRect_mem_iff hh]
  split_ifs with hi hj
  · rw [Finset.sum_eq_single (⟨gridIndex h z.1,hi⟩:D)]
    · rw [Finset.sum_eq_single (⟨gridIndex h z.2,hj⟩:D)]
      · simp
      · intro j _ hj'
        have hne : gridIndex h z.2 ≠ (j:ℤ) := by intro he; exact hj' (Subtype.ext he.symm)
        simp only [hne,and_false,ite_false]
      · simp
    · intro i _ hi'
      have hne : gridIndex h z.1 ≠ (i:ℤ) := by intro he; exact hi' (Subtype.ext he.symm)
      simp only [hne,false_and,ite_false,Finset.sum_const_zero]
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hne : gridIndex h z.2 ≠ (j:ℤ) := by intro he; exact hj (he ▸ j.property)
    simp only [hne,and_false,ite_false]
  · apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hne : gridIndex h z.1 ≠ (i:ℤ) := by intro he; exact hi (he ▸ i.property)
    simp only [hne,false_and,ite_false]

lemma gridLift_comp {D : Finset ℤ} {h : ℝ} (hh : 0 < h) {E : Type uE} {F : Type uF} [AddCommMonoid E] [AddCommMonoid F]
    (f : D → D → E) (g : E → F) (hg : g 0 = 0) (z : ℝ×ℝ) :
    g (gridLift D h f z) = gridLift D h (fun i j => g (f i j)) z := by
  simp only [gridLift_eq hh]
  split_ifs <;> simp only [hg]

lemma measurableSet_gridRect (h : ℝ) (i j : ℤ) : MeasurableSet (gridRect h i j) :=
  measurableSet_Ico.prod measurableSet_Ico

lemma volume_gridRect (h : ℝ) (i j : ℤ) : volume (gridRect h i j) = (ENNReal.ofReal h)^2 := by
  change (volume.prod volume) (gridCell h i ×ˢ gridCell h j) = _
  rw [Measure.prod_prod,volume_gridCell,volume_gridCell,pow_two]

lemma integral_gridLift (D : Finset ℤ) (h : ℝ) {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : D → D → E) (hh : 0 ≤ h) :
    (∫ z : ℝ×ℝ, gridLift D h f z) = ∑ i, ∑ j, h^2 • f i j := by
  have hi (i j : D) : Integrable ((gridRect h i j).indicator (fun _ : ℝ×ℝ => f i j)) :=
    IntegrableOn.integrable_indicator
      (integrableOn_const (μ := volume) (s := gridRect h i j) (C := f i j)
        (by rw [volume_gridRect]; finiteness)) (measurableSet_gridRect h i j)
  unfold gridLift
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator (measurableSet_gridRect h i j),setIntegral_const,measureReal_def,volume_gridRect,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hh]
end
end TriangularHilbert
end

end OAI
