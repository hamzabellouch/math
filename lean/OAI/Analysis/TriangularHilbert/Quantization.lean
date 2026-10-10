import OAI.Analysis.TriangularHilbert.GridCell

namespace OAI

universe uE

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma measurable_gridIndex (h : ℝ) : Measurable (gridIndex h) := by
  exact Int.measurable_floor.comp (measurable_id.div_const h)

lemma measurable_gridPoint (h : ℝ) : Measurable (gridPoint h) := by
  exact measurable_const.mul ((measurable_of_countable (fun i : ℤ => (i:ℝ))).comp (measurable_gridIndex h))

def gridSquare (h : ℝ) (z : ℝ×ℝ) : ℝ×ℝ := (gridPoint h z.1,gridPoint h z.2)

lemma measurable_gridSquare (h : ℝ) : Measurable (gridSquare h) :=
  ((measurable_gridPoint h).comp measurable_fst).prodMk ((measurable_gridPoint h).comp measurable_snd)

lemma tendsto_gridPoint {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (ht : Tendsto h atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => gridPoint (h n) x) atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) ht
  exact (show ‖gridPoint (h n) x-x‖ < h n by simpa only [Real.norm_eq_abs] using abs_gridPoint_sub_lt (hh n) x).le

lemma tendsto_gridSquare {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (ht : Tendsto h atTop (𝓝 0)) (z : ℝ×ℝ) :
    Tendsto (fun n => gridSquare (h n) z) atTop (𝓝 z) :=
  (tendsto_gridPoint hh ht z.1).prodMk_nhds (tendsto_gridPoint hh ht z.2)

def sampleIndices (h M : ℝ) : Finset ℤ := Finset.Icc ⌈-M/h⌉ ⌊M/h⌋

lemma mem_sampleIndices {h : ℝ} (hh : 0 < h) (M : ℝ) (i : ℤ) :
    i ∈ sampleIndices h M ↔ |h*i| ≤ M := by
  rw [sampleIndices,Finset.mem_Icc,Int.ceil_le,Int.le_floor,abs_le]
  constructor
  · rintro ⟨hi,hj⟩
    exact ⟨by simpa only [mul_comm] using (div_le_iff₀ hh).mp hi,
      by simpa only [mul_comm] using (le_div_iff₀ hh).mp hj⟩
  · rintro ⟨hi,hj⟩
    exact ⟨(div_le_iff₀ hh).mpr (by simpa only [mul_comm] using hi),
      (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hj)⟩

def sampledMatrix {E : Type uE} (f : ℝ×ℝ → E) (h M : ℝ) :
    sampleIndices h M → sampleIndices h M → E := fun i j => f (h*(i:ℤ),h*(j:ℤ))

lemma gridLift_sampled {E : Type uE} [AddCommMonoid E] (f : ℝ×ℝ → E) {h M : ℝ}
    (hh : 0 < h) (hf : ∀ z, f z ≠ 0 → |z.1| ≤ M ∧ |z.2| ≤ M) (z : ℝ×ℝ) :
    gridLift (sampleIndices h M) h (sampledMatrix f h M) z = f (gridSquare h z) := by
  rw [gridLift_eq hh]
  split_ifs with hi hj
  · rfl
  · symm
    by_contra hn
    exact hj ((mem_sampleIndices hh M _).mpr (hf _ hn).2)
  · symm
    by_contra hn
    exact hi ((mem_sampleIndices hh M _).mpr (hf _ hn).1)

lemma sampled_support {E : Type uE} [Zero E] (f : ℝ×ℝ → E) {h M : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hf : ∀ z, f z ≠ 0 → |z.1| ≤ M ∧ |z.2| ≤ M)
    (z : ℝ×ℝ) (hz : f (gridSquare h z) ≠ 0) :
    |z.1| ≤ M+1 ∧ |z.2| ≤ M+1 := by
  have ha := hf _ hz
  have h1 := abs_gridPoint_sub_lt hh z.1
  have h2 := abs_gridPoint_sub_lt hh z.2
  have e1 := abs_add_le (z.1-gridPoint h z.1) (gridPoint h z.1)
  have e2 := abs_add_le (z.2-gridPoint h z.2) (gridPoint h z.2)
  simp only [sub_add_cancel] at e1 e2
  rw [abs_sub_comm] at h1 h2
  dsimp [gridSquare] at ha
  exact ⟨by linarith [ha.1],by linarith [ha.2]⟩
end
end TriangularHilbert
end

end OAI
