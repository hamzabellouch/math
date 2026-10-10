import OAI.Analysis.LipschitzHilbert.Trees.SourceLineMaximal
import OAI.Analysis.LipschitzHilbert.Estimates.PartitionIntegral

namespace OAI

/-! A uniform L² bound for actual dyadic cell averages on the whole line.
The root intervals are glued using their true measurable partition. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

def cellMean (q k : ℤ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ y in cell q k (index q k x), f y)/scale k

def dyadicMaximal (q top : ℤ) (N : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  finiteMaxSignal (fun n => cellMean q (top-(n:ℤ)) f) N

theorem cellMean_measurable (q k : ℤ) (f : ℝ → ℝ) : Measurable (cellMean q k f) :=
  (measurable_of_countable (fun i : ℤ => (∫ y in cell q k i, f y)/scale k)).comp (index_measurable q k)

theorem dyadicMaximal_measurable (q top : ℤ) (N : ℕ) (f : ℝ → ℝ) :
    Measurable (dyadicMaximal q top N f) :=
  finiteMaxSignal_measurable _ _ (fun n _ => cellMean_measurable q (top-(n:ℤ)) f)

theorem dyadicMaximal_nonneg (q top : ℤ) (N : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    0≤dyadicMaximal q top N f x := finiteMaxSignal_nonneg _ _ _

theorem dyadicMaximal_eq_on_root (q top j : ℤ) (N : ℕ) {f : ℝ → ℝ}
    (hf : Integrable f (rootMeasure q top j)) {x : ℝ} (hx : x∈cell q top j) :
    dyadicMaximal q top N f x=finiteMaxSignal (lineAverage q top j f) N x := by
  have heq : (fun n : ℕ => |cellMean q (top-(n:ℤ)) f x|) =
      (fun n : ℕ => |lineAverage q top j f n x|) := by
    funext n
    rw [lineAverage_eq_cell_mean q top j hf n hx]
    rfl
  exact congrArg (fun g : ℕ → ℝ => (Finset.range (N+1)).sup' Finset.nonempty_range_add_one g) heq

theorem dyadicMaximal_root_memLp (q top j : ℤ) (N : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (rootMeasure q top j)) :
    MemLp (dyadicMaximal q top N f) 2 (rootMeasure q top j) := by
  have hm := finiteMaxSignal_memLp (rootMeasure q top j) (lineAverage q top j f) N
    (fun n => lineAverage_memLp q top j hf n)
  refine (memLp_congr_ae ?_).mp hm
  change ∀ᵐ x ∂volume.restrict (cell q top j), _
  filter_upwards [ae_restrict_mem (cell_measurable q top j)] with x hx
  exact (dyadicMaximal_eq_on_root q top j N (hf.integrable (by norm_num)) hx).symm

theorem dyadicMaximal_root_energy (q top j : ℤ) (N : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (rootMeasure q top j)) :
    (∫ x, (dyadicMaximal q top N f x)^2 ∂rootMeasure q top j) ≤
      4*∫ x, (f x)^2 ∂rootMeasure q top j := by
  have heq : ∀ᵐ x ∂rootMeasure q top j,
      (dyadicMaximal q top N f x)^2=(finiteMaxSignal (lineAverage q top j f) N x)^2 := by
    change ∀ᵐ x ∂volume.restrict (cell q top j), _
    filter_upwards [ae_restrict_mem (cell_measurable q top j)] with x hx
    rw [dyadicMaximal_eq_on_root q top j N (hf.integrable (by norm_num)) hx]
  rw [integral_congr_ae heq]
  exact lineAverage_maximal_energy q top j hf N

/-- Actual finite dyadic maximal averages are L² bounded on Lebesgue
measure with constant four in squared norm, uniformly in both cutoffs. -/
theorem dyadicMaximal_energy (q top : ℤ) (N : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) :
    MemLp (dyadicMaximal q top N f) 2 volume ∧
    (∫ x, (dyadicMaximal q top N f x)^2) ≤ 4*∫ x, (f x)^2 := by
  have hcover : ⋃ j : ℤ, cell q top j = (univ : Set ℝ) := by
    apply Set.eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨index q top x,mem_index_cell q top x⟩
  have hdisj : Pairwise (fun i j : ℤ => Disjoint (cell q top i) (cell q top j)) :=
    fun _ _ h => cells_disjoint q top h
  have hroot (j : ℤ) : MemLp f 2 (rootMeasure q top j) := hf.restrict _
  have h := integral_le_of_partition volume (cell q top) (cell_measurable q top) hdisj hcover
    (fun x => (dyadicMaximal q top N f x)^2) (fun x => (f x)^2)
    (fun x => sq_nonneg _) hf.integrable_sq
    (fun j => (dyadicMaximal_root_memLp q top j N (hroot j)).integrable_sq)
    (fun j => dyadicMaximal_root_energy q top j N (hroot j))
  exact ⟨(memLp_two_iff_integrable_sq (dyadicMaximal_measurable q top N f).aestronglyMeasurable).mpr h.1,h.2⟩

end LipschitzHilbert.DyadicLineGrid

end

end OAI
