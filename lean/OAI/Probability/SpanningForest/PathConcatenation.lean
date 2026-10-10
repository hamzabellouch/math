import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Problem336.PathConcatenation
abbrev UnitPath := C(Set.Icc (0 : ℝ) 1, ℝ)
local instance : MeasurableSpace UnitPath := borel UnitPath
local instance : BorelSpace UnitPath := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ, ℝ) := borel C(ℝ, ℝ)
local instance : BorelSpace C(ℝ, ℝ) := ⟨rfl⟩
def leftEnd : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
def rightEnd : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩

def segment (w : ℕ → UnitPath) (k : ℕ) (t : ℝ) : ℝ :=
  w k (Set.projIcc 0 1 (by norm_num) (t - k)) - w k leftEnd
theorem continuous_segment (w : ℕ → UnitPath) (k : ℕ) : Continuous (segment w k) := by
  unfold segment
  exact ((w k).continuous.comp (continuous_projIcc.comp
    (continuous_id.sub continuous_const))).sub continuous_const
theorem segment_eq_zero_of_le (w : ℕ → UnitPath) (k : ℕ) {t : ℝ}
    (ht : t ≤ k) : segment w k t = 0 := by
  unfold segment
  rw [Set.projIcc_of_le_left _ (sub_nonpos.mpr ht)]
  exact sub_self _
theorem segment_eq_endpoint_of_ge (w : ℕ → UnitPath) (k : ℕ) {t : ℝ}
    (ht : (k : ℝ) + 1 ≤ t) : segment w k t = w k rightEnd - w k leftEnd := by
  unfold segment
  rw [Set.projIcc_of_right_le _ (by linarith : (1 : ℝ) ≤ t - k)]
  rfl

def concat (w : ℕ → UnitPath) (t : ℝ) : ℝ := ∑' k, segment w k t
theorem concat_eq_sum (w : ℕ → UnitPath) (N : ℕ) {t : ℝ} (ht : t ≤ N) :
    concat w t = ∑ k ∈ Finset.range N, segment w k t := by
  apply tsum_eq_sum
  intro k hk
  apply segment_eq_zero_of_le
  exact ht.trans (by exact_mod_cast (Nat.le_of_not_gt (fun h => hk (Finset.mem_range.mpr h))))
theorem continuous_concat (w : ℕ → UnitPath) : Continuous (concat w) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have hc : Continuous (fun s => ∑ k ∈ Finset.range N, segment w k s) :=
    continuous_finsetSum _ (fun k _ => continuous_segment w k)
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hN] with s hs
  exact concat_eq_sum w N (le_of_lt hs)

def concatPath (w : ℕ → UnitPath) : C(ℝ, ℝ) := ⟨concat w, continuous_concat w⟩
@[simp] theorem concat_nonpos (w : ℕ → UnitPath) {t : ℝ} (ht : t ≤ 0) : concat w t = 0 := by
  simpa using concat_eq_sum w 0 (by simpa using ht)
theorem continuous_segment_joint (k : ℕ) :
    Continuous (fun q : (ℕ → UnitPath) × ℝ => segment q.1 k q.2) := by
  unfold segment
  have hw : Continuous (fun q : (ℕ → UnitPath) × ℝ => q.1 k) :=
    (continuous_apply k).comp continuous_fst
  have ht : Continuous (fun q : (ℕ → UnitPath) × ℝ =>
      Set.projIcc (0 : ℝ) 1 (by norm_num) (q.2 - k)) :=
    continuous_projIcc.comp (continuous_snd.sub continuous_const)
  exact (continuous_eval.comp (hw.prodMk ht)).sub
    (continuous_eval.comp (hw.prodMk continuous_const))

theorem continuous_concat_joint :
    Continuous (fun q : (ℕ → UnitPath) × ℝ => concat q.1 q.2) := by
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨N, hN⟩ := exists_nat_gt q.2
  have hc : Continuous (fun p : (ℕ → UnitPath) × ℝ =>
      ∑ k ∈ Finset.range N, segment p.1 k p.2) :=
    continuous_finsetSum _ (fun k _ => continuous_segment_joint k)
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (Iio_mem_nhds hN)] with p hp
  exact concat_eq_sum p.1 N (le_of_lt hp)

theorem continuous_concatPath : Continuous concatPath :=
  ContinuousMap.continuous_of_continuous_uncurry _ continuous_concat_joint

theorem measurable_concatPath : Measurable concatPath := continuous_concatPath.measurable

theorem segment_at_nat_add (w : ℕ → UnitPath) (n : ℕ)
    (x : Set.Icc (0 : ℝ) 1) :
    segment w n ((n : ℝ) + x) = w n x - w n leftEnd := by
  unfold segment
  rw [add_sub_cancel_left, Set.projIcc_of_mem _ x.property]

theorem concat_nat_add (w : ℕ → UnitPath) (n : ℕ)
    (x : Set.Icc (0 : ℝ) 1) :
    concat w ((n : ℝ) + x) =
      (∑ k ∈ Finset.range n, (w k rightEnd - w k leftEnd)) +
        (w n x - w n leftEnd) := by
  rw [concat_eq_sum w (n + 1) (by push_cast; linarith [x.property.2]),
    Finset.sum_range_succ, segment_at_nat_add]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply segment_eq_endpoint_of_ge
  have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hk
  linarith [x.property.1]

theorem concat_nat (w : ℕ → UnitPath) (n : ℕ) :
    concat w n = ∑ k ∈ Finset.range n, (w k rightEnd - w k leftEnd) := by
  simpa [leftEnd] using concat_nat_add w n leftEnd

theorem concat_increment_same_segment (w : ℕ → UnitPath) (n : ℕ)
    (x y : Set.Icc (0 : ℝ) 1) :
    concat w ((n : ℝ) + x) - concat w ((n : ℝ) + y) = w n x - w n y := by
  rw [concat_nat_add, concat_nat_add]
  ring

theorem concat_nat_add_of_start_zero (w : ℕ → UnitPath)
    (h : ∀ k, w k leftEnd = 0) (n : ℕ) (x : Set.Icc (0 : ℝ) 1) :
    concat w ((n : ℝ) + x) = (∑ k ∈ Finset.range n, w k rightEnd) + w n x := by
  simpa only [h, sub_zero] using concat_nat_add w n x

end Problem336.PathConcatenation

end

end OAI
