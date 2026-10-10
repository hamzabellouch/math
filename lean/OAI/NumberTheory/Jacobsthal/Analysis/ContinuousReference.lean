import OAI.NumberTheory.Jacobsthal.Estimates.BoundaryGateSets

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped Topology
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

noncomputable def truncatedReference (N : ℕ) (i : Side) (r b : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,(-1:ℝ)^n*boundaryTerm n i r b

theorem boundaryTerm_zero_of_index (n : ℕ) (hn : 2 ≤ n) (i : Side) {r b : ℝ}
    (hr : r ≤ (n:ℝ)-1) : boundaryTerm n i r b=0 := by
  have he : n=(n-2)+2 := by omega
  rw [he]
  apply boundaryTerm_depth_zero
  have hc : ((n-2:ℕ):ℝ)=(n:ℝ)-2 := by rw [Nat.cast_sub hn]; norm_num
  linarith

theorem truncatedReference_stable {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M)
    (i : Side) {r b : ℝ} (hr : r ≤ (N:ℝ)-1) :
    truncatedReference N i r b=truncatedReference M i r b := by
  unfold truncatedReference
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro n _hnM hnN
  have hNn : N ≤ n := le_of_not_gt (by simpa only [Finset.mem_range] using hnN)
  have hrn : r ≤ (n:ℝ)-1 := hr.trans (sub_le_sub_right (by exact_mod_cast hNn) 1)
  rw [boundaryTerm_zero_of_index n (hN.trans hNn) i hrn,mul_zero]

noncomputable def referenceDepth (r : ℝ) : ℕ := ⌈max r 0⌉₊+3

theorem referenceDepth_bounds (r : ℝ) : 2 ≤ referenceDepth r ∧ r ≤ (referenceDepth r : ℝ)-1 := by
  have h := Nat.le_ceil (max r 0)
  have hr : r ≤ max r 0 := le_max_left _ _
  unfold referenceDepth
  constructor
  · omega
  · push_cast
    linarith

noncomputable def boundaryReference (i : Side) (r b : ℝ) : ℝ :=
  truncatedReference (referenceDepth r) i r b

theorem boundaryReference_eq_truncated (N : ℕ) (hN : 2 ≤ N) (i : Side)
    {r b : ℝ} (hr : r ≤ (N:ℝ)-1) : boundaryReference i r b=truncatedReference N i r b := by
  unfold boundaryReference
  rcases le_total (referenceDepth r) N with h | h
  · exact truncatedReference_stable (referenceDepth_bounds r).1 h i (referenceDepth_bounds r).2
  · exact (truncatedReference_stable hN h i hr).symm

theorem truncatedReference_continuous (N : ℕ) (i : Side) :
    Continuous (fun p : ℝ×ℝ => truncatedReference N i p.1 p.2) := by
  apply continuous_finsetSum
  intro n _hn
  exact continuous_const.mul (boundaryTerm_continuous n i)

theorem boundaryReference_continuous (i : Side) :
    Continuous (fun p : ℝ×ℝ => boundaryReference i p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let N := referenceDepth (p.1+1)
  have hc := (truncatedReference_continuous N i).continuousAt (x:=p)
  apply hc.congr_of_eventuallyEq
  have he : ∀ᶠ q : ℝ×ℝ in 𝓝 p,q.1 < p.1+1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by linarith : p.1 < p.1+1))
  filter_upwards [he] with q hq
  exact boundaryReference_eq_truncated N (referenceDepth_bounds (p.1+1)).1 i
    (hq.le.trans (referenceDepth_bounds (p.1+1)).2)

end ErdosContinuousBoundary

end

end Erdos970

end OAI
