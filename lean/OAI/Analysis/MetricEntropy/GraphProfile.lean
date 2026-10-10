import OAI.Analysis.MetricEntropy.PartitionGraph
import OAI.Analysis.MetricEntropy.LogProfile
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.Linarith

namespace OAI

universe uX uι uLabel

/-!
# The actual logarithmic graph matrix

Columns retain both their vertex and their admissible partition set. The graph
metric takes values in ENat, so disconnected vertices have profile zero.
The row separation proof uses an actual coordinate of this matrix; the finite
field construction supplies its graph-separation hypothesis separately.
-/

noncomputable section

namespace MetricEntropyDuality.GraphProfile

open scoped BigOperators

variable {X : Type uX} {ι : Type uι} {Label : ι → Type uLabel}

/-- Actual column indices, including the choice of partition graph. -/
abbrev Columns (X : Type uX) (𝒯 : Finset (Finset ι)) :=
  X × {T : Finset ι // T ∈ 𝒯}

/-- The graph-distance column function. -/
def column (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι)) (h : ℕ)
    (y : Columns X 𝒯) (x : X) : ℝ :=
  LogProfile.phi h (PartitionGraph.distance L y.2.val x y.1)

/-- The actual row vector has one coordinate for every actual column. -/
def row (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι)) (h : ℕ)
    (x : X) : Columns X 𝒯 → ℝ := fun y => column L 𝒯 h y x

theorem column_nonneg (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι))
    {h : ℕ} (_hh : 0 < h) (y : Columns X 𝒯) (x : X) :
    0 ≤ column L 𝒯 h y x :=
  LogProfile.phi_nonneg h _

theorem column_le_one (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι))
    {h : ℕ} (hh : 0 < h) (y : Columns X 𝒯) (x : X) :
    column L 𝒯 h y x ≤ 1 :=
  LogProfile.phi_le_one hh _

theorem column_self (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι))
    {h : ℕ} (_hh : 0 < h) (x : X) (T : {T : Finset ι // T ∈ 𝒯}) :
    column L 𝒯 h (x, T) x = 1 := by
  unfold column
  rw [PartitionGraph.distance_self]
  exact LogProfile.phi_zero h

theorem column_eq_zero_of_le (L : (i : ι) → X → Label i)
    (𝒯 : Finset (Finset ι)) {h : ℕ} (hh : 0 < h)
    (y : Columns X 𝒯) (x : X)
    (hd : (h : ℕ∞) ≤ PartitionGraph.distance L y.2.val x y.1) :
    column L 𝒯 h y x = 0 :=
  LogProfile.phi_eq_zero_of_le hh hd

/-- Exact finite-ball expansion, with no finite-distance assumption. -/
theorem column_eq_sum (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι))
    {h : ℕ} (hh : 0 < h) (y : Columns X 𝒯) (x : X) :
    column L 𝒯 h y x = ∑ j ∈ Finset.range h,
      if PartitionGraph.distance L y.2.val x y.1 ≤ (j : ℕ∞)
      then LogProfile.gamma h j else 0 :=
  LogProfile.phi_eq_sum hh _

/-- The concrete coordinate witness consumed by the convex-body construction. -/
theorem exists_column_abs_eq_one (L : (i : ι) → X → Label i)
    (𝒯 : Finset (Finset ι)) {h : ℕ} (hh : 0 < h) (x z : X)
    (hsep : ∃ T ∈ 𝒯, (h : ℕ∞) < PartitionGraph.distance L T x z) :
    ∃ y : Columns X 𝒯, |column L 𝒯 h y x - column L 𝒯 h y z| = 1 := by
  obtain ⟨T, hT, hd⟩ := hsep
  let c : Columns X 𝒯 := (x, ⟨T, hT⟩)
  have hx : column L 𝒯 h c x = 1 := column_self L 𝒯 hh x ⟨T, hT⟩
  have hz : column L 𝒯 h c z = 0 := by
    apply column_eq_zero_of_le L 𝒯 hh c z
    change (h : ℕ∞) ≤ PartitionGraph.distance L T z x
    rw [PartitionGraph.distance_comm]
    exact hd.le
  refine ⟨c, ?_⟩
  rw [hx, hz, sub_zero, abs_one]

/-- All row coordinates lie in the common unit interval. -/
theorem abs_row_sub_le_one (L : (i : ι) → X → Label i)
    (𝒯 : Finset (Finset ι)) {h : ℕ} (hh : 0 < h)
    (x z : X) (y : Columns X 𝒯) :
    |row L 𝒯 h x y - row L 𝒯 h z y| ≤ 1 := by
  have hx0 := column_nonneg L 𝒯 hh y x
  have hx1 := column_le_one L 𝒯 hh y x
  have hz0 := column_nonneg L 𝒯 hh y z
  have hz1 := column_le_one L 𝒯 hh y z
  change |column L 𝒯 h y x - column L 𝒯 h y z| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The column `(x,T)` certifies exact unit separation, including when the
chosen graph disconnects x from z. -/
theorem norm_row_sub_eq_one [Fintype X]
    (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι))
    {h : ℕ} (hh : 0 < h) (x z : X)
    (hsep : ∃ T ∈ 𝒯, (h : ℕ∞) < PartitionGraph.distance L T x z) :
    ‖row L 𝒯 h x - row L 𝒯 h z‖ = 1 := by
  classical
  obtain ⟨T, hT, hd⟩ := hsep
  let c : Columns X 𝒯 := (x, ⟨T, hT⟩)
  have hx : column L 𝒯 h c x = 1 := column_self L 𝒯 hh x ⟨T, hT⟩
  have hz : column L 𝒯 h c z = 0 := by
    apply column_eq_zero_of_le L 𝒯 hh c z
    change (h : ℕ∞) ≤ PartitionGraph.distance L T z x
    rw [PartitionGraph.distance_comm]
    exact hd.le
  have hc : (row L 𝒯 h x - row L 𝒯 h z) c = 1 := by
    change column L 𝒯 h c x - column L 𝒯 h c z = 1
    rw [hx, hz, sub_zero]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro y
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using abs_row_sub_le_one L 𝒯 hh x z y
  · have hb := norm_le_pi_norm (row L 𝒯 h x - row L 𝒯 h z) c
    simpa only [hc, norm_one] using hb

/-- The norm equality also gives the usual finite-product metric equality. -/
theorem dist_row_eq_one [Fintype X]
    (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι))
    {h : ℕ} (hh : 0 < h) (x z : X)
    (hsep : ∃ T ∈ 𝒯, (h : ℕ∞) < PartitionGraph.distance L T x z) :
    dist (row L 𝒯 h x) (row L 𝒯 h z) = 1 := by
  rw [dist_eq_norm]
  exact norm_row_sub_eq_one L 𝒯 hh x z hsep

end MetricEntropyDuality.GraphProfile

end

end OAI
