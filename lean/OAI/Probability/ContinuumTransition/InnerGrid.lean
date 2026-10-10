import OAI.Probability.ContinuumTransition.UpperKac

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def innerGridBox (u : ℝ) (k : Lattice) : Set Space :=
  (fun x : Space => x+gridCenter u k) '' cube (u-2)

theorem measurableSet_innerGridBox (u : ℝ) (k : Lattice) : MeasurableSet (innerGridBox u k) :=
  ((isCompact_cube (u-2)).image (continuous_id.add continuous_const)).measurableSet

theorem innerGridBox_subset_gridBox (u : ℝ) (k : Lattice) : innerGridBox u k ⊆ gridBox u k := by
  rintro x ⟨a,ha,rfl⟩ i
  have hi := ha i
  change u*(k i : ℝ) ≤ a i+u*((k i : ℝ)+1/2) ∧ a i+u*((k i : ℝ)+1/2) < u*((k i : ℝ)+1)
  constructor <;> linarith [hi.1,hi.2]

theorem innerGridBox_disjoint {u : ℝ} (hu : 0 < u) {k l : Lattice} (hkl : k ≠ l) :
    Disjoint (innerGridBox u k) (innerGridBox u l) :=
  (gridBox_disjoint hu hkl).mono (innerGridBox_subset_gridBox u k) (innerGridBox_subset_gridBox u l)

theorem innerGridBox_separation {u : ℝ} (hu : 2 ≤ u) {k l : Lattice} (hkl : k ≠ l)
    {x y : Space} (hx : x ∈ innerGridBox u k) (hy : y ∈ innerGridBox u l) : 2 ≤ ‖x-y‖ := by
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  obtain ⟨i,hi⟩ : ∃ i, k i ≠ l i := by
    by_contra! hh
    exact hkl (funext hh)
  have hai := ha i
  have hbi := hb i
  have hh : |(a+gridCenter u k) i-(b+gridCenter u l) i| ≤
      ‖(a+gridCenter u k)-(b+gridCenter u l)‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
      PiLp.norm_apply_le ((a+gridCenter u k)-(b+gridCenter u l)) i
  change |a i+u*((k i : ℝ)+1/2)-(b i+u*((l i : ℝ)+1/2))| ≤ _ at hh
  rw [abs_le] at hh
  rcases lt_or_gt_of_ne hi with hk | hl
  · have hlk : (k i : ℝ)+1 ≤ (l i : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hk)
    have hm := mul_le_mul_of_nonneg_left hlk (by linarith : 0 ≤ u)
    nlinarith [hai.1,hai.2,hbi.1,hbi.2]
  · have hlk : (l i : ℝ)+1 ≤ (k i : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hl)
    have hm := mul_le_mul_of_nonneg_left hlk (by linarith : 0 ≤ u)
    nlinarith [hai.1,hai.2,hbi.1,hbi.2]

theorem gridIndices_mono {m n : ℕ} (h : m ≤ n) : gridIndices m 1 ⊆ gridIndices n 1 := by
  intro k hk
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hk i)
  apply Finset.mem_Icc.mpr
  change -(n : ℤ)*1 ≤ k i ∧ k i ≤ (n : ℤ)*1
  change -(m : ℤ)*1 ≤ k i ∧ k i ≤ (m : ℤ)*1 at hi
  have hn : (m : ℤ) ≤ n := Int.ofNat_le.mpr h
  constructor <;> omega

theorem gridIndex_coordinate_bounds {m : ℕ} {k : Lattice} (hk : k ∈ gridIndices m 1) (i : Fin 3) :
    -(m : ℝ) ≤ k i ∧ (k i : ℝ) ≤ m := by
  have hi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hk i)
  change -(m : ℤ)*1 ≤ k i ∧ k i ≤ (m : ℤ)*1 at hi
  exact_mod_cast (by simpa only [mul_one] using hi)

theorem innerGridBox_subset_cube {u : ℝ} (hu : 0 ≤ u) {m : ℕ} {k : Lattice}
    (hk : k ∈ gridIndices m 1) : innerGridBox u k ⊆ cube (2*((m : ℝ)+1)*u) := by
  rintro x ⟨a,ha,rfl⟩ i
  have hi := ha i
  have hk' := gridIndex_coordinate_bounds hk i
  have hl := mul_le_mul_of_nonneg_left hk'.1 hu
  have hr := mul_le_mul_of_nonneg_left hk'.2 hu
  change -(2*((m : ℝ)+1)*u)/2 ≤ a i+u*((k i : ℝ)+1/2) ∧
    a i+u*((k i : ℝ)+1/2) ≤ (2*((m : ℝ)+1)*u)/2
  constructor <;> linarith [hi.1,hi.2]

theorem interior_grid_cover {u R : ℝ} (hu : 0 < u) {N m : ℕ} (hN : R+u ≤ (N : ℝ)*u)
    {k : Lattice} (hk : k ∈ gridIndices m 1) (y : Space) (hy : ‖gridCenter u k-y‖ < R) :
    ∃ l ∈ gridIndices (m+N) 1, y ∈ gridBox u l := by
  suffices hy' : y ∈ ⋃ l ∈ gridIndices (m+N) 1, gridBox u l by
    obtain ⟨l,hl,hyl⟩ := mem_iUnion₂.mp hy'
    exact ⟨l,hl,hyl⟩
  apply cube_subset_gridBlocks hu (m+N)
  intro i
  have hk' := gridIndex_coordinate_bounds hk i
  have hl := mul_le_mul_of_nonneg_left hk'.1 hu.le
  have hr := mul_le_mul_of_nonneg_left hk'.2 hu.le
  have hi : |u*((k i : ℝ)+1/2)-y i| < R := by
    have hh := PiLp.norm_apply_le (gridCenter u k-y) i
    change |u*((k i : ℝ)+1/2)-y i| ≤ ‖gridCenter u k-y‖ at hh
    exact hh.trans_lt hy
  rw [abs_lt] at hi
  change -(2*((m+N : ℕ) : ℝ)*u)/2 ≤ y i ∧ y i ≤ 2*((m+N : ℕ) : ℝ)*u/2
  push_cast
  constructor <;> linarith [hi.1,hi.2]

end ContinuumTemperature
end

end OAI
