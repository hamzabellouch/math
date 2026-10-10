import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineMaximal

namespace OAI

/-! Horizontal Whitney cells for the ordinary tree estimate. An allowed
cell has no tile of shorter length whose center meets its triple. A
maximal allowed cell obtains its concrete witness from its parent. -/
noncomputable section
open Set
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid
attribute [local instance] Classical.propDecidable

def center (k j : ℤ) : ℝ := left 0 k j+scale k/2

def Allowed {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ) (k j : ℤ) : Prop :=
  ∀ i ∈ tiles, ell i ≤ scale k → (3/2:ℝ)*scale k < |x i-center k j|

def Whitney {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ) (k j : ℤ) : Prop :=
  Allowed tiles x ell k j ∧ ¬Allowed tiles x ell (k+1) (parent 0 k j)

theorem point_center_bound (k j : ℤ) {z : ℝ} (hz : z ∈ cell 0 k j) :
    |z-center k j| ≤ scale k/2 := by
  have hr : left 0 k (j+1)=left 0 k j+scale k := by
    simp only [left,Int.cast_add,Int.cast_one]
    ring
  change left 0 k j ≤ z ∧ z < left 0 k (j+1) at hz
  rw [hr] at hz
  unfold center
  exact abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩

theorem center_parent_bound (k j : ℤ) :
    |center k j-center (k+1) (parent 0 k j)| ≤ scale k/2 := by
  have hlo : 2*(j/2) ≤ j := by omega
  have hhi : j ≤ 2*(j/2)+1 := by omega
  have hlo' : (2:ℝ)*(j/2:ℤ) ≤ j := by exact_mod_cast hlo
  have hhi' : (j:ℝ) ≤ 2*(j/2:ℤ)+1 := by exact_mod_cast hhi
  have hs := scale_pos k
  have hl := mul_le_mul_of_nonneg_left hlo' hs.le
  have hh := mul_le_mul_of_nonneg_left hhi' hs.le
  simp only [center,left,parent,shift,Int.mul_zero,Int.cast_zero,zero_div,add_zero,scale_succ]
  apply abs_le.mpr
  constructor <;> nlinarith only [hl,hh,hs]

theorem allowed_of_parent {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    (k j : ℤ) (h : Allowed tiles x ell (k+1) (parent 0 k j)) :
    Allowed tiles x ell k j := by
  intro i hi hlen
  have hs := scale_pos k
  have hlen' : ell i ≤ scale (k+1) := by rw [scale_succ]; linarith only [hlen,hs]
  have hp := h i hi hlen'
  have hd := center_parent_bound k j
  have ht := abs_sub_le (x i) (center k j) (center (k+1) (parent 0 k j))
  rw [scale_succ] at hp
  linarith only [hp,hd,ht,hs]

theorem short_tile_separation {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    {k j : ℤ} (h : Allowed tiles x ell k j) {i : ι} (hi : i ∈ tiles)
    (hlen : ell i ≤ scale k) {z : ℝ} (hz : z ∈ cell 0 k j) :
    scale k < |x i-z| := by
  have hp := h i hi hlen
  have hd := point_center_bound k j hz
  have ht := abs_sub_le (x i) z (center k j)
  linarith only [hp,hd,ht]

theorem parent_witness {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    {k j : ℤ} (h : Whitney tiles x ell k j) :
    ∃ i ∈ tiles, ell i ≤ 2*scale k ∧
      ∀ z ∈ cell 0 k j, |x i-z| ≤ 4*scale k := by
  have hn := h.2
  simp only [Allowed,not_forall,not_lt] at hn
  obtain ⟨i,hi,hlen,hnear⟩ := hn
  refine ⟨i,hi,by simpa only [scale_succ] using hlen,?_⟩
  intro z hz
  have hd := point_center_bound (k+1) (parent 0 k j) (cell_subset_parent 0 k j hz)
  rw [scale_succ] at hd hnear
  have ht := abs_sub_le (x i) (center (k+1) (parent 0 k j)) z
  rw [abs_sub_comm (center (k+1) (parent 0 k j)) z] at ht
  linarith only [ht,hd,hnear]

/-- The index of a point at the next scale is exactly its parent index. -/
theorem parent_index (k : ℤ) (z : ℝ) :
    parent 0 k (index 0 k z) = index 0 (k+1) z :=
  (index_eq_of_mem (cell_subset_parent 0 k (index 0 k z)
    (mem_index_cell 0 k z))).symm

/-- Being allowed passes from a larger cell to every smaller cell it meets. -/
theorem allowed_at_point_mono {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    {k l : ℤ} (hkl : k ≤ l) (z : ℝ)
    (h : Allowed tiles x ell l (index 0 l z)) :
    Allowed tiles x ell k (index 0 k z) := by
  obtain ⟨n,rfl⟩ := Int.le.dest hkl
  induction n with
  | zero => simpa only [Nat.cast_zero,add_zero] using h
  | succ n ih =>
    apply ih (by omega)
    apply allowed_of_parent tiles x ell (k+n) (index 0 (k+n) z)
    simpa only [parent_index,Nat.cast_add,Nat.cast_one,add_assoc] using h

/-- Distinct maximal allowed cells are disjoint at all scales. -/
theorem whitney_disjoint {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    {k l i j : ℤ} (hi : Whitney tiles x ell k i)
    (hj : Whitney tiles x ell l j) (hne : (k,i) ≠ (l,j)) :
    Disjoint (cell 0 k i) (cell 0 l j) := by
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  have hei := index_eq_of_mem hzi
  have hej := index_eq_of_mem hzj
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · apply hi.2
    have hp := cell_subset_parent 0 k i hzi
    have he := index_eq_of_mem hp
    rw [← he]
    apply allowed_at_point_mono tiles x ell (by omega : k+1 ≤ l) z
    simpa only [hej] using hj.1
  · subst l
    exact hne (by simp [hei.symm.trans hej])
  · apply hj.2
    have hp := cell_subset_parent 0 l j hzj
    have he := index_eq_of_mem hp
    rw [← he]
    apply allowed_at_point_mono tiles x ell (by omega : l+1 ≤ k) z
    simpa only [hei] using hi.1

theorem scale_mono {k l : ℤ} (hkl : k ≤ l) : scale k ≤ scale l :=
  zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hkl

/-- A finite family of positive tile lengths has a common strictly smaller scale. -/
theorem exists_small_scale {ι : Type*} (tiles : Finset ι) (ell : ι → ℝ)
    (hpos : ∀ i ∈ tiles, 0 < ell i) :
    ∃ k : ℤ, ∀ i ∈ tiles, scale k < ell i := by
  classical
  induction tiles using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert i tiles hi ih =>
    obtain ⟨k,hk⟩ := ih (fun j hj => hpos j (Finset.mem_insert_of_mem hj))
    obtain ⟨l,hl,_⟩ := exists_mem_Ioc_zpow
      (hpos i (Finset.mem_insert_self i tiles)) (by norm_num : (1:ℝ) < 2)
    refine ⟨min k l,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (scale_mono (min_le_right k l)).trans_lt hl
    · exact (scale_mono (min_le_left k l)).trans_lt (hk j hj)

/-- Every real point lies in a maximal allowed interval. The upper scale
is obtained from one actual tile, rather than an assumed global cutoff. -/
theorem exists_whitney_cover {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    (hne : tiles.Nonempty) (hpos : ∀ i ∈ tiles, 0 < ell i) (z : ℝ) :
    ∃ k j, Whitney tiles x ell k j ∧ z ∈ cell 0 k j := by
  obtain ⟨k,hk⟩ := exists_small_scale tiles ell hpos
  obtain ⟨i,hi⟩ := hne
  obtain ⟨l,_,hl⟩ := exists_mem_Ico_zpow
    (show 0 < max (ell i) |x i-z| + 1 by
      have := le_max_right (ell i) |x i-z|
      linarith [abs_nonneg (x i-z)]) (by norm_num : (1:ℝ) < 2)
  let top := max k (l+1)
  have hbig : max (ell i) |x i-z| < scale top := by
    exact (lt_trans (by linarith) hl).trans_le (scale_mono (le_max_right k (l+1)))
  have htop : ¬Allowed tiles x ell top (index 0 top z) := by
    intro h
    have ha := h i hi ((le_max_left (ell i) |x i-z|).trans hbig.le)
    have hd := point_center_bound top (index 0 top z) (mem_index_cell 0 top z)
    have ht := abs_sub_le (x i) z (center top (index 0 top z))
    have hz := (le_max_right (ell i) |x i-z|).trans hbig.le
    linarith only [ha,hd,ht,hz]
  have hstart : Allowed tiles x ell k (index 0 k z) := by
    intro j hj hlen
    exact False.elim ((hk j hj).not_ge hlen)
  obtain ⟨m,j,hm,hsub⟩ := exists_maximalBad (le_max_left k (l+1)) hstart
  have hz := hsub (mem_index_cell 0 k z)
  refine ⟨m,j,⟨hm.2.1,?_⟩,hz⟩
  have hmt : m < top := by
    apply lt_of_le_of_ne hm.1
    intro he
    apply htop
    have hz' : z ∈ cell 0 top j := by simpa only [he] using hz
    rw [index_eq_of_mem hz']
    simpa only [he] using hm.2.1
  exact hm.2.2 (m+1) (parent 0 m j) (by omega) (by omega)
    (cell_subset_parent 0 m j)

end LipschitzHilbert.SourceWhitney

end

end OAI
