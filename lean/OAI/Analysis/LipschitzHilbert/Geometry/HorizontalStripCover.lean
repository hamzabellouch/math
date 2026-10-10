import OAI.Analysis.LipschitzHilbert.Estimates.L2SpatialPartition
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval

namespace OAI

/-! A concrete partition into horizontal strips; their one-cell
extensions have uniformly bounded overlap and contain short translates. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def horizontalCell (d : ℝ) (j : ℤ) : Set ℝ := Ico ((j:ℝ)*d) (((j:ℝ)+1)*d)
def horizontalEnlargement (d : ℝ) (j : ℤ) : Set ℝ := Icc (((j:ℝ)-1)*d) (((j:ℝ)+2)*d)

theorem horizontalCell_floor (d : ℝ) (hd : 0<d) (x : ℝ) : x∈horizontalCell d ⌊x/d⌋ := by
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le (x/d)) hd.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x/d)) hd
  rw [div_mul_cancel₀ _ hd.ne'] at hlo hhi
  exact ⟨hlo,hhi⟩

theorem horizontalCell_iUnion (d : ℝ) (hd : 0<d) : ⋃ j : ℤ, horizontalCell d j=univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨⌊x/d⌋,horizontalCell_floor d hd x⟩

theorem horizontalCell_disjoint (d : ℝ) (hd : 0<d) :
    Pairwise (fun j k : ℤ => Disjoint (horizontalCell d j) (horizontalCell d k)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro x hxj hxk
  rcases lt_or_gt_of_ne hjk with hlt|hlt
  · have h : (j:ℝ)+1≤k := by exact_mod_cast (show j+1≤k by omega)
    have hm := mul_le_mul_of_nonneg_right h hd.le
    exact (not_lt_of_ge (hm.trans hxk.1)) hxj.2
  · have h : (k:ℝ)+1≤j := by exact_mod_cast (show k+1≤j by omega)
    have hm := mul_le_mul_of_nonneg_right h hd.le
    exact (not_lt_of_ge (hm.trans hxj.1)) hxk.2

theorem horizontalCell_subset (d : ℝ) (hd : 0<d) (j : ℤ) :
    horizontalCell d j⊆horizontalEnlargement d j := by
  intro x hx
  constructor
  · linarith only [hx.1,hd]
  · linarith only [hx.2,hd]

theorem horizontalEnlargement_translate (d : ℝ) (_hd : 0<d) (j : ℤ)
    (x : ℝ) (hx : x∈horizontalCell d j) (t : ℝ) (ht : |t|≤d) :
    x-t∈horizontalEnlargement d j := by
  have ht' := abs_le.mp ht
  constructor
  · change ((j:ℝ)-1)*d≤x-t
    linarith only [hx.1,ht'.2]
  · change x-t≤((j:ℝ)+2)*d
    linarith only [hx.2,ht'.1]

theorem horizontalEnlargement_index (d : ℝ) (hd : 0<d) (x : ℝ) (j : ℤ)
    (hx : x∈horizontalEnlargement d j) :
    j∈Finset.Icc (⌊x/d⌋-2) (⌊x/d⌋+2) := by
  have hf := horizontalCell_floor d hd x
  have hleft : (⌊x/d⌋:ℝ)-2≤j := by
    have h : (((⌊x/d⌋:ℤ):ℝ)-2-(j:ℝ))*d≤0 := by
      dsimp only [horizontalCell,horizontalEnlargement,mem_Ico,mem_Icc] at hf hx
      nlinarith only [hf.1,hx.2,hd]
    nlinarith only [h,hd]
  have hright : (j:ℝ)<(⌊x/d⌋:ℝ)+2 := by
    have h : ((j:ℝ)-((⌊x/d⌋:ℤ):ℝ)-2)*d<0 := by
      dsimp only [horizontalCell,horizontalEnlargement,mem_Ico,mem_Icc] at hf hx
      nlinarith only [hf.2,hx.1,hd]
    nlinarith only [h,hd]
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast hleft
  · exact_mod_cast hright.le

theorem horizontalEnlargement_overlap (d : ℝ) (hd : 0<d) (J : Finset ℤ) (x : ℝ) :
    (∑ j∈J, (horizontalEnlargement d j).indicator (fun _ => (1:ℝ)) x)≤5 := by
  classical
  let A := J.filter (fun j => x∈horizontalEnlargement d j)
  have hsub : A⊆Finset.Icc (⌊x/d⌋-2) (⌊x/d⌋+2) := fun j hj =>
    horizontalEnlargement_index d hd x j (Finset.mem_filter.mp hj).2
  have hc : A.card≤5 := by
    have h := Finset.card_le_card hsub
    rw [Int.card_Icc] at h
    omega
  have heq : (∑ j∈J, (horizontalEnlargement d j).indicator (fun _ => (1:ℝ)) x)=(A.card:ℝ) := by
    simp only [Set.indicator]
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    rfl
  rw [heq]
  exact_mod_cast hc

end LipschitzHilbert.PacketRepresentation

end

end OAI
