import OAI.Analysis.LipschitzHilbert.Estimates.IntGeometricSum
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteEnergySchur
import OAI.Analysis.LipschitzHilbert.Trees.DyadicLineGrid

namespace OAI

/-! The actual binary scale ratio is a summable row-and-column kernel. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

def lineScaleWeight (i j : ℤ) : ℝ := (1/2:ℝ)^(j-i).natAbs

theorem lineScaleWeight_pos (i j : ℤ) : 0<lineScaleWeight i j := by
  unfold lineScaleWeight
  positivity

theorem lineScaleWeight_ratio (i j : ℤ) (hij : i≤j) :
    DyadicLineGrid.scale i/DyadicLineGrid.scale j=lineScaleWeight i j := by
  have hn : ((j-i).natAbs:ℤ)=j-i := by omega
  unfold lineScaleWeight DyadicLineGrid.scale
  rw [←zpow_natCast,show (1/2:ℝ)=(2:ℝ)⁻¹ by norm_num,inv_zpow,←zpow_neg,hn,neg_sub,
    zpow_sub₀ (by norm_num : (2:ℝ)≠0)]

theorem lineScaleWeight_row (J : Finset ℤ) (i : ℤ) :
    (∑ j∈J, lineScaleWeight i j)≤4 := by
  simpa only [lineScaleWeight,show (2:ℝ)/(1-1/2)=4 by norm_num] using
    (int_geometric_shift_sum_le (r:=(1/2:ℝ)) (by norm_num) (by norm_num) J i)

theorem lineScaleWeight_col (I : Finset ℤ) (j : ℤ) :
    (∑ i∈I, lineScaleWeight i j)≤4 := by
  have he (i : ℤ) : lineScaleWeight i j=lineScaleWeight j i := by
    unfold lineScaleWeight
    rw [←Int.natAbs_neg,neg_sub]
  simpa only [he] using lineScaleWeight_row I j

theorem line_geometric_energy_schur {E : Type*} [NormedAddCommGroup E]
    (I J : Finset ℤ) (F : ℤ → ℤ → ℝ → E)
    (hF : ∀ i∈I, ∀ j∈J, MemLp (F i j) 2 volume)
    (b : ℤ → ℝ) (hb : ∀ j∈J, 0≤b j)
    (hbound : ∀ i∈I, ∀ j∈J, (∫ x, ‖F i j x‖^2)≤(lineScaleWeight i j)^2*b j) :
    (∑ i∈I, ∫ x, ‖∑ j∈J, F i j x‖^2)≤16*∑ j∈J, b j := by
  classical
  have hh := finite_energy_schur (volume : Measure ℝ)
    (fun (i : I) (j : J) => F i.val j.val)
    (fun i j => hF i.val i.property j.val j.property)
    (fun (i : I) (j : J) => lineScaleWeight i.val j.val)
    (fun i j => lineScaleWeight_pos i.val j.val)
    (fun j : J => b j.val) (fun j => hb j.val j.property)
    (R:=4) (C:=4) (by norm_num)
    (fun i => by
      rw [Finset.sum_coe_sort J (fun j => lineScaleWeight i.val j)]
      exact lineScaleWeight_row J i.val)
    (fun j => by
      rw [Finset.sum_coe_sort I (fun i => lineScaleWeight i j.val)]
      exact lineScaleWeight_col I j.val)
    (fun i j => hbound i.val i.property j.val j.property)
  change (∑ i : I, ∫ x, ‖∑ j : J, F i.val j.val x‖^2)≤
    4*4*(∑ j : J, b j.val) at hh
  have he (i : ℤ) : (∫ x, ‖∑ j : J, F i j.val x‖^2)=
      ∫ x, ‖∑ j∈J, F i j x‖^2 := by
    congr 1
    funext x
    rw [Finset.sum_coe_sort J (fun j => F i j x)]
  simp_rw [he] at hh
  rw [Finset.sum_coe_sort I (fun i => ∫ x, ‖∑ j∈J, F i j x‖^2),
    Finset.sum_coe_sort J b] at hh
  norm_num at hh
  exact hh

end LipschitzHilbert

end

end OAI
