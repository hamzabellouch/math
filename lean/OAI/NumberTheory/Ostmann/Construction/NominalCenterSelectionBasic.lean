import OAI.NumberTheory.Ostmann.Construction.BalancedCenterSelection
import OAI.NumberTheory.Ostmann.Construction.NominalTotalsScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

structure NominalCenterArray (d : Decomposition) (k : ℕ) (L J tb : ℝ) (w : Fin k → ℝ) where
  top : Fin 3 → ℤ
  comp : Fin k → Fin 2 → ℤ
  top_sum : ∑i,top i = ⌊(J-2*tb)/2⌋
  comp_sum : ∀j,∑i,comp j i = ⌊w j/2⌋
  top_near : ∀i,|(top i:ℝ)-(⌊(J-2*tb)/2⌋:ℝ)/3|≤favorableBlockWidth L/1000
  comp_near : ∀j i,|(comp j i:ℝ)-(⌊w j/2⌋:ℝ)/2|≤favorableBlockWidth L/1000
  top_balanced : ∀i,BalancedCellAfterTwo d (top i)
  comp_balanced : ∀j i,BalancedCellAfterTwo d (comp j i)

lemma floor_half_total_bounds {h v b : ℝ} (hh : 16≤h)
    (hvlo : h/4≤v) (hvhi : v≤b*h) :
    h/16≤(⌊v/2⌋:ℝ) ∧ (⌊v/2⌋:ℝ)≤b*h/2 := by
  have hlo := Int.lt_floor_add_one (v/2)
  have hhi := Int.floor_le (v/2)
  constructor <;> linarith

lemma doubled_floor_half_error (v : ℝ) : |2*(⌊v/2⌋:ℝ)-v|<2 := by
  have hlo := Int.lt_floor_add_one (v/2)
  have hhi := Int.floor_le (v/2)
  apply abs_lt.mpr
  constructor <;> linarith

lemma center_near_nominal {h v a n : ℝ} (hh : 1000≤h) (hn : 1≤n)
    (ha : |a-(⌊v/2⌋:ℝ)/n|≤h/1000) : |a-v/(2*n)|≤h/500 := by
  have hnp : 0<n := by linarith
  have hf : |(⌊v/2⌋:ℝ)-v/2|≤1 := by
    have hlo := Int.lt_floor_add_one (v/2)
    have hhi := Int.floor_le (v/2)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have he : a-v/(2*n) = (a-(⌊v/2⌋:ℝ)/n)+((⌊v/2⌋:ℝ)-v/2)/n := by ring
  rw [he]
  calc
    _ ≤ |a-(⌊v/2⌋:ℝ)/n|+|((⌊v/2⌋:ℝ)-v/2)/n| := abs_add_le _ _
    _ ≤ h/1000+1/n := by
      rw [abs_div,abs_of_pos hnp]
      exact add_le_add ha (div_le_div_of_nonneg_right hf hnp.le)
    _ ≤ h/500 := by
      have : 1/n≤1 := (div_le_one hnp).mpr hn
      linarith

namespace NominalCenterArray
variable {d : Decomposition} {k : ℕ} {L J tb : ℝ} {w : Fin k → ℝ}

theorem top_doubled_error (C : NominalCenterArray d k L J tb w) :
    |2*(∑i,(C.top i:ℝ))-(J-2*tb)|<2 := by
  have hs : (∑i,(C.top i:ℝ))=(⌊(J-2*tb)/2⌋:ℝ) := by exact_mod_cast C.top_sum
  rw [hs]
  exact doubled_floor_half_error _

theorem comp_doubled_error (C : NominalCenterArray d k L J tb w) (j : Fin k) :
    |2*(∑i,(C.comp j i:ℝ))-w j|<2 := by
  have hs : (∑i,(C.comp j i:ℝ))=(⌊w j/2⌋:ℝ) := by exact_mod_cast C.comp_sum j
  rw [hs]
  exact doubled_floor_half_error _

theorem top_nominal_near (C : NominalCenterArray d k L J tb w)
    (hh : 1000≤favorableBlockWidth L) (i : Fin 3) :
    |(C.top i:ℝ)-(J-2*tb)/6|≤favorableBlockWidth L/500 := by
  simpa only [show (2:ℝ)*3=6 by norm_num] using center_near_nominal hh (by norm_num : (1:ℝ)≤3) (C.top_near i)

theorem comp_nominal_near (C : NominalCenterArray d k L J tb w)
    (hh : 1000≤favorableBlockWidth L) (j : Fin k) (i : Fin 2) :
    |(C.comp j i:ℝ)-w j/4|≤favorableBlockWidth L/500 := by
  simpa only [show (2:ℝ)*2=4 by norm_num] using center_near_nominal hh (by norm_num : (1:ℝ)≤2) (C.comp_near j i)

end NominalCenterArray
end Ostmann.Construction

end

end OAI
