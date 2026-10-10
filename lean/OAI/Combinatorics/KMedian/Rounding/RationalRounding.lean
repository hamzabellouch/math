import Mathlib
import OAI.Combinatorics.KMedian.Rounding.UniformSplitRounding
import OAI.Combinatorics.KMedian.Geometry.RationalSplitting
import OAI.Combinatorics.KMedian.Geometry.NearestFractional

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset

theorem uniform_rational_rounding {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℕ, ∀ (I J X : Type) [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] [Nonempty J] [PseudoMetricSpace X],
      ∀ (y : I → ℚ) (x : J → I → ℚ) (d : J → I → ℚ)
        (client : J → X) (location : I → X),
        (∀ i, 0 < y i) → (∀ i, y i ≤ 1) →
        (∀ j i, 0 ≤ x j i ∧ x j i ≤ y i) → (∀ j, ∑ i, x j i=1) →
        (∀ j i, (d j i:ℝ)=dist (client j) (location i)) →
        ∃ O : Finset I, ∃ a : J → I,
          (∀ j, a j ∈ O) ∧ O.Nonempty ∧ (O.card:ℝ) ≤ (∑ i, (y i:ℝ))+(C:ℝ) ∧
          (∑ j, dist (client j) (location (a j))) ≤
            (1+2/Real.exp 1+ε)*(∑ j, ∑ i, (x j i:ℝ)*dist (client j) (location i)) := by
  obtain ⟨C,hC⟩ := uniform_split_rounding hε
  refine ⟨C,?_⟩
  intro I J X _ _ _ _ _ _ y x d client location hy hy1 hx hxsum hd
  have hm : (1:ℚ) ≤ ∑ i, y i := by
    obtain ⟨j⟩ := ‹Nonempty J›
    rw [← hxsum j]
    exact sum_le_sum (fun i _ => (hx j i).2)
  have hex : ∀ j, ∃ z : I → ℚ,
      (∀ i, 0 ≤ z i ∧ z i ≤ y i) ∧ (∑ i, z i)=1 ∧
      (∀ i a, 0 < z i → z a < y a → d j i ≤ d j a) ∧
      (∑ i, z i*d j i) ≤ ∑ i, x j i*d j i := by
    intro j
    obtain ⟨z,_,hz,hzs,hzo⟩ := nearest_fractional univ y (d j) 1
      (fun i _ => (hy i).le) (by norm_num) hm
    refine ⟨z,fun i => hz i (mem_univ _),hzs,fun i a => hzo i (mem_univ _) a (mem_univ _),?_⟩
    exact nearest_fractional_cheaper univ y (d j) z (x j) (by norm_num)
      (fun i hi => (hz i hi).1) (fun i _ => hx j i) hzs (hxsum j) hzo
  choose z hz hzs hzo hzc using hex
  let P := RationalSplitting.Piece y z
  let : DecidableEq P := Classical.decEq P
  let loc : P → X := fun a => location a.1
  let w : P → ℝ := fun a => (RationalSplitting.weight y z a:ℝ)
  let Fj : J → Finset P := RationalSplitting.assignment y z
  let v : J → ℝ := fun j => ∑ i, (z j i:ℝ)*dist (client j) (location i)
  have hw : ∀ a, 0 < w a := by
    intro a
    dsimp only [w]
    exact_mod_cast RationalSplitting.weight_pos y z a
  have hw1 : ∀ a, w a ≤ 1 := by
    intro a
    have hh := (RationalSplitting.weight_le y z (fun j i => (hz j i).2) a).trans (hy1 a.1)
    dsimp only [w]
    exact_mod_cast hh
  have hunit : ∀ j, ∑ a ∈ Fj j, w a=1 := by
    intro j
    have hh := (RationalSplitting.sum_assignment y z (fun j i => (hz j i).1) j).trans (hzs j)
    dsimp only [Fj,w]
    exact_mod_cast hh
  have hcost : ∀ j, ∑ a ∈ Fj j, w a*dist (client j) (loc a)=v j := by
    intro j
    exact RationalSplitting.cost_assignment y z (fun j i => (hz j i).1) j
      (fun i => dist (client j) (location i))
  have hnear : ∀ j, ∀ a ∈ Fj j, ∀ b ∉ Fj j, dist (client j) (loc a) ≤ dist (client j) (loc b) := by
    intro j a ha b hb
    apply RationalSplitting.nearest_assignment y z (fun j i => (hz j i).2)
      (fun j i => dist (client j) (location i)) ?_ j a ha b hb
    intro j i b hi hb
    rw [← hd j i,← hd j b]
    exact_mod_cast hzo j i b hi hb
  obtain ⟨O,a,ha,hO,hcount,hconn⟩ := hC P J X Fj w client loc v hw hw1 hunit hcost hnear
  refine ⟨O.image Sigma.fst,fun j => (a j).1,fun j => mem_image.mpr ⟨a j,ha j,rfl⟩,
    hO.image _,?_,hconn.trans ?_⟩
  · have hc : ((O.image Sigma.fst).card:ℝ) ≤ (O.card:ℝ) := by exact_mod_cast card_image_le
    apply hc.trans (hcount.trans_eq ?_)
    congr 1
    dsimp only [w]
    exact_mod_cast RationalSplitting.sum_weight y z hy (fun j i => (hz j i).2)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sum_le_sum
    intro j _
    simp only [v,← hd]
    exact_mod_cast hzc j

end MetricKMedian.Preparation
end
end

end OAI
