import Mathlib
import OAI.Analysis.HardSphere.Geometry.LiftedBadComponent

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice

lemma finite_scaled_box {h d : ℝ} (hh : 0 < h) (z : Vertex) :
    {w : Vertex | ∀ i, h * |(w i : ℝ)-z i| ≤ d}.Finite := by
  let M : ℤ := ⌈d/h⌉
  apply (Set.finite_Icc (fun i ↦ z i-M) (fun i ↦ z i+M)).subset
  intro w hw
  constructor
  · intro i
    have ht : |(w i : ℝ)-z i| ≤ (M : ℝ) :=
      (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hw i) |>.trans (Int.le_ceil _)
    have ht' := (abs_le.mp ht).1
    exact_mod_cast (show (z i : ℝ)-(M : ℝ) ≤ w i by linarith)
  · intro i
    have ht : |(w i : ℝ)-z i| ≤ (M : ℝ) :=
      (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hw i) |>.trans (Int.le_ceil _)
    have ht' := (abs_le.mp ht).2
    exact_mod_cast (show (w i : ℝ) ≤ z i+(M : ℝ) by linarith)

lemma infinite_component_has_exit {B : Set Vertex} {z : Vertex} {h : ℝ}
    (hh : 0 < h) (hinf : ¬ (liftedBadComponent B z).Finite) :
    ∃ w, withinReach starStep B z w ∧ ∃ i, (1:ℝ)/4 ≤ h * |(w i : ℝ)-z i| := by
  by_contra hn
  push Not at hn
  apply hinf
  apply (finite_scaled_box (d := (1:ℝ)/4) hh z).subset
  intro w hw i
  exact (hn w hw.2.2 i).le
end HardSphere.Lattice

end

end OAI
