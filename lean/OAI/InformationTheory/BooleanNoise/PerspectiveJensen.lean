import OAI.InformationTheory.BooleanNoise.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

universe u

namespace LeanBlast.CourtadeKumar

theorem weighted_perspective_jensen {ι : Type u} [Fintype ι]
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ioi 0) f)
    (p A H : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hA : ∀ i, 0 < A i)
    (hH : ∀ i, 0 < H i) (hS : 0 < ∑ i, p i * A i) :
    (∑ i, p i * A i) * f ((∑ i, p i * H i) / (∑ i, p i * A i)) ≤
      ∑ i, p i * A i * f (H i / A i) := by
  have hj := hf.map_centerMass_le
    (t := Finset.univ) (w := fun i => p i * A i) (p := fun i => H i / A i)
    (fun i _ => mul_nonneg (hp i) (hA i).le) hS (fun i _ => div_pos (hH i) (hA i))
  have heq : (∑ i, p i * A i * (H i / A i)) = ∑ i, p i * H i := by
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hA i).ne']
  simp only [Finset.centerMass, smul_eq_mul, Function.comp_apply] at hj
  rw [heq] at hj
  have hm := mul_le_mul_of_nonneg_left hj hS.le
  simp only [← mul_assoc, mul_inv_cancel₀ hS.ne', one_mul] at hm
  simpa [← div_eq_inv_mul, mul_assoc] using hm

theorem cubeAverage_perspective_jensen {n : ℕ}
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ioi 0) f)
    (A H : Cube n → ℝ) (hA : ∀ i, 0 < A i) (hH : ∀ i, 0 < H i) :
    cubeAverage A * f (cubeAverage H / cubeAverage A) ≤
      cubeAverage (fun i => A i * f (H i / A i)) := by
  have hc : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hs : 0 < ∑ i, ((2 : ℝ) ^ n)⁻¹ * A i :=
    Finset.sum_pos (fun i _ => mul_pos (inv_pos.mpr hc) (hA i)) Finset.univ_nonempty
  have h := weighted_perspective_jensen f hf (fun _ => ((2 : ℝ) ^ n)⁻¹)
    A H (fun _ => (inv_pos.mpr hc).le) hA hH hs
  have havg (g : Cube n → ℝ) :
      (∑ i, ((2 : ℝ) ^ n)⁻¹ * g i) = cubeAverage g := by
    rw [← Finset.mul_sum, cubeAverage, div_eq_mul_inv]
    ring
  simpa only [mul_assoc, havg] using h

end LeanBlast.CourtadeKumar

end

end OAI
