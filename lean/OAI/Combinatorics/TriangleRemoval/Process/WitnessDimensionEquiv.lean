import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.WitnessDimensions
import OAI.Combinatorics.TriangleRemoval.Asymptotics.EndpointMarksExponential

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

def witnessDimensionEquiv (R d : ℕ) : WitnessDimensions R d ≃ Fin (2*d+1) where
  toFun q := q.val.2
  invFun s := ⟨(⟨R+s.val,by have h := s.isLt; omega⟩,s),rfl⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact q.property.symm
    · rfl
  right_inv _ := rfl

lemma witness_dimensions_sum {R d : ℕ} (f : ℕ → ℝ) :
    (∑ q : WitnessDimensions R d, f q.val.2.val) =
      ∑ s ∈ Finset.range (2*d+1), f s := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (witnessDimensionEquiv R d) _ _ (fun _ => rfl)

lemma finite_exp_series_le {x : ℝ} (hx : 0 ≤ x) (L : ℕ) :
    (∑ s ∈ Finset.range L, x^s/(s.factorial : ℝ)) ≤ Real.exp x := by
  exact sum_le_hasSum _ (fun s _ => by positivity) (witness_exp_series x)

theorem witness_dimensions_weight_sum {R d r : ℕ} {m D C x : ℝ}
    (hR : R ≤ 4) (hm : 0 ≤ m) (hD : 0 ≤ D) (hC : 0 ≤ C) (hx : 0 ≤ x) :
    (∑ q : WitnessDimensions R d,
      64*(q.val.1.val^2*6^q.val.2.val : ℕ)*
        ((4*m)^r*(2*D)^q.val.2.val/D^50)*
          (C^3*((3*x)^q.val.2.val/(q.val.2.val.factorial : ℝ)))) ≤
      (2048*(4*m)^r*C^3/D^50)*Real.exp (45*D*x) := by
  have hnon : 0 ≤ (2048*(4*m)^r*C^3/D^50) := by positivity
  calc
    _ ≤ ∑ q : WitnessDimensions R d,
        (2048*(4*m)^r*C^3/D^50)*((45*D*x)^q.val.2.val/(q.val.2.val.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro q _
      have hmark := pattern_marks_exponential (s := q.val.2.val) hR
      rw [← q.property] at hmark
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmark (by norm_num : (0 : ℝ) ≤ 64))
          (show 0 ≤ (4*m)^r*(2*D)^q.val.2.val/D^50 by positivity))
        (show 0 ≤ C^3*((3*x)^q.val.2.val/(q.val.2.val.factorial : ℝ)) by positivity)
      apply hh.trans_eq
      have hp : (15/2 : ℝ)^q.val.2.val*(2*D)^q.val.2.val*(3*x)^q.val.2.val =
          (45*D*x)^q.val.2.val := by
        rw [← mul_pow,← mul_pow]
        congr 1
        ring
      calc
        _ = (2048*(4*m)^r*C^3/D^50)*
            (((15/2 : ℝ)^q.val.2.val*(2*D)^q.val.2.val*(3*x)^q.val.2.val)/
              (q.val.2.val.factorial : ℝ)) := by ring
        _ = _ := by rw [hp]
    _ = (2048*(4*m)^r*C^3/D^50)*
        (∑ s ∈ Finset.range (2*d+1), (45*D*x)^s/(s.factorial : ℝ)) := by
      rw [← Finset.mul_sum, witness_dimensions_sum (R := R) (d := d)
        (fun s => (45*D*x)^s/(s.factorial : ℝ))]
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_exp_series_le (by positivity) _) hnon

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
