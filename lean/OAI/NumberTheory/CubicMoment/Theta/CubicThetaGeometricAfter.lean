import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGeometricNumerics

namespace OAI

/-! Exact sums of the two truncated geometric majorants. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubic_geometric_after {q : ℝ} (hq : |q|<1) (C : ℝ) (R : ℕ) :
    HasSum (fun k : ℕ => if R<k then C*q^k else 0)
      (C*q^(R+1)*(1-q)⁻¹) := by
  let f := fun k : ℕ => if R<k then C*q^k else 0
  have hs : HasSum (fun n => f (n+(R+1))) (C*q^(R+1)*(1-q)⁻¹) := by
    convert (hasSum_geometric_of_abs_lt_one hq).mul_left (C*q^(R+1)) using 1
    funext n
    simp only [f,ite_eq_left (by omega : R<n+(R+1)),pow_add]
    ring
  have hh := hs.sum_range_add (f:=f)
  have hz : ∑ k∈Finset.range (R+1),f k=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    simp only [f,ite_eq_right (by omega : ¬R<k)]
  rw [hz,zero_add] at hh
  exact hh

lemma cubic_primary_geometric_after :
    Summable (fun k : ℕ => if 3<k then (9/4:ℝ)*(2/15:ℝ)^k else 0) ∧
      (∑' k : ℕ,if 3<k then (9/4:ℝ)*(2/15:ℝ)^k else 0)<1/1000 := by
  have h := cubic_geometric_after (by norm_num : |(2/15:ℝ)|<1) (9/4:ℝ) 3
  refine ⟨h.summable,?_⟩
  rw [h.tsum_eq]
  norm_num

lemma cubic_ramified_geometric_after :
    Summable (fun k : ℕ => if 2<k then (9/16:ℝ)*(1/25:ℝ)^k else 0) ∧
      (∑' k : ℕ,if 2<k then (9/16:ℝ)*(1/25:ℝ)^k else 0)<1/10000 := by
  have h := cubic_geometric_after (by norm_num : |(1/25:ℝ)|<1) (9/16:ℝ) 2
  refine ⟨h.summable,?_⟩
  rw [h.tsum_eq]
  norm_num

end CubicFirstMoment

end

end OAI
