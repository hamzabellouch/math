import OAI.MeasureTheory.Falconer.Geometry.ScalarNetAmplification

namespace OAI

/-! Repeated finite sum-product amplification of a power-scale interval
net, with its exact error recurrence. -/
namespace Falconer
open scoped Pointwise

 theorem scalarCoefficientClosure_step (S : Finset ℝ) (n : ℕ) :
    scalarCoefficientClosure S n ⊆ scalarCoefficientClosure S (n+1) := by
  intro x hx
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)

 theorem scalarCoefficientClosure_sum_product (S : Finset ℝ) (n : ℕ) :
    scalarCoefficientClosure S n+scalarCoefficientClosure S n*scalarCoefficientClosure S n ⊆
      scalarCoefficientClosure S (n+2) := by
  intro x hx
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
  have ha' := scalarCoefficientClosure_step S n ha
  have hb' : b ∈ scalarCoefficientClosure S (n+1) :=
    Finset.mem_union_right _ (Finset.mem_union_right _ hb)
  exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.add_mem_add ha' hb'))

 theorem scalarCoefficientClosure_zero (S : Finset ℝ) (hzero : 0 ∈ S) (n : ℕ) :
    0 ∈ scalarCoefficientClosure S n := by
  induction n with
  | zero => exact hzero
  | succ n ih => exact scalarCoefficientClosure_step S n ih

def scalarNetError (η : ℝ) : ℕ → ℝ
  | 0 => η
  | n+1 => 5*(scalarNetError η n)^2

 theorem scalarNetError_bounds {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1/8) (n : ℕ) :
    0 < scalarNetError η n ∧ scalarNetError η n ≤ η := by
  induction n with
  | zero => exact ⟨hη,le_rfl⟩
  | succ n ih =>
    refine ⟨mul_pos (by norm_num : (0 : ℝ) < 5) (sq_pos_of_pos ih.1),?_⟩
    have he : 5*(scalarNetError η n)^2 ≤ scalarNetError η n := by nlinarith [ih.2]
    exact he.trans ih.2

 theorem scalarNetError_formula (η : ℝ) (n : ℕ) :
    scalarNetError η n = (5*η)^(2^n)/5 := by
  induction n with
  | zero => simp [scalarNetError]
  | succ n ih =>
    rw [scalarNetError,ih,show (2 : ℕ)^(n+1) = 2^n*2 by rw [pow_succ],pow_mul]
    ring

 theorem scalar_interval_net_iterate {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1/8)
    (S : Finset ℝ) (hzero : 0 ∈ S)
    (hnet : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∃ a ∈ S, |x-a| ≤ η) (n : ℕ) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∃ a ∈ scalarCoefficientClosure S (2*n),
      |x-a| ≤ scalarNetError η n := by
  induction n with
  | zero => simpa only [Nat.mul_zero,scalarCoefficientClosure,scalarNetError] using hnet
  | succ n ih =>
    intro x hx0 hx1
    obtain ⟨a,ha,hea⟩ := scalar_interval_net_amplify (scalarNetError_bounds hη hη1 n).1
      ((scalarNetError_bounds hη hη1 n).2.trans hη1) (scalarCoefficientClosure S (2*n))
      (scalarCoefficientClosure_zero S hzero _) ih x hx0 hx1
    refine ⟨a,?_,hea⟩
    rw [show 2*(n+1) = 2*n+2 by omega]
    exact scalarCoefficientClosure_sum_product S (2*n) ha

end Falconer

end OAI
