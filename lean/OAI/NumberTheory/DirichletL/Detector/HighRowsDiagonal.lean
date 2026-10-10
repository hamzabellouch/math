import OAI.NumberTheory.DirichletL.Detector.LocalSummation

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeEuler

theorem diagonal_recurrence_eq (f : ℕ→ℕ→ℂ) (R : ℂ)
    (hstep : ∀ r m,f (r+1) (m+1)=R*f r m) (hz : ∀ r,f (r+1) 0=0) :
    ∀ r m,f r m=if r≤m then R^r*f 0 (m-r) else 0 := by
  intro r
  induction r with
  | zero => intro m; simp
  | succ r ih =>
    intro m
    cases m with
    | zero => simp [hz]
    | succ m =>
      rw [hstep,ih]
      by_cases h : r≤m
      · simp only [h,ite_true,Nat.succ_le_succ_iff,Nat.succ_sub_succ_eq_sub,pow_succ]
        ring
      · simp only [h,ite_false,Nat.succ_le_succ_iff,mul_zero]

theorem diagonal_recurrence_inner_hasSum (f : ℕ→ℕ→ℂ) (R : ℂ)
    (hstep : ∀ r m,f (r+1) (m+1)=R*f r m) (hz : ∀ r,f (r+1) 0=0)
    (hs : Summable (f 0)) (r : ℕ) : HasSum (f r) (R^r*∑' m,f 0 m) := by
  have he := diagonal_recurrence_eq f R hstep hz
  have htail : HasSum (fun m=>f r (m+r)) (R^r*∑' m,f 0 m) := by
    convert hs.hasSum.mul_left (R^r) using 1
    funext m
    rw [he,ite_eq_left (Nat.le_add_left r m),Nat.add_sub_cancel]
  have hzero : (∑ m∈Finset.range r,f r m)=0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [he,ite_eq_right (by have := Finset.mem_range.mp hm; omega)]
  simpa only [hzero,zero_add] using htail.sum_range_add

theorem diagonal_recurrence_hasSum (f : ℕ→ℕ→ℂ) (R : ℂ)
    (hstep : ∀ r m,f (r+1) (m+1)=R*f r m) (hz : ∀ r,f (r+1) 0=0)
    (hs : Summable (f 0)) (hR : ‖R‖<1) :
    HasSum (fun r=>∑' m,f r m) ((∑' m,f 0 m)/(1-R)) := by
  have he (r : ℕ) := (diagonal_recurrence_inner_hasSum f R hstep hz hs r).tsum_eq
  have hg : HasSum (fun r=>R^r*(∑' m,f 0 m)) ((∑' m,f 0 m)/(1-R)) := by
    simpa only [div_eq_mul_inv,mul_comm] using
      (hasSum_geometric_of_norm_lt_one hR).mul_right (∑' m,f 0 m)
  convert hg using 1
  funext r
  exact he r

end SevenEighths.ProbeEuler
end

end OAI
