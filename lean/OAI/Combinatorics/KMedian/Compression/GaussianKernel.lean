import Mathlib

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

def residual {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1)) :
    Fin r → Fin n → ℚ :=
  fun i j => A i.succ (p.succAbove j) - A 0 (p.succAbove j)/A 0 p*A i.succ p

def lift {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1))
    (z : Fin n → ℚ) : Fin (n+1) → ℚ :=
  p.insertNth (-(∑ j, A 0 (p.succAbove j)/A 0 p*z j)) z

theorem lift_nonzero {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1))
    (z : Fin n → ℚ) (hz : ∃ j, z j ≠ 0) : ∃ j, lift A p z j ≠ 0 := by
  obtain ⟨j,hj⟩ := hz
  exact ⟨p.succAbove j, by simpa only [lift,Fin.insertNth_apply_succAbove] using hj⟩

theorem lift_kernel {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1))
    (hp : A 0 p ≠ 0) (z : Fin n → ℚ)
    (hz : ∀ i, ∑ j, residual A p i j*z j=0) :
    ∀ i, ∑ j, A i j*lift A p z j=0 := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Fin.sum_univ_succAbove _ p]
    simp only [lift,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,mul_neg]
    have hs : A 0 p*(∑ j, A 0 (p.succAbove j)/A 0 p*z j)=
        ∑ j, A 0 (p.succAbove j)*z j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      field_simp
    rw [hs,neg_add_cancel]
  · rw [Fin.sum_univ_succAbove _ p]
    simp only [lift,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
    have hh := hz i
    simp only [residual,sub_mul,sum_sub_distrib] at hh
    have he : (∑ j, A 0 (p.succAbove j)/A 0 p*A i.succ p*z j)=
        A i.succ p*(∑ j, A 0 (p.succAbove j)/A 0 p*z j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    rw [he] at hh
    linarith

def kernel : (r n : ℕ) → (Fin r → Fin n → ℚ) → Fin n → ℚ
  | 0, _, _ => fun j => if j.val=0 then 1 else 0
  | _+1, 0, _ => Fin.elim0
  | r+1, n+1, A =>
    if h : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty then
      let p := (univ.filter (fun j => A 0 j ≠ 0)).min' h
      lift A p (kernel r n (residual A p))
    else kernel r (n+1) (fun i j => A i.succ j)

theorem kernel_spec (r n : ℕ) (A : Fin r → Fin n → ℚ) (hn : r < n) :
    (∃ j, kernel r n A j ≠ 0) ∧ (∀ i, ∑ j, A i j*kernel r n A j=0) := by
  induction r generalizing n with
  | zero =>
    have hn0 : 0 < n := hn
    refine ⟨⟨⟨0,hn0⟩,?_⟩,fun i => Fin.elim0 i⟩
    simp only [kernel,ite_true,ne_eq,one_ne_zero,not_false_eq_true]
  | succ r ih =>
    cases n with
    | zero => omega
    | succ n =>
      by_cases hh : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty
      · let p := (univ.filter (fun j => A 0 j ≠ 0)).min' hh
        have hp : A 0 p ≠ 0 := (mem_filter.mp (min'_mem _ hh)).2
        have hi := ih n (residual A p) (by omega)
        change (∃ j, (if h : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty then
            lift A ((univ.filter (fun j => A 0 j ≠ 0)).min' h)
              (kernel r n (residual A ((univ.filter (fun j => A 0 j ≠ 0)).min' h)))
            else kernel r (n+1) (fun i j => A i.succ j)) j ≠ 0) ∧ _
        simp only [kernel,dite_eq_left hh]
        exact ⟨lift_nonzero A p _ hi.1,lift_kernel A p hp _ hi.2⟩
      · have hzero : ∀ j, A 0 j=0 := by
          intro j
          by_contra hj
          exact hh ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩⟩
        have hi := ih (n+1) (fun i j => A i.succ j) (by omega)
        have he : kernel (r+1) (n+1) A=kernel r (n+1) (fun i j => A i.succ j) := by
          rw [kernel,dite_eq_right hh]
        rw [he]
        refine ⟨hi.1,?_⟩
        intro i
        refine Fin.cases ?_ (fun i => hi.2 i) i
        simp only [hzero,zero_mul,sum_const_zero]

end MetricKMedian.Gaussian

end OAI
