import Mathlib
import OAI.Combinatorics.KMedian.Compression.GaussianKernel

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

def IsCircuit {r n : ℕ} (A : Fin r → Fin n → ℚ) (z : Fin n → ℚ) : Prop :=
  ∀ v : Fin n → ℚ, (∀ j, z j=0 → v j=0) → (∀ i, ∑ j, A i j*v j=0) →
    ∃ t : ℚ, ∀ j, v j=t*z j

theorem lift_eq_of_kernel {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (hp : A 0 p ≠ 0) (v : Fin (n+1) → ℚ)
    (h0 : ∑ j, A 0 j*v j=0) :
    v=lift A p (fun j => v (p.succAbove j)) := by
  have he : v p= -(∑ j, A 0 (p.succAbove j)/A 0 p*v (p.succAbove j)) := by
    rw [Fin.sum_univ_succAbove _ p] at h0
    have hs : A 0 p*(∑ j, A 0 (p.succAbove j)/A 0 p*v (p.succAbove j))=
        ∑ j, A 0 (p.succAbove j)*v (p.succAbove j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      field_simp
    apply (mul_left_cancel₀ hp)
    rw [mul_neg,hs]
    linarith
  funext j
  by_cases hj : j=p
  · subst j
    simpa only [lift,Fin.insertNth_apply_same] using he
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [lift,Fin.insertNth_apply_succAbove]

theorem residual_kernel {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (hp : A 0 p ≠ 0) (v : Fin (n+1) → ℚ)
    (hv : ∀ i, ∑ j, A i j*v j=0) :
    ∀ i, ∑ j, residual A p i j*v (p.succAbove j)=0 := by
  have he := lift_eq_of_kernel A p hp v (hv 0)
  intro i
  have hi := hv i.succ
  rw [Fin.sum_univ_succAbove _ p] at hi
  have hep := congrFun he p
  simp only [lift,Fin.insertNth_apply_same] at hep
  rw [hep] at hi
  simp only [residual,sub_mul,sum_sub_distrib]
  have hs : (∑ j, A 0 (p.succAbove j)/A 0 p*A i.succ p*v (p.succAbove j))=
      A i.succ p*(∑ j, A 0 (p.succAbove j)/A 0 p*v (p.succAbove j)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  rw [hs]
  linarith

theorem lift_smul {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (z : Fin n → ℚ) (t : ℚ) :
    lift A p (fun j => t*z j)=fun j => t*lift A p z j := by
  funext j
  by_cases hj : j=p
  · subst j
    simp only [lift,Fin.insertNth_apply_same]
    rw [mul_neg, mul_sum]
    congr 1
    apply sum_congr rfl
    intro i _
    ring
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [lift,Fin.insertNth_apply_succAbove]

theorem lift_circuit {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (hp : A 0 p ≠ 0) (z : Fin n → ℚ)
    (hz : IsCircuit (residual A p) z) : IsCircuit A (lift A p z) := by
  intro v hs hv
  have hsub : ∀ j, z j=0 → v (p.succAbove j)=0 := by
    intro j hj
    apply hs
    simpa only [lift,Fin.insertNth_apply_succAbove] using hj
  obtain ⟨t,ht⟩ := hz (fun j => v (p.succAbove j)) hsub (residual_kernel A p hp v hv)
  refine ⟨t,?_⟩
  have he := lift_eq_of_kernel A p hp v (hv 0)
  rw [show (fun j => v (p.succAbove j))=(fun j => t*z j) from funext ht,lift_smul] at he
  exact congrFun he

theorem kernel_circuit (r n : ℕ) (A : Fin r → Fin n → ℚ) (hn : r < n) :
    (∃ j, kernel r n A j=1) ∧ IsCircuit A (kernel r n A) := by
  induction r generalizing n with
  | zero =>
    let j0 : Fin n := ⟨0,hn⟩
    refine ⟨⟨j0,by simp only [kernel,j0,ite_true]⟩,?_⟩
    intro v hs _
    refine ⟨v j0,?_⟩
    intro j
    by_cases hj : j.val=0
    · have he : j=j0 := Fin.ext hj
      subst j
      simp only [kernel,j0,ite_true,mul_one]
    · have hh := hs j (by simp only [kernel,ite_eq_right hj])
      simp only [kernel,ite_eq_right hj,mul_zero,hh]
  | succ r ih =>
    cases n with
    | zero => omega
    | succ n =>
      by_cases hh : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty
      · let p := (univ.filter (fun j => A 0 j ≠ 0)).min' hh
        have hp : A 0 p ≠ 0 := (mem_filter.mp (min'_mem _ hh)).2
        obtain ⟨⟨j,hj⟩,hc⟩ := ih n (residual A p) (by omega)
        have he : kernel (r+1) (n+1) A=lift A p (kernel r n (residual A p)) := by
          rw [kernel,dite_eq_left hh]
        rw [he]
        refine ⟨⟨p.succAbove j,?_⟩,lift_circuit A p hp _ hc⟩
        simpa only [lift,Fin.insertNth_apply_succAbove] using hj
      · have hi := ih (n+1) (fun i j => A i.succ j) (by omega)
        have he : kernel (r+1) (n+1) A=kernel r (n+1) (fun i j => A i.succ j) := by
          rw [kernel,dite_eq_right hh]
        rw [he]
        refine ⟨hi.1,?_⟩
        intro v hs hv
        exact hi.2 v hs (fun i => hv i.succ)

end MetricKMedian.Gaussian

end OAI
