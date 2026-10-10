import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.Basic

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

@[simp] theorem coupling_self {n : ℕ} (J : Disorder n) (i : Fin n) : coupling J i i = 0 := by
  simp [coupling]

theorem coupling_comm {n : ℕ} (J : Disorder n) (i j : Fin n) : coupling J i j = coupling J j i := by
  rcases lt_trichotomy i j with h | h | h
  · simp [coupling,h,not_lt_of_ge h.le]
  · subst j; rfl
  · simp [coupling,h,not_lt_of_ge h.le]

def interactionSum {n : ℕ} (J : Disorder n) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, coupling J i j*v i*v j

theorem interactionSum_eq_edges {n : ℕ} (J : Disorder n) (v : Fin n → ℝ) :
    interactionSum J v = 2*∑ e : Edge n, J e*v e.val.1*v e.val.2 := by
  have hE : (∑ e : Edge n, J e*v e.val.1*v e.val.2) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then coupling J i j*v i*v j else 0 := by
    calc
      _ = ∑ e : Edge n, coupling J e.val.1 e.val.2*v e.val.1*v e.val.2 := by
        apply Finset.sum_congr rfl
        intro e _
        simp only [coupling,dite_eq_left e.property]
      _ = _ := sum_edges (fun p => coupling J p.1 p.2*v p.1*v p.2)
  have ht (i j : Fin n) : coupling J i j*v i*v j =
      (if i < j then coupling J i j*v i*v j else 0)+
      (if j < i then coupling J i j*v i*v j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp only [h,not_lt_of_ge h.le,ite_true,ite_false,add_zero]
    · subst j; simp
    · simp only [h,not_lt_of_ge h.le,ite_true,ite_false,zero_add]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
    (fun j _ => Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun k _ => ht j k))
  unfold interactionSum
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  have hswap : (∑ i : Fin n, ∑ j : Fin n, if j < i then coupling J i j*v i*v j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then coupling J i j*v i*v j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [coupling_comm J j i]
    split_ifs <;> ring
  rw [hswap,← hE]
  ring

theorem hamiltonian_eq_interactionSum {n : ℕ} (J : Disorder n) (x : Config n) :
    hamiltonian J x = interactionSum J (fun i => spin (x i))/(2*Real.sqrt n) := by
  rw [interactionSum_eq_edges]
  unfold hamiltonian
  ring

theorem interactionSum_update {n : ℕ} (J : Disorder n) (v : Fin n → ℝ) (i : Fin n) (r : ℝ) :
    interactionSum J (Function.update v i r) = interactionSum J v+
      2*(r-v i)*(∑ j, coupling J i j*v j) := by
  classical
  have ht (j k : Fin n) : coupling J j k*Function.update v i r j*Function.update v i r k =
      coupling J j k*v j*v k+
      (if j=i then coupling J i k*(r-v i)*v k else 0)+
      (if k=i then coupling J j i*v j*(r-v i) else 0) := by
    by_cases hj : j=i <;> by_cases hk : k=i
    · subst j; subst k; simp
    · subst j; simp only [Function.update_self,Function.update_of_ne hk,ite_true,ite_eq_right hk,add_zero]; ring
    · subst k; simp only [Function.update_self,Function.update_of_ne hj,ite_true,ite_eq_right hj,add_zero]; ring
    · simp only [Function.update_of_ne hj,Function.update_of_ne hk,ite_false,hj,hk,add_zero]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
    (fun j _ => Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun k _ => ht j k))
  unfold interactionSum
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  have H1 : (∑ j : Fin n, ∑ k : Fin n, if j=i then coupling J i k*(r-v i)*v k else 0) =
      (r-v i)*(∑ k, coupling J i k*v k) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have H2 : (∑ j : Fin n, ∑ k : Fin n, if k=i then coupling J j i*v j*(r-v i) else 0) =
      (r-v i)*(∑ j, coupling J i j*v j) := by
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [coupling_comm J j i]
    ring
  rw [H1,H2]
  ring

theorem hamiltonian_update {n : ℕ} (J : Disorder n) (x : Config n) (i : Fin n) (b : Bool) :
    hamiltonian J (Function.update x i b) = hamiltonian J x+
      (spin b-spin (x i))*localField J x i := by
  have hu : (fun j => spin (Function.update x i b j)) =
      Function.update (fun j => spin (x j)) i (spin b) := by
    funext j
    by_cases h : j=i
    · subst j; simp
    · simp [Function.update_of_ne h]
  rw [hamiltonian_eq_interactionSum,hu,interactionSum_update,hamiltonian_eq_interactionSum]
  unfold localField
  ring

theorem localField_update {n : ℕ} (J : Disorder n) (x : Config n) (i : Fin n) (b : Bool) :
    localField J (Function.update x i b) i = localField J x i := by
  unfold localField
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j=i
  · subst j; simp
  · simp only [Function.update_of_ne h]

end SK.Analytic

end
end

end

end OAI
