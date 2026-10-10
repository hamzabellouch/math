import Mathlib
import OAI.Probability.SKBarriers.Dynamics.FiniteMarkovPath

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

structure FiniteLaw (X : Type*) [Fintype X] where
  weight : X → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  sum_one : ∑ x, weight x=1

namespace FiniteLaw
variable {X Y : Type*} [Fintype X] [Fintype Y]

def expect (P : FiniteLaw X) (f : X → ℝ) : ℝ := ∑ x, P.weight x*f x

def prob (P : FiniteLaw X) (E : X → Prop) : ℝ := P.expect (fun x => if E x then 1 else 0)

theorem expect_nonneg (P : FiniteLaw X) {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ P.expect f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (P.nonneg x) (hf x))

theorem expect_mono (P : FiniteLaw X) {f g : X → ℝ} (h : ∀ x, f x ≤ g x) : P.expect f ≤ P.expect g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (P.nonneg x))

@[simp] theorem expect_const (P : FiniteLaw X) (c : ℝ) : P.expect (fun _ => c)=c := by
  simp only [expect,← Finset.sum_mul,P.sum_one,one_mul]

@[simp] theorem expect_zero (P : FiniteLaw X) : P.expect (fun _ => 0)=0 := expect_const P 0

theorem expect_add (P : FiniteLaw X) (f g : X → ℝ) :
    P.expect (fun x => f x+g x)=P.expect f+P.expect g := by
  simp only [expect,mul_add,Finset.sum_add_distrib]

theorem expect_mul_const (P : FiniteLaw X) (f : X → ℝ) (c : ℝ) :
    P.expect (fun x => f x*c)=P.expect f*c := by
  simp only [expect,← mul_assoc,Finset.sum_mul]

theorem expect_const_mul (P : FiniteLaw X) (c : ℝ) (f : X → ℝ) :
    P.expect (fun x => c*f x)=c*P.expect f := by
  simp_rw [mul_comm c]
  exact expect_mul_const P f c

theorem expect_sum (P : FiniteLaw X) {I : Type*} [Fintype I] (f : I → X → ℝ) :
    P.expect (fun x => ∑ i, f i x)=∑ i, P.expect (f i) := by
  simp only [expect,Finset.mul_sum]
  exact Finset.sum_comm

theorem prob_nonneg (P : FiniteLaw X) (E : X → Prop) : 0 ≤ P.prob E :=
  P.expect_nonneg (fun x => by split_ifs <;> norm_num)

theorem prob_le_one (P : FiniteLaw X) (E : X → Prop) : P.prob E ≤ 1 := by
  rw [← P.expect_const 1]
  exact P.expect_mono (fun x => by split_ifs <;> norm_num)

theorem prob_mono (P : FiniteLaw X) {E F : X → Prop} (h : ∀ x, E x → F x) : P.prob E ≤ P.prob F := by
  apply P.expect_mono
  intro x
  by_cases he : E x
  · simp only [ite_eq_left he,ite_eq_left (h x he),le_refl]
  · simp only [ite_eq_right he]; split_ifs <;> norm_num

@[simp] theorem prob_true (P : FiniteLaw X) : P.prob (fun _ => True)=1 := by simp [prob]
@[simp] theorem prob_false (P : FiniteLaw X) : P.prob (fun _ => False)=0 := by simp [prob]

theorem prob_not (P : FiniteLaw X) (E : X → Prop) : P.prob (fun x => ¬E x)=1-P.prob E := by
  have he : P.prob E+P.prob (fun x => ¬E x)=1 := by
    rw [prob,prob,← expect_add]
    convert P.expect_const 1 using 2
    funext x
    by_cases h : E x <;> simp [h]
  linarith only [he]

theorem prob_or (P : FiniteLaw X) (E F : X → Prop) :
    P.prob (fun x => E x ∨ F x) ≤ P.prob E+P.prob F := by
  simp only [prob]
  rw [← expect_add]
  apply P.expect_mono
  intro x
  by_cases he : E x <;> by_cases hf : F x <;> simp [he,hf]

theorem prob_exists (P : FiniteLaw X) {I : Type*} [Fintype I] (E : I → X → Prop) :
    P.prob (fun x => ∃ i, E i x) ≤ ∑ i, P.prob (E i) := by
  simp only [prob]
  rw [← expect_sum]
  apply P.expect_mono
  intro x
  by_cases h : ∃ i, E i x
  · rw [ite_eq_left h]
    obtain ⟨i,hi⟩ := h
    exact (by simpa only [ite_eq_left hi] using
      (Finset.single_le_sum (fun j (_ : j∈Finset.univ) => show 0 ≤ (if E j x then (1:ℝ) else 0) by split_ifs <;> norm_num) (Finset.mem_univ i)))
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

def prod (P : FiniteLaw X) (Q : FiniteLaw Y) : FiniteLaw (X × Y) where
  weight z := P.weight z.1*Q.weight z.2
  nonneg z := mul_nonneg (P.nonneg _) (Q.nonneg _)
  sum_one := by simp only [Fintype.sum_prod_type,← Finset.mul_sum,Q.sum_one,mul_one,P.sum_one]

theorem prod_expect (P : FiniteLaw X) (Q : FiniteLaw Y) (f : X × Y → ℝ) :
    (P.prod Q).expect f=P.expect (fun x => Q.expect (fun y => f (x,y))) := by
  simp only [expect,prod,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem prod_expect_fst (P : FiniteLaw X) (Q : FiniteLaw Y) (f : X → ℝ) :
    (P.prod Q).expect (fun z => f z.1)=P.expect f := by
  simp only [prod_expect,expect_const]

theorem prod_expect_snd (P : FiniteLaw X) (Q : FiniteLaw Y) (f : Y → ℝ) :
    (P.prod Q).expect (fun z => f z.2)=Q.expect f := by
  simp only [prod_expect,expect_const]

def pi {I : Type*} [Fintype I] [DecidableEq I] (A : I → Type*) [∀ i, Fintype (A i)] (P : ∀ i, FiniteLaw (A i)) :
    FiniteLaw (∀ i, A i) where
  weight z := ∏ i, (P i).weight (z i)
  nonneg z := Finset.prod_nonneg (fun i _ => (P i).nonneg _)
  sum_one := by rw [← Fintype.prod_sum]; simp only [sum_one,Finset.prod_const_one]

theorem prob_eq_zero_of_support (P : FiniteLaw X) (E : X → Prop)
    (h : ∀ x, 0 < P.weight x → ¬E x) : P.prob E=0 := by
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : 0 < P.weight x
  · simp only [ite_eq_right (h x hx),mul_zero]
  · have he : P.weight x=0 := le_antisymm (le_of_not_gt hx) (P.nonneg x)
    simp only [he,zero_mul]

end FiniteLaw

def gibbsFiniteLaw {n : ℕ} (β : ℝ) (J : Disorder n) : FiniteLaw (Config n) :=
  ⟨gibbs β J,(fun x => (gibbs_pos β J x).le),gibbs_sum β J⟩

def pathFiniteLaw {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (m : ℕ) :
    FiniteLaw (Fin (m+1) → Config n) :=
  ⟨stationaryPathWeight β J m,
    FiniteMarkov.pathWeight_nonneg _ _ (fun x => (gibbs_pos β J x).le) (heatBath_nonneg β J) m,
    stationaryPathWeight_sum hn β J m⟩

theorem pathFiniteLaw_marginal {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (m : ℕ) (k : Fin (m+1)) (f : Config n → ℝ) :
    (pathFiniteLaw hn β J m).expect (fun x => f (x k))=(gibbsFiniteLaw β J).expect f :=
  stationaryPathWeight_marginal hn β J m k f

end SK.Analytic

end
end

end OAI
