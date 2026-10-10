import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

variable {I : Type*} [Fintype I] {Ω G : I → Type*}
  [∀i,Fintype (Ω i)] [∀i,Fintype (G i)]

def finitePush {X Y : Type*} [Fintype X] (w : X → ℂ) (f : X → Y) (y : Y) : ℂ :=
  ∑x, if f x=y then w x else 0

omit [∀ i, Fintype (G i)] in
lemma finitePush_pi (w : ∀i, Ω i → ℂ) (f : ∀i, Ω i → G i) (g : ∀i, G i) :
    (∏i, finitePush (w i) (f i) (g i)) =
      finitePush (fun x : ∀i, Ω i => ∏i,w i (x i)) (fun x i => f i (x i)) g := by
  unfold finitePush
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_ite_zero]
  congr 1
  exact propext funext_iff.symm

lemma finitePush_expectation {X Y V : Type*} [Fintype X] [Fintype Y]
    [AddCommMonoid V] [Module ℂ V] (w : X → ℂ) (f : X → Y) (F : Y → V) :
    (∑y, finitePush w f y • F y)=∑x,w x • F (f x) := by
  classical
  unfold finitePush
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [ite_smul,zero_smul]
  simp

lemma independentPush_expectation {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (w : ∀i, Ω i → ℂ) (f : ∀i, Ω i → G i) (F : (∀i,G i) → V) :
    (∑g : ∀i,G i, (∏i,finitePush (w i) (f i) (g i)) • F g)=
      ∑x : ∀i,Ω i, (∏i,w i (x i)) • F (fun i=>f i (x i)) := by
  simp_rw [finitePush_pi]
  exact finitePush_expectation _ _ _

end BinaryCoordinateSweeps

end

end OAI
