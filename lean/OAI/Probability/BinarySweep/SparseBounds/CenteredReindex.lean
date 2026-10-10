import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.CenteredMatrix

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {I J X Y : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

omit [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] in
lemma partialKernel_iff (A : Finset I) (g : Equiv.Perm X) (x y : I ↪ X) :
    subPlacement A (movePlacement g x)=subPlacement A y ↔ ∀i∈A, g (x i)=y i := by
  constructor
  · intro h i hi
    exact congrArg (fun u => u ⟨i,hi⟩) h
  · intro h
    apply Function.Embedding.ext
    intro i
    exact h i.val i.property

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype X] [Fintype Y] in
lemma partialKernel_reindex (a : I ≃ J) (e : X ≃ Y) (A : Finset I)
    (g : Equiv.Perm X) (x y : I ↪ X) :
    partialKernel (a.finsetCongr A) (e.permCongr g)
      (Equiv.embeddingCongr a e y) (Equiv.embeddingCongr a e x)=partialKernel A g y x := by
  unfold partialKernel
  congr 1
  rw [partialKernel_iff,partialKernel_iff]
  apply propext
  constructor
  · intro he i hi
    have ht := he (a i) (by simpa using hi)
    simpa using ht
  · intro he j hj
    obtain ⟨i,rfl⟩ := a.surjective j
    have ht := he i (by simpa using hj)
    simpa using congrArg e ht

omit [DecidableEq I] [DecidableEq J] in
theorem centeredMatrix_reindex (a : I ≃ J) (e : X ≃ Y) (s : ℝ)
    (p : Equiv.Perm X → ℂ) (x y : I ↪ X) :
    centeredMatrix s (fun g => p (e.permCongr.symm g))
      (Equiv.embeddingCongr a e y) (Equiv.embeddingCongr a e x)=centeredMatrix s p y x := by
  simp only [centeredMatrix,Finset.powerset_univ,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  have ht := Equiv.sum_comp a.finsetCongr (fun A : Finset J =>
    ((-1:ℂ)^(Fintype.card J-A.card)*(s:ℂ)^A.card/(s:ℂ)^Fintype.card J) *
      ∑g, p (e.permCongr.symm g) * partialKernel A g
        (Equiv.embeddingCongr a e y) (Equiv.embeddingCongr a e x))
  rw [← ht]
  apply Finset.sum_congr rfl
  intro A _
  have hc : (a.finsetCongr A).card=A.card := by simp
  rw [hc,← Fintype.card_congr a]
  congr 1
  have hu := Equiv.sum_comp e.permCongr (fun g =>
    p (e.permCongr.symm g) * partialKernel (a.finsetCongr A) g
      (Equiv.embeddingCongr a e y) (Equiv.embeddingCongr a e x))
  rw [← hu]
  apply Finset.sum_congr rfl
  intro g _
  rw [Equiv.symm_apply_apply,partialKernel_reindex]

omit [DecidableEq I] [DecidableEq J] in
lemma centeredMatrix_hs_reindex (a : I ≃ J) (e : X ≃ Y) (s : ℝ)
    (p : Equiv.Perm X → ℂ) :
    (∑x : J ↪ Y, ∑y, ‖centeredMatrix s (fun g => p (e.permCongr.symm g)) y x‖^2)=
      ∑x : I ↪ X, ∑y, ‖centeredMatrix s p y x‖^2 := by
  rw [← Equiv.sum_comp (Equiv.embeddingCongr a e)]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Equiv.sum_comp (Equiv.embeddingCongr a e)]
  simp_rw [centeredMatrix_reindex]

end BinaryCoordinateSweeps.Young

end

end OAI
