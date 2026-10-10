import OAI.Analysis.Laughlin.Pair.FockHaar
import OAI.Analysis.Laughlin.Spin.EmbeddedSpinHaar

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

noncomputable def complexOuter {I : Type*} (v w : I → ℂ) : Matrix I I ℂ :=
  fun i j => v i * star (w j)

theorem contractionForm_outer {I : Type*} [Fintype I] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (v : I → ℂ) (x : Space Q) :
    contractionForm Q minus (complexOuter v v) x =
      (occupationNormSq Q (∑ i, star (v i) • minus i x) : ℂ) := by
  rw [← occupationInner_self]
  simp only [occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,star_star,contractionForm,complexOuter,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

noncomputable def diagonalUnit {J : Type*} [DecidableEq J] (p : J) : Matrix J J ℂ :=
  fun i j => if i=p ∧ j=p then 1 else 0

theorem matrix_sandwich_single {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (W : Matrix I J ℂ) (p : J) :
    W*diagonalUnit p*Wᴴ =
      complexOuter (fun i => W i p) (fun i => W i p) := by
  ext i j
  simp [diagonalUnit,Matrix.mul_apply,complexOuter,Matrix.conjTranspose_apply,ite_and]

theorem physical_family_spin_norm_haar {I : Type*} [Fintype I] [DecidableEq I]
    (Q : ℕ) (ρ : SourceSU2 →* Matrix I I ℂ)
    (hρ : ∀ g, ρ g⁻¹=(ρ g)ᴴ) (hc : ∀ i j, Continuous (fun g => ρ g i j))
    (minus : I → Module.End ℂ (Space Q))
    (hm : ∀ g i x, minus i (exteriorRotation Q g x) =
      ∑ j, ρ g i j • exteriorRotation Q g (minus j x))
    (m : ℕ) (W : Matrix I (Fin (m+1)) ℂ)
    (hW : ∀ g, ρ g*W=W*sourceSpinRepresentation m g)
    (p : Fin (m+1)) (x : Space Q) :
    ((m+1 : ℕ) : ℂ) * (∫ g,
      (occupationNormSq Q (∑ i, star (W i p) • minus i (exteriorRotation Q g⁻¹ x)) : ℂ)
        ∂sourceHaar) = contractionForm Q minus (W*Wᴴ) x := by
  let M : Matrix (Fin (m+1)) (Fin (m+1)) ℂ := fun i j => if i=p ∧ j=p then 1 else 0
  have h := contractionForm_haar Q ρ hρ hc minus hm (W*M*Wᴴ) x
  rw [embedded_spin_haar ρ hρ m W hW,contractionForm_smul] at h
  have ht : Matrix.trace M=1 := by simp [M,Matrix.trace,Matrix.diag]
  rw [ht] at h
  have he : W*M*Wᴴ=complexOuter (fun i => W i p) (fun i => W i p) := matrix_sandwich_single W p
  simp_rw [he,contractionForm_outer] at h
  rw [h]
  have hd : ((m+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp

end Laughlin.Fock

end OAI
