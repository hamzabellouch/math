import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.Ring

namespace OAI

/-! # Binary Matrices -/

noncomputable section
namespace HadwigerCounterexample

open scoped BigOperators
open Matrix

abbrev F := ZMod 2
abbrev Vec (I : Type) := I → F
abbrev Mat (I J : Type) := Matrix I J F
abbrev Space (V : Type) [AddCommGroup V] [Module F V] := Submodule F V

theorem bit_cases (x : F) : x = 0 ∨ x = 1 :=
  (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x
theorem bit_sq (x : F) : x*x = x := by rcases bit_cases x with e|e <;> rw [e] <;> simp
theorem char_two {V : Type*} [AddCommGroup V] [Module F V] (x : V) : x+x=0 :=
  ZModModule.add_self x
theorem odd_smul_bit {n : ℕ} (hn : Odd n) (x : F) : n • x = x := by
  obtain ⟨m,rfl⟩ := hn
  rw [add_smul, one_smul, mul_smul, two_smul,char_two,zero_add]

section Linear

variable {I J K L R S : Type} [Fintype I] [Fintype J]

def evmat (M : Mat I J) (x : Vec I) (y : Vec J) := dotProduct x (M *ᵥ y)

def mpair (M : Mat I J) : Mat I J →ₗ[F] F where
  toFun A := ∑ i, ∑ j, M i j * A i j
  map_add' A B := by simp only [Matrix.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' b A := by
    simp only [Matrix.smul_apply, smul_eq_mul,RingHom.id_apply,Finset.mul_sum,mul_left_comm b]

theorem mpair_comm (M A : Mat I J) : mpair M A = mpair A M := by
  dsimp [mpair]
  simp only [mul_comm]

theorem mpair_outer (M : Mat I J) (x : Vec I) (y : Vec J) :
    mpair M (vecMulVec x y) = evmat M x y := by
  dsimp [mpair,evmat,mulVec,dotProduct,vecMulVec]
  simp only [Finset.mul_sum,mul_left_comm]

/-- Apply frame maps to the two factors of every tensor. -/
def liftM (P : Mat K I) (Q : Mat L J) : Mat I J →ₗ[F] Mat K L where
  toFun A := P*A*Qᵀ
  map_add' A B := by rw [Matrix.mul_add,Matrix.add_mul]
  map_smul' b A := by simp only [Matrix.mul_smul, Matrix.smul_mul,RingHom.id_apply]

theorem liftM_def (P : Mat K I) (Q : Mat L J) (A : Mat I J) :
    liftM P Q A = P*A*Qᵀ := rfl

theorem liftM_outer (P : Mat K I) (Q : Mat L J) (x : Vec I) (y : Vec J) :
    liftM P Q (vecMulVec x y) = vecMulVec (P *ᵥ x) (Q *ᵥ y) := by
  rw [liftM_def,mul_vecMulVec,vecMulVec_mul,vecMul_transpose]

variable [Fintype K] [Fintype L]

theorem liftM_comp (P : Mat K I) (Q : Mat L J) (P' : Mat R K) (Q' : Mat S L)
    (A : Mat I J) :
    liftM P' Q' (liftM P Q A) = liftM (P'*P) (Q'*Q) A := by
  simp only [liftM_def, Matrix.transpose_mul,Matrix.mul_assoc]

theorem mpair_liftM (P : Mat K I) (Q : Mat L J) (M : Mat K L) (A : Mat I J) :
    mpair M (liftM P Q A) = mpair (liftM Pᵀ Qᵀ M) A := by

  simp only [liftM_def, mpair, transpose_transpose, LinearMap.coe_mk,AddHom.coe_mk,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, transpose_apply]

  conv_lhs =>
    arg 2
    intro k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs =>
    arg 2
    intro k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem mat_left_inv [DecidableEq I] {P : Mat K I} (hp : Function.Injective P.mulVec) :
    ∃ Q : Mat I K, Q*P = 1 := by
  classical
  have hp' : Function.Injective (P.mulVecLin) := hp
  obtain ⟨f,hf⟩ := P.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hp')
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul]
  simp only [Matrix.toLin'_one]
  change ((LinearMap.toMatrix').symm _) ∘ₗ _ = _
  rw [LinearEquiv.symm_apply_apply]
  exact hf

theorem liftM_inj {P : Mat K I} {Q : Mat L J} (hp : Function.Injective P.mulVec)
    (hq : Function.Injective Q.mulVec) : Function.Injective (liftM P Q) := by
  classical
  obtain ⟨P', hP⟩ := mat_left_inv hp
  obtain ⟨Q', hQ⟩ := mat_left_inv hq
  intro A B hab
  have hh := congrArg (liftM P' Q') hab
  rw [liftM_comp,liftM_comp,hP,hQ] at hh
  simpa only [liftM_def, Matrix.one_mul, Matrix.transpose_one,
    Matrix.mul_one] using hh

end Linear
end HadwigerCounterexample

end

end OAI
