import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupMatrixApproximation
import Mathlib.Data.Fintype.EquivFin

namespace OAI
noncomputable section
namespace CuntzPureness
local instance freeGroupMatrixDimensionsDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
open CuntzTrace
open scoped ComplexOrder

def indexedPermutationUnitary {ι : Type*} [Fintype ι] [DecidableEq ι] : Equiv.Perm ι →* unitary (CStarMatrix ι ι ℂ) where
  toFun p := ⟨CStarMatrix.ofMatrix ((p⁻¹).permMatrix ℂ), by
    constructor
    · change CStarMatrix.ofMatrix
        (((p⁻¹).permMatrix ℂ).conjTranspose * (p⁻¹).permMatrix ℂ) = 1
      rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
      simp [CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv]
    · change CStarMatrix.ofMatrix
        ((p⁻¹).permMatrix ℂ * ((p⁻¹).permMatrix ℂ).conjTranspose) = 1
      rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
      simp [CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv]⟩
  map_one' := by apply Subtype.ext; simp [CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv]
  map_mul' p q := by
    apply Subtype.ext
    change CStarMatrix.ofMatrix (((p*q)⁻¹).permMatrix ℂ) =
      CStarMatrix.ofMatrix ((p⁻¹).permMatrix ℂ * (q⁻¹).permMatrix ℂ)
    rw [mul_inv_rev, Matrix.permMatrix_mul]

def freeGroupModelDimension : ℕ → ℕ
  | 0 => Fintype.card (FreeGroupMatrixIndex 0)
  | n+1 => Fintype.card (FreeGroupMatrixIndex (n+1)) * (freeGroupModelDimension n+1)

def freeGroupModelMultiplicity : ℕ → ℕ
  | 0 => 1
  | n+1 => freeGroupModelDimension n+1

lemma freeGroupModelDimension_eq (n : ℕ) : freeGroupModelDimension n =
    Fintype.card (FreeGroupMatrixIndex n) * freeGroupModelMultiplicity n := by
  cases n <;> simp [freeGroupModelDimension, freeGroupModelMultiplicity]

lemma freeGroupModelDimension_pos (n : ℕ) : 0 < freeGroupModelDimension n := by
  cases n with
  | zero => exact Fintype.card_pos
  | succ n => exact Nat.mul_pos Fintype.card_pos (Nat.succ_pos _)

lemma freeGroupModelDimension_strictMono : StrictMono freeGroupModelDimension := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h : 1 ≤ Fintype.card (FreeGroupMatrixIndex (n+1)) := Fintype.card_pos
  have hm := Nat.mul_le_mul_right (freeGroupModelDimension n+1) h
  change freeGroupModelDimension n < Fintype.card (FreeGroupMatrixIndex (n+1)) * (freeGroupModelDimension n+1)
  exact (Nat.lt_succ_self _).trans_le (by simpa only [one_mul] using hm)

def freeGroupModelCoordinate (n : ℕ) := freeGroupModelDimension n - 1

lemma freeGroupModelCoordinate_succ (n : ℕ) :
    freeGroupModelCoordinate n+1 = freeGroupModelDimension n :=
  Nat.sub_add_cancel (freeGroupModelDimension_pos n)

lemma freeGroupModelCoordinate_strictMono : StrictMono freeGroupModelCoordinate := by
  intro i j hij
  have h := freeGroupModelDimension_strictMono hij
  have hi := freeGroupModelCoordinate_succ i
  have hj := freeGroupModelCoordinate_succ j
  omega

def freeGroupModelIndexEquiv (n : ℕ) :
    FreeGroupMatrixIndex n × Fin (freeGroupModelMultiplicity n) ≃
      Fin (freeGroupModelCoordinate n+1) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_prod, Fintype.card_fin, ← freeGroupModelDimension_eq,
      freeGroupModelCoordinate_succ])

def freeGroupReplicatedPermutation (n : ℕ) : FreeGroup ℕ →*
    Equiv.Perm (Fin (freeGroupModelCoordinate n+1)) where
  toFun g := (freeGroupModelIndexEquiv n).permCongr
    ((Equiv.mulLeft (separatingQuotientMap (FreeGroup ℕ) n g)).prodCongr (Equiv.refl _))
  map_one' := by ext i; simp
  map_mul' g h := by ext i; simp [Prod.map]

lemma freeGroupReplicatedPermutation_no_fixed (n : ℕ) (g : FreeGroup ℕ)
    (hg : separatingQuotientMap (FreeGroup ℕ) n g ≠ 1)
    (i : Fin (freeGroupModelCoordinate n+1)) :
    freeGroupReplicatedPermutation n g i ≠ i := by
  intro hi
  have h := congrArg (fun j => ((freeGroupModelIndexEquiv n).symm j).1) hi
  have he : separatingQuotientMap (FreeGroup ℕ) n g *
      ((freeGroupModelIndexEquiv n).symm i).1 = ((freeGroupModelIndexEquiv n).symm i).1 := by
    simpa [freeGroupReplicatedPermutation] using h
  exact hg (mul_right_cancel (he.trans (one_mul _).symm))

def freeGroupReplicatedMatrix (n : ℕ) : FreeGroup ℕ →*
    unitary (FinMatrix ℂ (freeGroupModelCoordinate n+1)) :=
  @indexedPermutationUnitary _ (Fin.fintype _) (instDecidableEqFin _) |>.comp (freeGroupReplicatedPermutation n)

lemma freeGroupReplicatedMatrix_trace (g : FreeGroup ℕ) :
    ∀ᶠ n in Filter.atTop,
      (scalarMatrixTracialState (freeGroupModelCoordinate n)).functional
        (freeGroupReplicatedMatrix n g) = if g=1 then 1 else 0 := by
  by_cases hg : g=1
  · subst g
    exact Filter.Eventually.of_forall (fun n => by simp [TracialState.normalized])
  · filter_upwards [separatingQuotientMap_eventually_ne (FreeGroup ℕ) g 1 hg] with n hn
    rw [ite_eq_right hg]
    have hn' : separatingQuotientMap (FreeGroup ℕ) n g ≠ 1 := by simpa using hn
    have hd (i : Fin (freeGroupModelCoordinate n+1)) :
        (freeGroupReplicatedMatrix n g : FinMatrix ℂ (freeGroupModelCoordinate n+1)) i i = 0 := by
      have hnf : (freeGroupReplicatedPermutation n g)⁻¹ i ≠ i := by
        intro h
        apply freeGroupReplicatedPermutation_no_fixed n g hn' i
        have := congrArg (freeGroupReplicatedPermutation n g) h
        simpa using this.symm
      simp [freeGroupReplicatedMatrix, indexedPermutationUnitary,
        Equiv.Perm.permMatrix, PEquiv.toMatrix]
      exact hnf
    change (Fintype.card (Fin (freeGroupModelCoordinate n+1)) : ℂ)⁻¹ *
      ∑ i, complexScalarTracialState.functional
        ((freeGroupReplicatedMatrix n g : FinMatrix ℂ (freeGroupModelCoordinate n+1)) i i) = 0
    simp [hd]
end CuntzPureness

end

end OAI
