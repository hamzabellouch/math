import OAI.Analysis.Quasitrace.Order
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel

namespace OAI

noncomputable section

/-! Proper infiniteness, isometry columns, and C-star matrix amplification. -/

open scoped ComplexOrder CStarAlgebra BigOperators
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

def ProperlyInfinite (A : Type*) [CStarAlgebra A] : Prop :=
  ∃ s t : A, star s*s = 1 ∧ star t*t = 1 ∧ star s*t = 0

theorem not_properlyInfinite (τ : OneQuasitrace A) (hτ : τ.Normalized) :
    ¬ ProperlyInfinite A := by
  rintro ⟨s,t,hs,ht,hst⟩
  change τ 1 = 1 at hτ
  let p := s * star s
  let q := t * star t
  have hp : IsSelfAdjoint p := IsSelfAdjoint.mul_star_self s
  have hq : IsSelfAdjoint q := IsSelfAdjoint.mul_star_self t
  have hpp : p*p = p := by
    dsimp [p]
    calc
      (s*star s)*(s*star s) = s*(star s*s)*star s := by simp only [mul_assoc]
      _ = s*star s := by rw [hs]; simp
  have hqq : q*q = q := by
    dsimp [q]
    calc
      (t*star t)*(t*star t) = t*(star t*t)*star t := by simp only [mul_assoc]
      _ = t*star t := by rw [ht]; simp
  have hpq : p*q = 0 := by
    dsimp [p,q]
    calc
      (s*star s)*(t*star t) = s*(star s*t)*star t := by simp only [mul_assoc]
      _ = 0 := by rw [hst]; simp
  have hqp : q*p = 0 := by
    have h := congrArg star hpq
    simpa only [star_mul, hp.star_eq, hq.star_eq, star_zero] using h
  have hcomm : Commute p q := hpq.trans hqp.symm
  have hpqSq : (p+q)*(p+q) = p+q := by
    simp only [add_mul, mul_add, hpp, hqq, hpq, hqp, add_zero, zero_add]
  have he : star (1-(p+q))*(1-(p+q)) = 1-(p+q) := by
    rw [(IsSelfAdjoint.one A |>.sub (hp.add hq)).star_eq]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hpqSq, sub_self, sub_zero]
  have hle : p+q ≤ 1 := by
    apply sub_nonneg.mp
    rw [← he]
    exact star_mul_self_nonneg _
  have hvp : τ p = 1 := by
    have h := τ.square_swap s
    simpa only [hs, hτ] using h.symm
  have hvq : τ q = 1 := by
    have h := τ.square_swap t
    simpa only [ht, hτ] using h.symm
  have hv : τ (p+q) = 2 := by rw [τ.map_add hp hq hcomm, hvp, hvq]; norm_num
  have h := τ.scalar_upper_bound 1
    (add_nonneg (mul_star_self_nonneg s) (mul_star_self_nonneg t))
    (by simpa only [Complex.ofReal_one, one_smul] using hle)
  rw [hv, hτ] at h
  norm_num at h

variable {m : ℕ}

def properIsometryColumns (s t : CStarMatrix (Fin m) (Fin m) A) :
    CStarMatrix (Fin m) (Fin (m+m)) A :=
  CStarMatrix.ofMatrix (fun row col =>
    Matrix.fromCols (CStarMatrix.ofMatrix.symm s) (CStarMatrix.ofMatrix.symm t) row
      ((finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m+m)).symm col))

/-- The rectangular concatenation of a pair of orthogonal isometries has
column adjoint-square identity, with exactly 2m input columns. -/
theorem properIsometryColumns_column (s t : CStarMatrix (Fin m) (Fin m) A)
    (hs : star s*s=1) (ht : star t*t=1) (hst : star s*t=0) (i j : Fin (m+m)) :
    (∑ row, star (properIsometryColumns s t row i)*properIsometryColumns s t row j) =
      if i=j then (1 : A) else 0 := by
  have hts : star t*s=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hst
  let S := CStarMatrix.ofMatrix.symm s
  let T := CStarMatrix.ofMatrix.symm t
  have hS : S.conjTranspose*S=1 := hs
  have hT : T.conjTranspose*T=1 := ht
  have hST : S.conjTranspose*T=0 := hst
  have hTS : T.conjTranspose*S=0 := hts
  have hc : (Matrix.fromCols S T).conjTranspose * Matrix.fromCols S T = 1 := by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,Matrix.fromRows_mul_fromCols,
      hS,hT,hST,hTS,Matrix.fromBlocks_one]
  let e := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m+m)).symm
  have he := congrArg (fun M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A => M (e i) (e j)) hc
  have he' : (∑ row, star (Matrix.fromCols S T row (e i)) *
      Matrix.fromCols S T row (e j)) = if i=j then (1 : A) else 0 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Equiv.apply_eq_iff_eq] using he
  exact he'

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem properlyInfinite_map (f : A →⋆ₐ[ℂ] B) (hp : ProperlyInfinite A) :
    ProperlyInfinite B := by
  obtain ⟨s,t,hs,ht,hst⟩ := hp
  refine ⟨f s,f t,?_,?_,?_⟩
  · simpa only [map_mul,map_star,map_one] using congrArg f hs
  · simpa only [map_mul,map_star,map_one] using congrArg f ht
  · simpa only [map_mul,map_star,map_zero] using congrArg f hst

theorem properlyInfinite_starAlgEquiv_iff (e : A ≃⋆ₐ[ℂ] B) :
    ProperlyInfinite A ↔ ProperlyInfinite B :=
  ⟨properlyInfinite_map e.toStarAlgHom,properlyInfinite_map e.symm.toStarAlgHom⟩

variable (A) (m n : Type*) [Fintype m] [Fintype n]

/-- Flatten the two genuine C*-matrix levels into one product-indexed
matrix algebra, preserving multiplication, star, and complex scalars. -/
def cstarMatrixFlatten : CStarMatrix m m (CStarMatrix n n A) ≃⋆ₐ[ℂ]
    CStarMatrix (m × n) (m × n) A where
  toFun X := CStarMatrix.ofMatrix (fun i j => X i.1 j.1 i.2 j.2)
  invFun X := CStarMatrix.ofMatrix (fun i j => CStarMatrix.ofMatrix (fun a b => X (i,a) (j,b)))
  left_inv X := rfl
  right_inv X := rfl
  map_add' X Y := rfl
  map_smul' c X := rfl
  map_star' X := rfl
  map_mul' X Y := by
    ext i j
    simp only [CStarMatrix.mul_apply,
      Fintype.sum_prod_type]
    calc
      _ = ∑ k : m, (X i.1 k * Y k j.1) i.2 j.2 :=
        Matrix.sum_apply i.2 j.2 Finset.univ (fun k => (show Matrix n n A from X i.1 k * Y k j.1))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rfl

end Kaplansky

end

end OAI
