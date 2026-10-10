import OAI.Analysis.NuclearUltrapower.CuntzAlgebra
import OAI.Analysis.NuclearUltrapower.HilbertTensor

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.CuntzWords

/-- Fixed-length binary words, with a product decomposition at every successor. -/
@[reducible] def Word : ℕ → Type
  | 0 => PUnit
  | n+1 => Fin 2 × Word n

instance (n : ℕ) : Fintype (Word n) := by
  induction n with
  | zero => exact PUnit.fintype
  | succ n ih =>
    letI : Fintype (Word n) := ih
    exact inferInstanceAs (Fintype (Fin 2 × Word n))

instance (n : ℕ) : DecidableEq (Word n) := Classical.decEq _

def value {D : Type*} [Monoid D] (r : Fin 2 → D) : {n : ℕ} → Word n → D
  | 0, _ => 1
  | _+1, (i,w) => r i * value r w

@[simp] theorem value_zero {D : Type*} [Monoid D] (r : Fin 2 → D) (w : Word 0) :
    value r w = 1 := rfl
@[simp] theorem value_succ {D : Type*} [Monoid D] (r : Fin 2 → D) {n : ℕ}
    (i : Fin 2) (w : Word n) : value r (n := n+1) (i,w) = r i * value r w := rfl

def index : {n : ℕ} → Word n → CuntzModel.Index
  | 0, _ => (0,0)
  | _+1, (i,w) => CuntzModel.shiftIndex i (index w)

@[simp] theorem index_succ {n : ℕ} (i : Fin 2) (w : Word n) :
    index (n := n+1) (i,w) = CuntzModel.shiftIndex i (index w) := rfl

@[simp] theorem index_height {n : ℕ} (w : Word n) : (index w).1 = (n : ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases w with ⟨i,w⟩
    simp only [index_succ,CuntzModel.shiftIndex_apply,ih,Nat.cast_add,Nat.cast_one]

theorem index_injective (n : ℕ) : Function.Injective (@index n) := by
  induction n with
  | zero => exact fun _ _ _ => Subsingleton.elim _ _
  | succ n ih =>
    rintro ⟨i,w⟩ ⟨j,v⟩ h
    have hij : i = j := by
      by_contra hn
      exact CuntzModel.shiftIndex_disjoint hn (index w) (index v) h
    subst j
    have hw := ih ((CuntzModel.shiftIndex i).injective h)
    subst v
    rfl

theorem index_ne_of_length_ne {n m : ℕ} (hnm : n ≠ m) (w : Word n) (v : Word m) :
    index w ≠ index v := by
  intro h
  have hh := congrArg Prod.fst h
  simp only [index_height] at hh
  exact hnm (Int.ofNat_inj.mp hh)

/-- Orthogonality is a consequence of the two defining Cuntz relations. -/
theorem cross {D : Type*} [CStarAlgebra D] (r : Fin 2 → D) (hr : CuntzTwoRelations r)
    (i j : Fin 2) (hij : i ≠ j) : star (r i) * r j = 0 := by
  have hsum : r i * star (r i) + r j * star (r j) = 1 := by
    have h := hr.2
    fin_cases i <;> fin_cases j <;> try contradiction
    · simpa [Fin.sum_univ_two] using h
    · simpa [Fin.sum_univ_two,add_comm] using h
  have hh : star (r j) * (r i * star (r i) + r j * star (r j)) * r j = 1 := by
    rw [hsum,mul_one,hr.1]
  have he : star (star (r i) * r j) * (star (r i) * r j) = 0 := by
    simp only [mul_add,add_mul] at hh
    have ht : star (r j) * (r j * star (r j)) * r j = 1 := by
      simp only [← mul_assoc, hr.1, one_mul]
    rw [ht,add_eq_right] at hh
    simpa only [star_mul,star_star,mul_assoc] using hh
  exact (CStarRing.star_mul_self_eq_zero_iff _).mp he

/-- Completeness of the finite-length row is proved, not assumed. -/
theorem sum_range {D : Type*} [CStarAlgebra D] (r : Fin 2 → D) (hr : CuntzTwoRelations r)
    (n : ℕ) : ∑ w : Word n, value r w * star (value r w) = 1 := by
  induction n with
  | zero => simp [Word,value]
  | succ n ih =>
    change (∑ w : Fin 2 × Word n, value r (n := n+1) w * star (value r (n := n+1) w)) = (1 : D)
    rw [Fintype.sum_prod_type]
    simp only [value_succ,star_mul]
    have he (i : Fin 2) :
        (∑ w : Word n, (r i * value r w) * (star (value r w) * star (r i))) =
          r i * star (r i) := by
      calc
        _ = r i * (∑ w : Word n, value r w * star (value r w)) * star (r i) := by
          simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
        _ = _ := by rw [ih,mul_one]
    simp only [he]
    exact hr.2

end NuclearUltrapower.CuntzWords
end
end

section

noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords
local instance : DecidableEq Index := Classical.decEq _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev Target (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  TensorHilbert Space H

def coordinate (i : Index) : H →L[ℂ] Target H :=
  UniformSpace.Completion.toComplL.comp (TensorProduct.mkL ℂ Space H (lp.single 2 i 1))

@[simp] theorem coordinate_apply (i : Index) (x : H) :
    coordinate i x = ((lp.single 2 i 1) ⊗ₜ[ℂ] x : Space ⊗[ℂ] H) := rfl

@[simp] theorem inner_coordinate (i j : Index) (x y : H) :
    ⟪coordinate i x, coordinate j y⟫_ℂ = if i = j then ⟪x,y⟫_ℂ else 0 := by
  simp only [coordinate_apply,UniformSpace.Completion.inner_coe,TensorProduct.inner_tmul,
    lp.inner_single_left,RCLike.inner_apply',map_one,one_mul,lp.single_apply,Pi.single_apply]
  split_ifs with h <;> simp_all

@[simp] theorem coordinate_norm (i : Index) (x : H) : ‖coordinate i x‖ = ‖x‖ := by
  rw [coordinate_apply,UniformSpace.Completion.norm_coe,TensorProduct.norm_tmul]
  rw [lp.norm_single (by norm_num),norm_one,one_mul]

variable [CompleteSpace H]

def left (i : Fin 2) : Target H →L[ℂ] Target H := tensorLeftHom (shift i)
def right (T : H →L[ℂ] H) : Target H →L[ℂ] Target H := tensorRightHom T

@[simp] theorem left_coordinate (i : Fin 2) (k : Index) (x : H) :
    left i (coordinate k x) = coordinate (shiftIndex i k) x := by
  change completedTensorMap (shift i) 1 (coordinate k x) = _
  rw [coordinate_apply,completedTensorMap_coe]
  simp only [TensorProduct.mapL_tmul,shift_single,one_apply_eq_self,coordinate_apply]

@[simp] theorem right_coordinate (T : H →L[ℂ] H) (k : Index) (x : H) :
    right T (coordinate k x) = coordinate k (T x) := by
  change completedTensorMap 1 T (coordinate k x) = _
  rw [coordinate_apply,completedTensorMap_coe]
  simp only [TensorProduct.mapL_tmul,one_apply_eq_self,coordinate_apply]

@[simp] theorem left_star_mul (i j : Fin 2) :
    star (left (H := H) i) * left j = if i = j then 1 else 0 := by
  change star (tensorLeftHom (shift i)) * tensorLeftHom (shift j) = _
  rw [← map_star,← map_mul]
  by_cases h : i = j
  · subst j
    rw [relations.1,map_one,ite_eq_left rfl]
  · rw [cross shift relations i j h,map_zero,ite_eq_right h]

theorem left_norm_le (i : Fin 2) : ‖left (H := H) i‖ ≤ 1 := by
  change ‖completedTensorMap (shift i) (1 : H →L[ℂ] H)‖ ≤ 1
  have hs : ‖shift i‖ ≤ 1 := (l2Embedding (shiftIndex i)).norm_toContinuousLinearMap_le
  have hi : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  exact (completedTensorMap_norm_le _ _).trans
    (by nlinarith [norm_nonneg (shift i), norm_nonneg (1 : H →L[ℂ] H)])

theorem right_norm_le (T : H →L[ℂ] H) : ‖right T‖ ≤ ‖T‖ :=
  NonUnitalStarAlgHom.norm_apply_le (tensorRightHom (E := Space) (F := H)) T

end NuclearUltrapower.CuntzAveraging
end
end

section

noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

def row (n : ℕ) : H →L[ℂ] Target H :=
  ∑ w : Word n, (coordinate (index w)).comp (star (R (value generator w)))

@[simp] theorem row_apply (n : ℕ) (x : H) :
    row R n x = ∑ w : Word n, coordinate (index w) (star (R (value generator w)) x) := by
  simp only [row,sum_apply,ContinuousLinearMap.comp_apply]

@[simp] theorem row_support (n : ℕ) : (row R n).comp (R 1) = row R n := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,row_apply]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  change (star (R (value generator w)) * R 1) x = _
  rw [← map_star,← map_mul,mul_one]

@[simp] theorem inner_row (n : ℕ) (x y : H) :
    ⟪row R n x, row R n y⟫_ℂ = ⟪x,R 1 y⟫_ℂ := by
  rw [row_apply,row_apply]
  simp only [sum_inner,inner_sum,inner_coordinate,(index_injective n).eq_iff,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
  rw [← inner_sum]
  congr 1
  have h := congrArg (fun T : H →L[ℂ] H => T y)
    (congrArg R (sum_range generator CuntzUniversal.relations n))
  simpa only [map_sum,map_mul,map_star,sum_apply,mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint] using h

@[simp] theorem inner_row_ne {n m : ℕ} (hnm : n ≠ m) (x y : H) :
    ⟪row R n x,row R m y⟫_ℂ = 0 := by
  simp only [row_apply,sum_inner,inner_sum,inner_coordinate,
    ite_eq_right (index_ne_of_length_ne hnm _ _),Finset.sum_const_zero]

theorem support_inner (x y : H) : ⟪R 1 x,R 1 y⟫_ℂ = ⟪x,R 1 y⟫_ℂ := by
  have hs : (R 1).adjoint * R 1 = R 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint,← map_star,star_one,← map_mul,one_mul]
  calc
    _ = ⟪x, (R 1).adjoint (R 1 y)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right (R 1) x (R 1 y)).symm
    _ = _ := congrArg (fun T : H →L[ℂ] H => ⟪x,T y⟫_ℂ) hs

@[simp] theorem row_norm (n : ℕ) (x : H) : ‖row R n x‖ = ‖R 1 x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ),inner_row,support_inner]

theorem support_norm_le (x : H) : ‖R 1 x‖ ≤ ‖x‖ := by
  have hR : ‖R 1‖ ≤ 1 := by simpa only [norm_one] using NonUnitalStarAlgHom.norm_apply_le R (1 : Algebra)
  simpa only [one_mul] using (R 1).le_of_opNorm_le hR x

theorem row_norm_le (n : ℕ) : ‖row R n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul,row_norm]
  exact support_norm_le R x

/-- The row recursion comes from word concatenation and the genuine model shifts. -/
theorem row_step (n : ℕ) : row R (n+1) =
    ∑ i : Fin 2, ((left i).comp (row R n)).comp (star (R (generator i))) := by
  ext x
  rw [row_apply]
  change (∑ w : Fin 2 × Word n, coordinate (index (n := n+1) w)
    (star (R (value generator (n := n+1) w)) x)) = _
  rw [Fintype.sum_prod_type]
  simp only [sum_apply,ContinuousLinearMap.comp_apply,row_apply,map_sum,value_succ,
    index_succ,left_coordinate,map_mul,star_mul,mul_apply_eq_comp]

theorem rep_cross (i j : Fin 2) :
    star (R (generator i)) * R (generator j) = if i = j then R 1 else 0 := by
  rw [← map_star,← map_mul]
  by_cases h : i = j
  · subst j
    rw [CuntzUniversal.relations.1,ite_eq_left rfl]
  · rw [cross generator CuntzUniversal.relations i j h,map_zero,ite_eq_right h]

/-- Exact finite-level intertwining of each Cuntz generator. -/
theorem row_next_generator (n : ℕ) (i : Fin 2) :
    (row R (n+1)).comp (R (generator i)) = (left i).comp (row R n) := by
  rw [row_step]
  ext x
  simp only [ContinuousLinearMap.comp_apply,sum_apply]
  rw [Finset.sum_eq_single i]
  · change left i (row R n ((star (R (generator i)) * R (generator i)) x)) = _
    rw [rep_cross,ite_eq_left rfl]
    exact congrArg (left i) (congrArg (fun T : H →L[ℂ] Target H => T x) (row_support R n))
  · intro j _ hji
    change left j (row R n ((star (R (generator j)) * R (generator i)) x)) = 0
    rw [rep_cross,ite_eq_right hji,zero_apply,map_zero,map_zero]
  · simp

/-- Exact finite-level intertwining of the adjoint generator in reverse. -/
theorem left_star_row_next (n : ℕ) (i : Fin 2) :
    (star (left i)).comp (row R (n+1)) = (row R n).comp (star (R (generator i))) := by
  rw [row_step]
  ext x
  simp only [ContinuousLinearMap.comp_apply,sum_apply,map_sum]
  rw [Finset.sum_eq_single i]
  · change (star (left (H := H) i) * left i : Target H →L[ℂ] Target H) (row R n (star (R (generator i)) x)) = _
    rw [left_star_mul,ite_eq_left rfl,one_apply_eq_self]
  · intro j _ hji
    change (star (left (H := H) i) * left j : Target H →L[ℂ] Target H) (row R n (star (R (generator j)) x)) = 0
    rw [left_star_mul,ite_eq_right (Ne.symm hji),zero_apply]
  · simp

/-- Arbitrary commuting operators intertwine with the second tensor coordinate. -/
theorem row_commuting (n : ℕ) (T : H →L[ℂ] H)
    (hT : ∀ a, Commute (R a) T) : (row R n).comp T = (right T).comp (row R n) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,row_apply,map_sum,right_coordinate]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  have h := congrArg (fun U : H →L[ℂ] H => U x) (hT (star (value generator w))).eq
  simpa only [map_star,mul_apply_eq_comp] using h

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
