import OAI.Analysis.InterpolatedFactors.StabilizationIso

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
variable {G : Type u_1}

def matrixBlock (i j : ℕ) (T : GroupOperator G) : GroupOperator (ℕ × G) :=
  (productSingle ℕ G i).comp (T.comp (productCoordinate ℕ G j))

@[simp] theorem matrixBlock_apply (i j k : ℕ) (T : GroupOperator G)
    (ξ : GroupHilbert (ℕ × G)) (g : G) :
    matrixBlock i j T ξ (k,g)=if k=i then T (productCoordinate ℕ G j ξ) g else 0 := by
  simp only [matrixBlock,ContinuousLinearMap.comp_apply,productSingle_apply]

@[simp] theorem productCoordinate_productSingle (i j : ℕ) (ξ : GroupHilbert G) :
    productCoordinate ℕ G i (productSingle ℕ G j ξ)=if i=j then ξ else 0 := by
  ext g
  simp only [productCoordinate_apply,productSingle_apply]
  split_ifs <;> rfl

@[simp] theorem matrixEntry_matrixBlock (i j k l : ℕ) (T : GroupOperator G) :
    matrixEntry (matrixBlock i j T) k l=if k=i ∧ l=j then T else 0 := by
  ext ξ g
  simp only [matrixEntry_apply,matrixBlock_apply,productCoordinate_productSingle]
  by_cases hk : k=i <;> by_cases hl : l=j <;> simp [hk,hl,show (j=l) ↔ (l=j) from eq_comm]

@[simp] theorem matrixBlock_zero (i j : ℕ) : matrixBlock i j (0 : GroupOperator G)=0 := by
  ext ξ ⟨k,g⟩
  simp

@[simp] theorem matrixBlock_mul (i j k l : ℕ) (T S : GroupOperator G) :
    matrixBlock i j T * matrixBlock k l S=if j=k then matrixBlock i l (T*S) else 0 := by
  ext ξ ⟨m,g⟩
  simp only [mul_apply_eq_comp,matrixBlock_apply]
  have hc : productCoordinate ℕ G j (matrixBlock k l S ξ)=
      if j=k then S (productCoordinate ℕ G l ξ) else 0 := by
    change productCoordinate ℕ G j (productSingle ℕ G k (S (productCoordinate ℕ G l ξ)))=_
    rw [productCoordinate_productSingle]
  rw [hc]
  by_cases hj : j=k <;> by_cases hm : m=i <;> simp [hj,hm,mul_apply_eq_comp]

@[simp] theorem matrixBlock_star (i j : ℕ) (T : GroupOperator G) :
    star (matrixBlock i j T)=matrixBlock j i (star T) := by
  apply matrixEntry_ext
  intro k l
  rw [matrixEntry_star,matrixEntry_matrixBlock,matrixEntry_matrixBlock]
  by_cases h : l=i ∧ k=j
  · simp only [ite_eq_left h,ite_eq_left (And.symm h)]
  · simp only [ite_eq_right h,ite_eq_right (fun hh => h (And.symm hh)),star_zero (GroupOperator G)]

theorem matrixBlock_mem [Group G] (i j : ℕ) (T : groupVonNeumann G) :
    matrixBlock i j (T : GroupOperator G)∈stabilization G := by
  rw [mem_stabilization_iff_matrix]
  intro k l
  rw [matrixEntry_matrixBlock]
  split_ifs
  · exact T.property
  · exact (groupVonNeumann G).zero_mem

def finiteMatrix (n : ℕ) (X : Fin n → Fin n → GroupOperator G) : GroupOperator (ℕ × G) :=
  ∑ i : Fin n, ∑ j : Fin n, matrixBlock i.val j.val (X i j)

@[simp] theorem matrixEntry_sum {ι : Type u_2} (s : Finset ι) (X : ι → GroupOperator (ℕ × G)) (i j : ℕ) :
    matrixEntry (∑ k∈s,X k) i j=∑ k∈s,matrixEntry (X k) i j := by
  classical
  induction s using Finset.induction_on with
  | empty => ext ξ g; simp [matrixEntry_apply]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [show matrixEntry (X a + ∑ k∈s,X k) i j=matrixEntry (X a) i j+matrixEntry (∑ k∈s,X k) i j by ext ξ g; simp [matrixEntry_apply],ih]

theorem matrixEntry_finiteMatrix (n : ℕ) (X : Fin n → Fin n → GroupOperator G) (i j : Fin n) :
    matrixEntry (finiteMatrix n X) i.val j.val=X i j := by
  classical
  simp [finiteMatrix,matrixEntry_sum,matrixEntry_matrixBlock,Fin.val_inj,ite_and]

theorem matrixEntry_finiteMatrix_out (n : ℕ) (X : Fin n → Fin n → GroupOperator G) (i j : ℕ)
    (h : n ≤ i ∨ n ≤ j) : matrixEntry (finiteMatrix n X) i j=0 := by
  classical
  simp only [finiteMatrix,matrixEntry_sum,matrixEntry_matrixBlock]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  rw [ite_eq_right]
  rintro ⟨rfl,rfl⟩
  cases h with
  | inl h => exact (not_le_of_gt a.isLt) h
  | inr h => exact (not_le_of_gt b.isLt) h

theorem finiteMatrix_mem [Group G] (n : ℕ) (X : Fin n → Fin n → groupVonNeumann G) :
    finiteMatrix n (fun i j => (X i j : GroupOperator G))∈stabilization G := by
  classical
  exact (stabilization G).sum_mem (fun i _ => (stabilization G).sum_mem (fun j _ => matrixBlock_mem i.val j.val (X i j)))

@[simp] theorem matrixBlock_add (i j : ℕ) (T S : GroupOperator G) :
    matrixBlock i j (T+S)=matrixBlock i j T+matrixBlock i j S := by
  ext ξ ⟨k,g⟩
  by_cases h : k=i <;> simp [h]

@[simp] theorem matrixBlock_smul (i j : ℕ) (c : ℂ) (T : GroupOperator G) :
    matrixBlock i j (c • T)=c • matrixBlock i j T := by
  ext ξ ⟨k,g⟩
  by_cases h : k=i <;> simp [h]

@[simp] theorem matrixBlock_sum {ι : Type u_3} (i j : ℕ) (s : Finset ι) (T : ι → GroupOperator G) :
    matrixBlock i j (∑ k∈s,T k)=∑ k∈s,matrixBlock i j (T k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha,ih]

 theorem matrixBlock_mul_finiteMatrix (n : ℕ) (i : ℕ) (j : Fin n) (T : GroupOperator G)
    (Y : Fin n → Fin n → GroupOperator G) :
    matrixBlock i j.val T * finiteMatrix n Y=∑ l : Fin n,matrixBlock i l.val (T*Y j l) := by
  classical
  simp only [finiteMatrix,Finset.mul_sum,matrixBlock_mul,Fin.val_inj]
  rw [Finset.sum_comm]
  congr 1
  ext l
  simp

 theorem finiteMatrix_mul (n : ℕ) (X Y : Fin n → Fin n → GroupOperator G) :
    finiteMatrix n X * finiteMatrix n Y=finiteMatrix n (fun i j => ∑ k : Fin n,X i k*Y k j) := by
  classical
  simp only [finiteMatrix,Finset.sum_mul]
  change (∑ i : Fin n,∑ j : Fin n,matrixBlock i.val j.val (X i j)*finiteMatrix n Y)=_
  simp only [matrixBlock_mul_finiteMatrix,matrixBlock_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

 theorem finiteMatrix_add (n : ℕ) (X Y : Fin n → Fin n → GroupOperator G) :
    finiteMatrix n (fun i j => X i j+Y i j)=finiteMatrix n X+finiteMatrix n Y := by
  classical
  simp [finiteMatrix,Finset.sum_add_distrib]

 theorem finiteMatrix_star (n : ℕ) (X : Fin n → Fin n → GroupOperator G) :
    star (finiteMatrix n X)=finiteMatrix n (fun i j => star (X j i)) := by
  classical
  simp only [finiteMatrix,star_sum (R := GroupOperator (ℕ × G)),matrixBlock_star]
  exact Finset.sum_comm

 theorem finiteMatrix_smul (n : ℕ) (X : Fin n → Fin n → GroupOperator G) (c : ℂ) :
    finiteMatrix n (fun i j => c • X i j)=c • finiteMatrix n X := by
  classical
  simp [finiteMatrix,Finset.smul_sum]

 def finiteDiagonal (n : ℕ) (T : GroupOperator G) : GroupOperator (ℕ × G) :=
  finiteMatrix n (fun i j => if i=j then T else 0)

 theorem finiteDiagonal_sum (n : ℕ) (T : GroupOperator G) :
    finiteDiagonal n T=∑ i : Fin n,matrixBlock i.val i.val T := by
  classical
  simp only [finiteDiagonal,finiteMatrix]
  apply Finset.sum_congr rfl
  intro i _
  have hh (j : Fin n) : matrixBlock i.val j.val (if i=j then T else 0)=if i=j then matrixBlock i.val j.val T else 0 := by split_ifs <;> simp
  simp_rw [hh]
  simp

 theorem finiteDiagonal_mul (n : ℕ) (T S : GroupOperator G) :
    finiteDiagonal n T*finiteDiagonal n S=finiteDiagonal n (T*S) := by
  classical
  rw [finiteDiagonal,finiteDiagonal,finiteMatrix_mul]
  congr 1
  funext i j
  simp

 theorem finiteDiagonal_star (n : ℕ) (T : GroupOperator G) :
    star (finiteDiagonal n T)=finiteDiagonal n (star T) := by
  classical
  rw [finiteDiagonal,finiteMatrix_star]
  congr 1
  funext i j
  split_ifs <;> simp_all [eq_comm,star_zero (R := GroupOperator G)]

theorem matrixBlock_sandwich (i j k l : ℕ) (A B : GroupOperator G) (T : GroupOperator (ℕ × G)) :
    matrixBlock i j A*T*matrixBlock k l B=matrixBlock i l (A*matrixEntry T j k*B) := by
  apply ContinuousLinearMap.ext
  intro ξ
  rfl

 theorem finiteDiagonal_sandwich (n : ℕ) (A B : GroupOperator G) (T : GroupOperator (ℕ × G)) :
    finiteDiagonal n A*T*finiteDiagonal n B=
      finiteMatrix n (fun i j => A*matrixEntry T i.val j.val*B) := by
  classical
  simp only [finiteDiagonal_sum,Finset.sum_mul,Finset.mul_sum,matrixBlock_sandwich,finiteMatrix]
  exact Finset.sum_comm

variable [Group G]

 def finiteProjection (n : ℕ) (p : groupVonNeumann G) : stabilization G :=
  ⟨finiteDiagonal n (p : GroupOperator G),by
    classical
    rw [finiteDiagonal_sum]
    exact (stabilization G).sum_mem (fun i _ => matrixBlock_mem i.val i.val p)⟩

 theorem finiteProjection_projection (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p) :
    IsStarProjection (finiteProjection n p) := by
  constructor
  · apply Subtype.ext
    change finiteDiagonal n (p : GroupOperator G)*finiteDiagonal n (p : GroupOperator G)=_
    rw [finiteDiagonal_mul]
    exact congrArg (finiteDiagonal n) (congrArg Subtype.val hp.isIdempotentElem.eq)
  · apply Subtype.ext
    change star (finiteDiagonal n (p : GroupOperator G))=_
    rw [finiteDiagonal_star]
    exact congrArg (finiteDiagonal n) (congrArg Subtype.val hp.isSelfAdjoint.star_eq)

 theorem finiteDiagonal_entries (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : Corner (finiteProjection n p) (finiteProjection_projection n p hp)) :
    finiteMatrix n (fun i j => (p : GroupOperator G)*matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val*(p : GroupOperator G))=
      (x.val : GroupOperator (ℕ × G)) := by
  rw [←finiteDiagonal_sandwich]
  change ((finiteProjection n p * x.val * finiteProjection n p : stabilization G) : GroupOperator (ℕ × G))=_
  rw [x.property.1,x.property.2]

end

open scoped ENNReal
variable {G : Type u_4} [Group G]

abbrev FiniteCorner (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p) :=
  Corner (finiteProjection n p) (finiteProjection_projection n p hp)

theorem finiteCorner_entry_sandwich (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) (i j : Fin n) :
    (p : GroupOperator G)*matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val*(p : GroupOperator G)=
      matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val := by
  have hh := congrArg (fun T : GroupOperator (ℕ × G) => matrixEntry T i.val j.val)
    (finiteDiagonal_entries n p hp x)
  rwa [matrixEntry_finiteMatrix] at hh

def finiteCornerEntry (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) (i j : Fin n) : Corner p hp := by
  let T : groupVonNeumann G := ⟨matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val,
    (mem_stabilization_iff_matrix _).mp x.val.property i.val j.val⟩
  have hh : p*T*p=T := Subtype.ext (finiteCorner_entry_sandwich n p hp x i j)
  refine ⟨T,?_,?_⟩
  · calc p*T=p*(p*T*p) := congrArg (p*·) hh.symm
         _=p*T*p := by rw [←mul_assoc,←mul_assoc,hp.isIdempotentElem.eq]
         _=T := hh
  · calc T*p=(p*T*p)*p := congrArg (·*p) hh.symm
         _=p*T*p := by rw [mul_assoc (p*T),hp.isIdempotentElem.eq]
         _=T := hh

theorem finiteCorner_reconstruct (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) :
    finiteMatrix n (fun i j => ((finiteCornerEntry n p hp x i j).val : GroupOperator G))=
      (x.val : GroupOperator (ℕ × G)) := by
  have he : (fun i j : Fin n => ((finiteCornerEntry n p hp x i j).val : GroupOperator G))=
      (fun i j : Fin n => (p : GroupOperator G)*matrixEntry (x.val : GroupOperator (ℕ × G)) i.val j.val*(p : GroupOperator G)) := by
    funext i j
    exact (finiteCorner_entry_sandwich n p hp x i j).symm
  rw [he]
  exact finiteDiagonal_entries n p hp x

theorem finiteCorner_ext (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x y : FiniteCorner n p hp) (h : ∀ i j,finiteCornerEntry n p hp x i j=finiteCornerEntry n p hp y i j) : x=y := by
  apply Subtype.ext
  apply Subtype.ext
  rw [←finiteCorner_reconstruct n p hp x,←finiteCorner_reconstruct n p hp y]
  congr 1
  funext i j
  rw [h i j]

 def finiteCornerOfMatrix (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (X : Fin n → Fin n → Corner p hp) : FiniteCorner n p hp := by
  let T : stabilization G := ⟨finiteMatrix n (fun i j => ((X i j).val : GroupOperator G)),
    finiteMatrix_mem n (fun i j => (X i j).val)⟩
  refine ⟨T,?_,?_⟩
  · apply Subtype.ext
    change finiteMatrix n (fun i j => if i=j then (p : GroupOperator G) else 0)*finiteMatrix n _=_
    rw [finiteMatrix_mul]
    congr 1
    funext i j
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    exact congrArg Subtype.val (X i j).property.1
  · apply Subtype.ext
    change finiteMatrix n _*finiteMatrix n (fun i j => if i=j then (p : GroupOperator G) else 0)=_
    rw [finiteMatrix_mul]
    congr 1
    funext i j
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact congrArg Subtype.val (X i j).property.2

@[simp] theorem finiteCornerEntry_ofMatrix (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (X : Fin n → Fin n → Corner p hp) (i j : Fin n) :
    finiteCornerEntry n p hp (finiteCornerOfMatrix n p hp X) i j=X i j := by
  apply Subtype.ext
  apply Subtype.ext
  exact matrixEntry_finiteMatrix n _ i j

@[simp] theorem finiteCornerEntry_add (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x y : FiniteCorner n p hp) (i j : Fin n) :
    finiteCornerEntry n p hp (x+y) i j=finiteCornerEntry n p hp x i j+finiteCornerEntry n p hp y i j := by
  apply Subtype.ext
  apply Subtype.ext
  ext ξ g
  simp [finiteCornerEntry,matrixEntry_apply]

@[simp] theorem finiteCornerEntry_smul (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) (c : ℂ) (i j : Fin n) :
    finiteCornerEntry n p hp (c • x) i j=c • finiteCornerEntry n p hp x i j := by
  apply Subtype.ext
  apply Subtype.ext
  ext ξ g
  simp [finiteCornerEntry,matrixEntry_apply]

@[simp] theorem finiteCornerEntry_star (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x : FiniteCorner n p hp) (i j : Fin n) :
    finiteCornerEntry n p hp (star x) i j=star (finiteCornerEntry n p hp x j i) := by
  apply Subtype.ext
  apply Subtype.ext
  exact matrixEntry_star _ i.val j.val

 theorem finiteCornerEntry_mul (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (x y : FiniteCorner n p hp) (i j : Fin n) :
    finiteCornerEntry n p hp (x*y) i j=∑ k : Fin n,finiteCornerEntry n p hp x i k*finiteCornerEntry n p hp y k j := by
  apply Subtype.ext
  apply Subtype.ext
  change matrixEntry ((x.val : GroupOperator (ℕ × G))*(y.val : GroupOperator (ℕ × G))) i.val j.val=_
  rw [←finiteCorner_reconstruct n p hp x,←finiteCorner_reconstruct n p hp y,finiteMatrix_mul,matrixEntry_finiteMatrix]
  simp

variable {H : Type u_5} [Group H]

def finiteCornerIso (n : ℕ) (p : groupVonNeumann G) (hp : IsStarProjection p)
    (q : groupVonNeumann H) (hq : IsStarProjection q) (e : Corner p hp ≃⋆ₐ[ℂ] Corner q hq) :
    FiniteCorner n p hp ≃⋆ₐ[ℂ] FiniteCorner n q hq where
  toFun x := finiteCornerOfMatrix n q hq (fun i j => e (finiteCornerEntry n p hp x i j))
  invFun x := finiteCornerOfMatrix n p hp (fun i j => e.symm (finiteCornerEntry n q hq x i j))
  left_inv x := by
    apply finiteCorner_ext n p hp
    intro i j
    simp only [finiteCornerEntry_ofMatrix,StarAlgEquiv.symm_apply_apply]
  right_inv x := by
    apply finiteCorner_ext n q hq
    intro i j
    simp only [finiteCornerEntry_ofMatrix,StarAlgEquiv.apply_symm_apply]
  map_mul' x y := by
    apply finiteCorner_ext n q hq
    intro i j
    simp only [finiteCornerEntry_ofMatrix,finiteCornerEntry_mul]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact e.map_mul' _ _
  map_add' x y := by
    apply finiteCorner_ext n q hq
    intro i j
    simp only [finiteCornerEntry_add,finiteCornerEntry_ofMatrix]
    exact e.map_add' _ _
  map_smul' c x := by
    apply finiteCorner_ext n q hq
    intro i j
    simp only [finiteCornerEntry_smul,finiteCornerEntry_ofMatrix]
    exact e.map_smul' c _
  map_star' x := by
    apply finiteCorner_ext n q hq
    intro i j
    simp only [finiteCornerEntry_star,finiteCornerEntry_ofMatrix]
    exact e.map_star' _

end FreeGroupFactorMain.Amplification

end

end OAI
