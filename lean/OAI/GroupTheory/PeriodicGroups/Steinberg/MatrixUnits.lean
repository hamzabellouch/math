import Mathlib
import OAI.GroupTheory.PeriodicGroups.Steinberg.BandFactorization

namespace OAI

section
universe u v w
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
def numericUnits (P : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ) : (Matrix (Fin N) (Fin N) R)ˣ :=
  Units.map (algebraMap (ZMod 2) R).mapMatrix.toMonoidHom P
lemma bigBasisUnits_entry {S : Type*} [Ring S] (P : (Matrix (Fin N) (Fin N) S)ˣ)
    (i j : Fin n) (s t : Fin N) :
    (bigBasisUnits P).val (blockIndex i s) (blockIndex j t)=if i=j then P.val s t else 0 := by
  change flattenRing (Matrix.diagonal (fun _ : Fin n=>P.val)) (blockIndex i s) (blockIndex j t)=_
  simp only [flattenRing,RingEquiv.trans_apply,Matrix.coe_reindexRingEquiv,Matrix.reindex_apply,
    Matrix.submatrix_apply,blockIndex,Equiv.symm_apply_apply,Matrix.compRingEquiv_apply,Matrix.comp_apply]
  by_cases hij : i=j <;> simp [Matrix.diagonal,hij]
lemma bigBasisUnits_map (P : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ) :
    Units.map (algebraMap (ZMod 2) R).mapMatrix.toMonoidHom (bigBasisUnits (n:=n) P)=
      bigBasisUnits (numericUnits (R:=R) P) := by
  apply Units.ext
  apply Matrix.ext
  intro u v
  obtain ⟨⟨i,s⟩,rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨j,t⟩,rfl⟩ := finProdFinEquiv.surjective v
  change algebraMap (ZMod 2) R ((bigBasisUnits P).val (blockIndex i s) (blockIndex j t))=
    (bigBasisUnits (numericUnits (R:=R) P)).val (blockIndex i s) (blockIndex j t)
  rw [bigBasisUnits_entry,bigBasisUnits_entry]
  split_ifs <;> simp [numericUnits]
lemma numerical_big_lift (P : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ) :
    ∃b : Steinberg (n*N) R,Elementary.representation b=bigBasisUnits (numericUnits (R:=R) P) := by
  have hdet : (bigBasisUnits (n:=n) P).val.det≠0 :=
    (Matrix.isUnits_det_units (bigBasisUnits (n:=n) P)).ne_zero
  obtain ⟨b,hb⟩ := numerical_matrix_lift (bigBasisUnits (n:=n) P).val hdet
  refine ⟨Steinberg.map (algebraMap (ZMod 2) R) b,?_⟩
  have hb' : Elementary.representation b=bigBasisUnits P := Units.ext hb
  have he := DFunLike.congr_fun (Elementary.representation_map (n:=n*N) (algebraMap (ZMod 2) R)) b
  change Elementary.representation (Steinberg.map (algebraMap (ZMod 2) R) b)=_
  simpa only [MonoidHom.comp_apply,hb',bigBasisUnits_map] using he
lemma numeric_conj_scalar (P : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ) (a : R) :
    coefficientConj (numericUnits (R:=R) P) (Matrix.scalar (Fin N) a)=Matrix.scalar (Fin N) a := by
  change (numericUnits (R:=R) P).val*Matrix.scalar (Fin N) a*(numericUnits (R:=R) P).inv=_
  have hc := (numeric_scalar_commute (R:=R) P.val a).eq
  change Matrix.scalar (Fin N) a*(numericUnits (R:=R) P).val=(numericUnits (R:=R) P).val*Matrix.scalar (Fin N) a at hc
  rw [←hc,mul_assoc,Units.val_inv,mul_one]
lemma numeric_conj_matrix (P : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ)
    (T : Matrix (Fin N) (Fin N) (ZMod 2)) :
    coefficientConj (numericUnits (R:=R) P) (numericMatrix (R:=R) T)=numericMatrix (R:=R) (P.val*T*P.inv) := by
  change (algebraMap (ZMod 2) R).mapMatrix P.val*(algebraMap (ZMod 2) R).mapMatrix T*
    (algebraMap (ZMod 2) R).mapMatrix P.inv=(algebraMap (ZMod 2) R).mapMatrix (P.val*T*P.inv)
  simp only [map_mul]
lemma matrixEval_conjugacy (P : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ)
    (T : Matrix (Fin N) (Fin N) (ZMod 2)) :
    (coefficientConj (numericUnits (R:=R) P)).comp (matrixEvalRingHom T)=
      matrixEvalRingHom (R:=R) (P.val*T*P.inv) := by
  apply Polynomial.ringHom_ext
  · intro a
    change coefficientConj (numericUnits (R:=R) P) (Polynomial.eval₂ _ _ (Polynomial.C a))=
      Polynomial.eval₂ _ _ (Polynomial.C a)
    rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
    exact numeric_conj_scalar P a
  · change coefficientConj (numericUnits (R:=R) P) (Polynomial.eval₂ _ _ Polynomial.X)=
      Polynomial.eval₂ _ _ Polynomial.X
    rw [Polynomial.eval₂_X,Polynomial.eval₂_X]
    exact numeric_conj_matrix P T

theorem stable_numerical_similarity (hn : 3 ≤ n)
    (P : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ) (T : Matrix (Fin N) (Fin N) (ZMod 2))
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1) :
    padSteinberg (matrixSteinbergEval T u)=padSteinberg (matrixSteinbergEval (P.val*T*P.inv) u) := by
  obtain ⟨b,hb⟩ := numerical_big_lift (n:=n) (R:=R) P
  have he := stable_basis_change hn (numericUnits (R:=R) P) b hb (Steinberg.map (matrixEvalRingHom T) u)
  rw [Steinberg.map_map,matrixEval_conjugacy] at he
  have hz := stabilized_kernel_central (matrixSteinbergEval T u) (matrixSteinbergEval_kernel T u hu)
  have hc : Commute (padSteinberg b) (padSteinberg (matrixSteinbergEval T u)) :=
    Subgroup.mem_center_iff.mp hz _
  change padSteinberg (b*matrixSteinbergEval T u*b⁻¹)=padSteinberg (matrixSteinbergEval (P.val*T*P.inv) u) at he
  simpa only [map_mul,map_inv,CommutatorCalculus.conj_of_commute hc] using he
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {N : ℕ}
def pascalMatrix (N : ℕ) : Matrix (Fin N) (Fin N) (ZMod 2) := fun s t=>(s.val.choose t.val : ZMod 2)
lemma pascal_lower : (pascalMatrix N).IsLowerTriangular := by
  intro s t hst
  change s.val<t.val at hst
  change ((s.val.choose t.val : ℕ) : ZMod 2)=0
  rw [Nat.choose_eq_zero_of_lt hst,Nat.cast_zero]
lemma pascal_det : (pascalMatrix N).det=1 := by
  rw [Matrix.det_of_isLowerTriangular _ pascal_lower]
  simp [pascalMatrix]
lemma matrix_mul_truncated {R : Type*} [Ring R] (A : Matrix (Fin N) (Fin N) R) (s t : Fin N) :
    (A*truncatedShift N R) s t=if h : t.val=0 then 0 else A s ⟨t.val-1,by have := t.isLt;omega⟩ := by
  rw [Matrix.mul_apply]
  by_cases ht : t.val=0
  · rw [dite_eq_left ht]
    apply Finset.sum_eq_zero
    intro k _
    have he : k.val+1≠t.val := by omega
    simp [truncatedShift,he]
  · rw [dite_eq_right ht]
    let k : Fin N := ⟨t.val-1,by have := t.isLt;omega⟩
    rw [Finset.sum_eq_single k]
    · have he : k.val+1=t.val := by dsimp [k];omega
      simp [truncatedShift,he,k]
    · intro u _ huk
      have he : u.val+1≠t.val := by
        intro he
        apply huk
        apply Fin.ext
        dsimp [k]
        omega
      simp [truncatedShift,he]
    · simp
lemma cyclic_mul_matrix {R : Type*} [Ring R] (hN : 0<N)
    (A : Matrix (Fin N) (Fin N) R) (s t : Fin N) :
    (cyclicShift N R*A) s t=A ⟨(s.val+1)%N,Nat.mod_lt _ hN⟩ t := by
  rw [Matrix.mul_apply]
  let k : Fin N := ⟨(s.val+1)%N,Nat.mod_lt _ hN⟩
  rw [Finset.sum_eq_single k]
  · simp [cyclicShift,k]
  · intro u _ huk
    have he : (s.val+1)%N≠u.val := by intro he;apply huk;apply Fin.ext;exact he.symm
    simp [cyclicShift,he]
  · simp
lemma pascal_times_unipotent (s t : Fin N) :
    (pascalMatrix N*(1+truncatedShift N (ZMod 2))) s t=((s.val+1).choose t.val : ZMod 2) := by
  rw [mul_add,mul_one,Matrix.add_apply,matrix_mul_truncated]
  by_cases ht : t.val=0
  · simp [ht,pascalMatrix]
  · rw [dite_eq_right ht]
    change (s.val.choose t.val : ZMod 2)+(s.val.choose (t.val-1) : ZMod 2)=_
    have hk : t.val=(t.val-1)+1 := by omega
    conv_rhs => rw [hk,Nat.choose_succ_succ',Nat.cast_add]
    rw [←hk,add_comm]
lemma power_two_choose (k j : ℕ) (hj : j<2^k) :
    ((2^k).choose j : ZMod 2)=((0 : ℕ).choose j : ZMod 2) := by
  by_cases hz : j=0
  · simp [hz]
  · have hd : 2 ∣ (2^k).choose j := Nat.prime_two.dvd_choose_pow hz (by omega)
    have hc : ((2^k).choose j : ZMod 2)=0 := (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mpr hd
    rw [hc]
    have hj0 : 0<j := by omega
    rw [Nat.choose_eq_zero_of_lt hj0,Nat.cast_zero]
lemma cyclic_pascal (k : ℕ) :
    cyclicShift (2^k) (ZMod 2)*pascalMatrix (2^k)=
      pascalMatrix (2^k)*(1+truncatedShift (2^k) (ZMod 2)) := by
  ext s t
  rw [cyclic_mul_matrix (by positivity),pascal_times_unipotent]
  change (((s.val+1)%(2^k)).choose t.val : ZMod 2)=((s.val+1).choose t.val : ZMod 2)
  by_cases hs : s.val+1<2^k
  · rw [Nat.mod_eq_of_lt hs]
  · have he : s.val+1=2^k := by have := s.isLt;omega
    rw [he,Nat.mod_self]
    exact (power_two_choose k t.val t.isLt).symm

theorem cyclic_triangularization (k : ℕ) :
    ∃P : (Matrix (Fin (2^k)) (Fin (2^k)) (ZMod 2))ˣ,
      P.inv*cyclicShift (2^k) (ZMod 2)*P.val=1+truncatedShift (2^k) (ZMod 2) := by
  have hi : IsUnit (pascalMatrix (2^k)) := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [pascal_det];exact isUnit_one)
  obtain ⟨P,hP⟩ := hi
  refine ⟨P,?_⟩
  have he := cyclic_pascal k
  rw [←hP] at he
  calc
    _ = P.inv*(cyclicShift (2^k) (ZMod 2)*P.val) := by simp [mul_assoc]
    _ = P.inv*(P.val*(1+truncatedShift (2^k) (ZMod 2))) := congrArg (fun A=>P.inv*A) he
    _ = _ := by simp [←mul_assoc]
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
lemma one_add_truncated_upper (N : ℕ) :
    ((1 : Matrix (Fin N) (Fin N) (ZMod 2))+truncatedShift N (ZMod 2)).IsUpperTriangular := by
  intro s t hts
  have hne : s≠t := ne_of_gt hts
  simp only [Matrix.add_apply,Matrix.one_apply,ite_eq_right hne,truncatedShift_upper hts,zero_add]
lemma one_add_truncated_diag (N : ℕ) (s : Fin N) :
    ((1 : Matrix (Fin N) (Fin N) (ZMod 2))+truncatedShift N (ZMod 2)) s s=1 := by
  simp [Matrix.add_apply,truncatedShift_diag]

theorem stable_cyclic_evaluation (hn : 3≤n) (k : ℕ)
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1) :
    padSteinberg (matrixSteinbergEval (cyclicShift (2^k) (ZMod 2)) u)=
      padSteinberg (diagonalCopy (N:=2^k) (Steinberg.map (scalarEval 1) u)) := by
  obtain ⟨P,hP⟩ := cyclic_triangularization k
  have he := stable_numerical_similarity hn P⁻¹ (cyclicShift (2^k) (ZMod 2)) u hu
  change padSteinberg (matrixSteinbergEval (cyclicShift (2^k) (ZMod 2)) u)=
    padSteinberg (matrixSteinbergEval (P.inv*cyclicShift (2^k) (ZMod 2)*P.val) u) at he
  rw [hP,triangular_evaluation (one_add_truncated_upper _) 1 (one_add_truncated_diag _) u hu] at he
  exact he

theorem stable_diagonal_evaluations (hn : 3≤n) (l : List (Root n×Polynomial R))
    (hm : 1≤l.length) (d k : ℕ) (hl : ∀pa∈l,pa.2.natDegree≤d)
    (hN : 2*(l.length+1)*max 1 d<2^k)
    (hu : Elementary.representation (rootWord l)=1) :
    padSteinberg (diagonalCopy (N:=2^k) (Steinberg.map (scalarEval 1) (rootWord l)))=
      padSteinberg (diagonalCopy (N:=2^k) (Steinberg.map (scalarEval 0) (rootWord l))) := by
  rw [←stable_cyclic_evaluation hn k _ hu,wrap_removal l hm d hl hN hu]
  rw [triangular_evaluation truncatedShift_upper 0 truncatedShift_diag _ hu]
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def copyMatrixHom (s : Fin N) : Matrix (Fin n) (Fin n) R →* Matrix (Fin (n*N)) (Fin (n*N)) R :=
  (Matrix.reindexRingEquiv R finProdFinEquiv).toMonoidHom.comp
    ((Matrix.blockDiagonalRingHom (Fin n) (Fin N) R).toMonoidHom.comp (MonoidHom.mulSingle (fun _ : Fin N=>Matrix (Fin n) (Fin n) R) s))
def copyUnitsHom (s : Fin N) : (Matrix (Fin n) (Fin n) R)ˣ →* (Matrix (Fin (n*N)) (Fin (n*N)) R)ˣ :=
  Units.map (copyMatrixHom s)
lemma copyUnitsHom_e (s : Fin N) (p : Root n) (a : R) :
    copyUnitsHom s (Elementary.e p a)=Elementary.e (blockPosition p (s,s)) a := by
  apply Units.ext
  apply Matrix.ext
  intro u v
  obtain ⟨⟨i,t⟩,rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨j,z⟩,rfl⟩ := finProdFinEquiv.surjective v
  change (Matrix.blockDiagonal (Pi.mulSingle s (1+Matrix.single p.row p.col a))).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm (finProdFinEquiv (i,t)) (finProdFinEquiv (j,z))=
    (1+Matrix.single (blockIndex p.row s) (blockIndex p.col s) a) (finProdFinEquiv (i,t)) (finProdFinEquiv (j,z))
  simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply,Matrix.blockDiagonal_apply,
    Pi.mulSingle_apply,Matrix.add_apply,Matrix.one_apply,Matrix.single_apply,blockIndex]
  by_cases htz : t=z <;> by_cases hts : t=s <;>
    simp_all [Matrix.add_apply,Matrix.one_apply,Matrix.single_apply,Prod.ext_iff,eq_comm,and_comm]
lemma copy_representation (s : Fin N) :
    Elementary.representation.comp (copyMap (n:=n) (R:=R) s)= (copyUnitsHom s).comp Elementary.representation := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply,copyMap_x,Elementary.representation_x,copyUnitsHom_e]
lemma copy_kernel (s : Fin N) (u : Steinberg n R) (hu : Elementary.representation u=1) :
    Elementary.representation (copyMap s u)=1 := by
  have he := DFunLike.congr_fun (copy_representation (n:=n) (R:=R) s) u
  simpa only [MonoidHom.comp_apply,hu,map_one] using he
variable [Algebra (ZMod 2) R]
def swapUnits (s t : Fin N) : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ where
  val := Matrix.swap (ZMod 2) s t
  inv := Matrix.swap (ZMod 2) s t
  val_inv := Matrix.swap_mul_self s t
  inv_val := Matrix.swap_mul_self s t
lemma swap_coefficient_single (s t : Fin N) (a : R) :
    coefficientConj (numericUnits (R:=R) (swapUnits s t)) (Matrix.single s s a)=Matrix.single t t a := by
  change (Matrix.swap (ZMod 2) s t).map (algebraMap (ZMod 2) R)*Matrix.single s s a*
    (Matrix.swap (ZMod 2) s t).map (algebraMap (ZMod 2) R)=_
  rw [Matrix.map_swap,Matrix.swap,PEquiv.toMatrix_toPEquiv_mul,PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  have h (i : Fin N) : s=(Equiv.swap s t) i ↔ t=i := by
    constructor
    · intro h
      have he := congrArg (Equiv.swap s t) h
      simpa using he
    · intro he
      subst i
      simp
  simp only [Matrix.submatrix_apply,Equiv.symm_swap,Matrix.single_apply]
  simp only [id_eq,h]

theorem stable_copy_eq (hn : 3≤n) (s t : Fin N) (u : Steinberg n R)
    (hu : Elementary.representation u=1) : padSteinberg (copyMap s u)=padSteinberg (copyMap t u) := by
  obtain ⟨b,hb⟩ := numerical_big_lift (n:=n) (R:=R) (swapUnits s t)
  let f := (MulAut.conj b).toMonoidHom.comp (copyMap (n:=n) (R:=R) s)
  have he : Elementary.representation.comp f=Elementary.representation.comp (copyMap t) := by
    apply Steinberg.hom_ext
    intro p a
    change Elementary.representation (b*copyMap s (Steinberg.x p a)*b⁻¹)=
      Elementary.representation (copyMap t (Steinberg.x p a))
    rw [copyMap_x,copyMap_x,←blockRoot_single p s s a,←blockRoot_single p t t a,
      map_mul,map_mul,map_inv,hb,big_conjugates_elementary,swap_coefficient_single]
  have hf := DFunLike.congr_fun (stable_uniqueness hn f (copyMap t) (fun v=>DFunLike.congr_fun he v)) u
  have hz := stabilized_kernel_central (copyMap s u) (copy_kernel s u hu)
  have hc : Commute (padSteinberg b) (padSteinberg (copyMap s u)) := Subgroup.mem_center_iff.mp hz _
  change padSteinberg (b*copyMap s u*b⁻¹)=padSteinberg (copyMap t u) at hf
  simpa only [map_mul,map_inv,CommutatorCalculus.conj_of_commute hc] using hf
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R S : Type*} [Ring R] [Ring S]
lemma pad_ringMap (f : R →+* S) (u : Steinberg n R) :
    Steinberg.map f (padSteinberg u)=padSteinberg (Steinberg.map f u) := by
  have he : (Steinberg.map f).comp padSteinberg=padSteinberg.comp (Steinberg.map (n:=n) f) := by
    apply Steinberg.hom_ext
    intro p a
    simp [padSteinberg,Steinberg.map_x]
  exact DFunLike.congr_fun he u
lemma copy_ringMap (f : R →+* S) (s : Fin N) (u : Steinberg n R) :
    Steinberg.map f (copyMap s u)=copyMap s (Steinberg.map f u) := by
  have he : (Steinberg.map f).comp (copyMap s)=(copyMap s).comp (Steinberg.map (n:=n) f) := by
    apply Steinberg.hom_ext
    intro p a
    simp [Steinberg.map_x]
  exact DFunLike.congr_fun he u
lemma diagonalCopy_ringMap (f : R →+* S) (u : Steinberg n R) :
    Steinberg.map f (diagonalCopy (N:=N) u)=diagonalCopy (N:=N) (Steinberg.map f u) := by
  change Steinberg.map f (Finset.noncommProd Finset.univ (fun s : Fin N=>copyMap s u) (fun _ _ _ _ h=>copy_commute h u u))=
    Finset.noncommProd Finset.univ (fun s : Fin N=>copyMap s (Steinberg.map f u)) (fun _ _ _ _ h=>copy_commute h _ _)
  erw [Finset.map_noncommProd]
  apply Finset.noncommProd_congr rfl
  intro s _
  exact copy_ringMap f s u
variable [Algebra (ZMod 2) R]
lemma stable_diagonalCopy_pow (hn : 3≤n) (s : Fin N) (u : Steinberg n R)
    (hu : Elementary.representation u=1) :
    padSteinberg (diagonalCopy (N:=N) u)=padSteinberg (copyMap s u)^N := by
  change padSteinberg (Finset.noncommProd Finset.univ (fun t : Fin N=>copyMap t u) (fun _ _ _ _ h=>copy_commute h u u))=_
  erw [Finset.map_noncommProd]
  have he := Finset.noncommProd_eq_pow_card Finset.univ (fun t : Fin N=>padSteinberg (copyMap t u))
    (fun t ht z hz htz=>(copy_commute htz u u).map padSteinberg)
    (padSteinberg (copyMap s u)) (fun t _=>stable_copy_eq hn t s u hu)
  simpa using he

lemma stable_ground_diagonal_periodic (hn : 3≤n) (hN : 0<N) (v : Steinberg n (ZMod 2)) :
    ∃m : ℕ, 0 < m ∧
      (padSteinberg (diagonalCopy (N:=N) (Steinberg.map (algebraMap (ZMod 2) R) v)))^m=1 := by
  have hnN : 3≤n*N := by nlinarith
  obtain ⟨m,hm,he⟩ := stabilized_field_periodic hnN (diagonalCopy (N:=N) v)
  refine ⟨m,hm,?_⟩
  have hf := congrArg (Steinberg.map (algebraMap (ZMod 2) R)) he
  simpa only [map_pow,map_one,pad_ringMap,diagonalCopy_ringMap] using hf

theorem stable_word_copy_torsion (hn : 3≤n) (l : List (Root n×Polynomial R))
    (hm : 1≤l.length) (d k : ℕ) (hl : ∀pa∈l,pa.2.natDegree≤d)
    (hN : 2*(l.length+1)*max 1 d<2^k)
    (hu : Elementary.representation (rootWord l)=1)
    (v : Steinberg n (ZMod 2))
    (hv : Steinberg.map (scalarEval 0) (rootWord l)=Steinberg.map (algebraMap (ZMod 2) R) v)
    (s : Fin (2^k)) :
    ∃m : ℕ, 0 < m ∧
      (padSteinberg (copyMap s (Steinberg.map (scalarEval 1) (rootWord l))))^m=1 := by
  obtain ⟨a,ha,he⟩ := stable_ground_diagonal_periodic (R:=R) hn (show 0<2^k by positivity) v
  have hdiag := stable_diagonal_evaluations hn l hm d k hl hN hu
  rw [hv] at hdiag
  have hz := scalarEval_kernel 1 (rootWord l) hu
  rw [←hdiag,stable_diagonalCopy_pow hn s _ hz] at he
  refine ⟨2^k*a,Nat.mul_pos (by positivity) ha,?_⟩
  simpa only [pow_mul] using he
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]

theorem polynomial_kernel_copy_torsion (hn : 3≤n)
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1)
    (v : Steinberg n (ZMod 2))
    (hv : Steinberg.map (scalarEval 0) u=Steinberg.map (algebraMap (ZMod 2) R) v) :
    ∃k : ℕ,∃s : Fin (2^k),∃m : ℕ, 0 < m ∧
      (padSteinberg (copyMap s (Steinberg.map (scalarEval 1) u)))^m=1 := by
  obtain ⟨l,hl⟩ := exists_rootWord u
  let p : Root n := ⟨⟨0,by omega⟩,⟨1,by omega⟩,by intro he;have hh : (0 : ℕ)=1 := congrArg Fin.val he;omega⟩
  let l' := l++[(p,(0 : Polynomial R))]
  have hl' : rootWord l'=u := by simp [l',rootWord,Steinberg.x_zero] at hl ⊢;exact hl
  have hm : 1≤l'.length := by dsimp [l'];simp
  let d := l'.toFinset.sup (fun pa=>pa.2.natDegree)
  have hd : ∀pa∈l',pa.2.natDegree≤d := by
    intro pa hpa
    exact Finset.le_sup (f:=fun pa : Root n×Polynomial R=>pa.2.natDegree) (List.mem_toFinset.mpr hpa)
  let k := 2*(l'.length+1)*max 1 d
  have hk : 2*(l'.length+1)*max 1 d<2^k := Nat.lt_two_pow_self
  let s : Fin (2^k) := ⟨0,by positivity⟩
  have hmat : Elementary.representation (rootWord l')=1 := hl' ▸ hu
  have hval : Steinberg.map (scalarEval 0) (rootWord l')=Steinberg.map (algebraMap (ZMod 2) R) v := hl' ▸ hv
  obtain ⟨m,hm,he⟩ := stable_word_copy_torsion hn l' hm d k hd hk hmat v hval s
  refine ⟨k,s,m,hm,?_⟩
  simpa only [hl'] using he
end
end SourceBurnside.Kernel
namespace SourceBurnside.WordAlgebra.Table
noncomputable section
open Classical
variable {α : Type*}
lemma scalarEval_zero (T : Table α) :
    Kernel.scalarEval (R:=T.Algebra (K:=ZMod 2)) 0=T.evalZero.toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [Kernel.scalarEval,evalZero]
  · simp [Kernel.scalarEval,evalZero]
lemma scalarEval_one (T : Table α) :
    Kernel.scalarEval (R:=T.Algebra (K:=ZMod 2)) 1=T.evalOne.toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [Kernel.scalarEval,evalOne]
  · simp [Kernel.scalarEval,evalOne]
end
end SourceBurnside.WordAlgebra.Table
namespace SourceBurnside.ConcreteSource
noncomputable section

theorem kernel_coordinate_torsion {n : ℕ} (hn : 3≤n) (u : Steinberg n R)
    (hu : Elementary.representation u=1) :
    ∃k : ℕ,∃s : Fin (2^k),∃m : ℕ, 0 < m ∧
      (Kernel.padSteinberg (Kernel.copyMap s u))^m=1 := by
  have h0 : Kernel.scalarEval (R:=R) 0=evalZero.toRingHom :=
    (machine.table height (by rfl)).scalarEval_zero
  have h1 : Kernel.scalarEval (R:=R) 1=evalOne.toRingHom :=
    (machine.table height (by rfl)).scalarEval_one
  have hv : Steinberg.map (Kernel.scalarEval 0) (gradedElement u)=
      Steinberg.map (algebraMap (ZMod 2) R) (groundElement u) := by
    rw [h0]
    exact gradedElement_zero u
  obtain ⟨k,s,m,hm,he⟩ := Kernel.polynomial_kernel_copy_torsion hn (gradedElement u)
    (gradedElement_matrix_one u hu) (groundElement u) hv
  refine ⟨k,s,m,hm,?_⟩
  rw [h1,gradedElement_one] at he
  exact he
end
end SourceBurnside.ConcreteSource
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n m : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
def permutationUnits (σ : Equiv.Perm (Fin m)) : (Matrix (Fin m) (Fin m) (ZMod 2))ˣ where
  val := σ⁻¹.permMatrix (ZMod 2)
  inv := σ.permMatrix (ZMod 2)
  val_inv := by rw [←Matrix.permMatrix_mul];simp
  inv_val := by rw [←Matrix.permMatrix_mul];simp
lemma numerical_lift (P : (Matrix (Fin m) (Fin m) (ZMod 2))ˣ) :
    ∃b : Steinberg m R,Elementary.representation b=numericUnits (R:=R) P := by
  obtain ⟨b,hb⟩ := numerical_matrix_lift P.val (Matrix.isUnits_det_units P).ne_zero
  refine ⟨Steinberg.map (algebraMap (ZMod 2) R) b,?_⟩
  have hb' : Elementary.representation b=P := Units.ext hb
  have he := DFunLike.congr_fun (Elementary.representation_map (n:=m) (algebraMap (ZMod 2) R)) b
  simpa only [MonoidHom.comp_apply,hb',numericUnits] using he
lemma permutation_conjugates_e (σ : Equiv.Perm (Fin m)) (p : Root m) (a : R) :
    numericUnits (R:=R) (permutationUnits σ)*Elementary.e p a*
      (numericUnits (R:=R) (permutationUnits σ))⁻¹=
      Elementary.e (p.map σ σ.injective) a := by
  apply Units.ext
  change (((σ⁻¹).permMatrix (ZMod 2)).map (algebraMap (ZMod 2) R))*(1+Matrix.single p.row p.col a)*
    ((σ.permMatrix (ZMod 2 )).map (algebraMap (ZMod 2) R))=1+Matrix.single (σ p.row) (σ p.col) a
  simp only [Equiv.Perm.permMatrix,PEquiv.map_toMatrix,PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv,Equiv.Perm.inv_def]
  ext i j
  simp [Matrix.submatrix_apply,Matrix.add_apply,Matrix.one_apply,Matrix.single_apply,
    ← Equiv.eq_symm_apply]

theorem stable_permutation_fixed (hm : 3 ≤ m) (σ : Equiv.Perm (Fin m))
    (u : Steinberg m R) (hu : Elementary.representation u=1) :
    padSteinberg (Steinberg.coordinateMap σ σ.injective u)=padSteinberg u := by
  obtain ⟨b,hb⟩ := numerical_lift (R:=R) (permutationUnits σ)
  let f := (MulAut.conj b).toMonoidHom
  let g := Steinberg.coordinateMap (R:=R) σ σ.injective
  have he : Elementary.representation.comp f=Elementary.representation.comp g := by
    apply Steinberg.hom_ext
    intro p a
    change Elementary.representation (b*Steinberg.x p a*b⁻¹)=_
    rw [map_mul,map_mul,map_inv,hb,Elementary.representation_x]
    change _=Elementary.representation (Steinberg.x (p.map σ σ.injective) a)
    rw [Elementary.representation_x]
    exact permutation_conjugates_e σ p a
  have hf := DFunLike.congr_fun (stable_uniqueness hm f g (fun v=>DFunLike.congr_fun he v)) u
  have hz := stabilized_kernel_central u hu
  have hc : Commute (padSteinberg b) (padSteinberg u) := Subgroup.mem_center_iff.mp hz _
  change padSteinberg (b*u*b⁻¹)=padSteinberg (Steinberg.coordinateMap σ σ.injective u) at hf
  simpa only [map_mul,map_inv,CommutatorCalculus.conj_of_commute hc] using hf.symm
omit [Algebra (ZMod 2) R] in
lemma coordinateMap_comp (f : Fin n→Fin m) (hf : Function.Injective f) {q : ℕ}
    (g : Fin m→Fin q) (hg : Function.Injective g) :
    (Steinberg.coordinateMap (R:=R) g hg).comp (Steinberg.coordinateMap f hf)=
      Steinberg.coordinateMap (g∘f) (hg.comp hf) := by
  apply Steinberg.hom_ext
  intro p a
  rfl

theorem stable_copy_to_standard (hn : 3 ≤ n) {N : ℕ} (hN : 0<N) (s : Fin N)
    (u : Steinberg n R) (hu : Elementary.representation u=1) :
    padSteinberg (copyMap s u)=
      padSteinberg (Steinberg.coordinateMap (Fin.castLE (show n≤n*N by nlinarith))
        (Fin.castLE_injective _) u) := by
  have hnm : n≤n*N := by nlinarith
  let f := fun i : Fin n=>blockIndex i s
  have hf : Function.Injective f := fun i j he=>congrArg Prod.fst (finProdFinEquiv.injective he)
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair f (Fin.castLE hnm) hf (Fin.castLE_injective _)
  have he := stable_permutation_fixed (R:=R) (by nlinarith : 3 ≤ n*N) σ (copyMap s u) (copy_kernel s u hu)
  have H : (Steinberg.coordinateMap (R:=R) σ σ.injective).comp (copyMap s)=
      Steinberg.coordinateMap (Fin.castLE hnm) (Fin.castLE_injective _) := by
    change (Steinberg.coordinateMap σ σ.injective).comp (Steinberg.coordinateMap f hf)=_
    rw [coordinateMap_comp]
    have heq : σ∘f=Fin.castLE hnm := funext hσ
    simp only [heq]
  have hU := DFunLike.congr_fun H u
  change Steinberg.coordinateMap σ σ.injective (copyMap s u)=
    Steinberg.coordinateMap (Fin.castLE hnm) (Fin.castLE_injective _) u at hU
  exact he.symm.trans (congrArg padSteinberg hU)
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
omit [Algebra (ZMod 2) R] in
lemma pad_standard {q : ℕ} (hnq : n≤q) (u : Steinberg n R) :
    padSteinberg (Steinberg.coordinateMap (Fin.castLE hnq) (Fin.castLE_injective _) u)=
      Steinberg.coordinateMap (Fin.castLE (hnq.trans (Nat.le_succ q))) (Fin.castLE_injective _) u := by
  have H : padSteinberg.comp (Steinberg.coordinateMap (R:=R) (Fin.castLE hnq) (Fin.castLE_injective _))=
      Steinberg.coordinateMap (Fin.castLE (hnq.trans (Nat.le_succ q))) (Fin.castLE_injective _) := by
    apply Steinberg.hom_ext
    intro p a
    rfl
  exact DFunLike.congr_fun H u

theorem polynomial_kernel_standard_torsion (hn : 3≤n)
    (u : Steinberg n (Polynomial R)) (hu : Elementary.representation u=1)
    (v : Steinberg n (ZMod 2))
    (hv : Steinberg.map (scalarEval 0) u=Steinberg.map (algebraMap (ZMod 2) R) v) :
    ∃q : ℕ,∃hnq : n≤q,∃m : ℕ, 0 < m ∧
      (Steinberg.coordinateMap (Fin.castLE hnq) (Fin.castLE_injective _)
        (Steinberg.map (scalarEval 1) u))^m=1 := by
  obtain ⟨k,s,m,hm,he⟩ := polynomial_kernel_copy_torsion hn u hu v hv
  have hN : 0<2^k := by positivity
  have hnq : n≤n*2^k := by nlinarith
  have hcopy := stable_copy_to_standard hn hN s (Steinberg.map (scalarEval 1) u) (scalarEval_kernel 1 u hu)
  rw [hcopy,pad_standard] at he
  exact ⟨n*2^k+1,hnq.trans (Nat.le_succ _),m,hm,he⟩
end
end SourceBurnside.Kernel
namespace SourceBurnside.ConcreteSource
noncomputable section

theorem kernel_standard_stable_torsion {n : ℕ} (hn : 3≤n) (u : Steinberg n R)
    (hu : Elementary.representation u=1) :
    ∃q : ℕ,∃hnq : n≤q,∃m : ℕ, 0 < m ∧
      (Steinberg.coordinateMap (Fin.castLE hnq) (Fin.castLE_injective _) u)^m=1 := by
  have h0 : Kernel.scalarEval (R:=R) 0=evalZero.toRingHom :=
    (machine.table height (by rfl)).scalarEval_zero
  have h1 : Kernel.scalarEval (R:=R) 1=evalOne.toRingHom :=
    (machine.table height (by rfl)).scalarEval_one
  have hv : Steinberg.map (Kernel.scalarEval 0) (gradedElement u)=
      Steinberg.map (algebraMap (ZMod 2) R) (groundElement u) := by
    rw [h0]
    exact gradedElement_zero u
  obtain ⟨q,hnq,m,hm,he⟩ := Kernel.polynomial_kernel_standard_torsion hn (gradedElement u)
    (gradedElement_matrix_one u hu) (groundElement u) hv
  refine ⟨q,hnq,m,hm,?_⟩
  rw [h1,gradedElement_one] at he
  exact he
end
end SourceBurnside.ConcreteSource

end

end OAI
