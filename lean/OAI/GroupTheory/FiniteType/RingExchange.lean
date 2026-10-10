import Mathlib
import OAI.GroupTheory.FiniteType.NonunitalCompression

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace RingExchange
variable {R : Type*} [Ring R]

structure Data (R : Type*) [Ring R] where
  E : R
  F : R
  a : R
  b : R
  EF : E*F=0
  FE : F*E=0
  aE : a*E=a
  Fa : F*a=a
  bF : b*F=b
  Eb : E*b=b
  ab : a*b=F
  ba : b*a=E

namespace Data
variable (D : Data R)
lemma Ea : D.E*D.a=0 := by rw [← D.Fa,← mul_assoc,D.EF,zero_mul]
lemma aF : D.a*D.F=0 := by rw [← D.aE,mul_assoc,D.EF,mul_zero]
lemma Fb : D.F*D.b=0 := by rw [← D.Eb,← mul_assoc,D.FE,zero_mul]
lemma bE : D.b*D.E=0 := by rw [← D.bF,mul_assoc,D.FE,mul_zero]
lemma aa : D.a*D.a=0 := by
  calc D.a*D.a=(D.a*D.E)*D.a := by rw [D.aE]
       _ = 0 := by rw [mul_assoc,D.Ea,mul_zero]
lemma bb : D.b*D.b=0 := by
  calc D.b*D.b=(D.b*D.F)*D.b := by rw [D.bF]
       _ = 0 := by rw [mul_assoc,D.Fb,mul_zero]
lemma EE : D.E*D.E=D.E := by
  calc D.E*D.E=(D.b*D.a)*D.E := by rw [D.ba]
       _ = D.E := by rw [mul_assoc,D.aE,D.ba]
lemma FF : D.F*D.F=D.F := by
  calc D.F*D.F=(D.a*D.b)*D.F := by rw [D.ab]
       _ = D.F := by rw [mul_assoc,D.bF,D.ab]

def value : R := 1-D.E-D.F+D.a+D.b

lemma square : D.value*D.value=1 := by
  simp only [value,add_mul,mul_add,sub_mul,mul_sub,one_mul,mul_one,
    D.EE,D.FF,D.EF,D.FE,D.Ea,D.aE,D.Fa,D.aF,D.Eb,D.bE,D.Fb,D.bF,D.aa,D.bb,D.ab,D.ba]
  abel

lemma value_E : D.value*D.E=D.a := by
  simp only [value,add_mul,sub_mul,one_mul,D.EE,D.FE,D.aE,D.bE]
  abel
lemma a_value : D.a*D.value=D.F := by
  simp only [value,mul_add,mul_sub,mul_one,D.aE,D.aF,D.aa,D.ab]
  abel

def unit : Rˣ := ⟨D.value,D.value,D.square,D.square⟩

lemma conjugates : D.unit.val*D.E*D.unit.inv=D.F := by
  change D.value*D.E*D.value=D.F
  rw [D.value_E,D.a_value]

lemma commutes {x : R} (hE : Commute D.E x) (hF : Commute D.F x)
    (ha : Commute D.a x) (hb : Commute D.b x) : Commute D.unit.val x :=
  (((Commute.one_left x).sub_left hE).sub_left hF).add_left ha |>.add_left hb
end Data

def ofPairs (p s d t e : R)
    (hpd : p*d=d) (hpe : p*e=e)
    (hds : d*s=p) (het : e*t=p) (hdt : d*t=0) (hes : e*s=0) : Data R where
  E := s*d
  F := t*e
  a := t*d
  b := s*e
  EF := by rw [mul_assoc,← mul_assoc d,hdt,zero_mul,mul_zero]
  FE := by rw [mul_assoc,← mul_assoc e,hes,zero_mul,mul_zero]
  aE := by rw [mul_assoc,← mul_assoc d,hds,hpd]
  Fa := by rw [mul_assoc,← mul_assoc e,het,hpd]
  bF := by rw [mul_assoc,← mul_assoc e,het,hpe]
  Eb := by rw [mul_assoc,← mul_assoc d,hds,hpe]
  ab := by rw [mul_assoc,← mul_assoc d,hds,hpe]
  ba := by rw [mul_assoc,← mul_assoc e,het,hpd]

end RingExchange

namespace Steinberg
variable {R : Type*} [Ring R]

def blockUpper (A : Matrix (Fin 2) (Fin 2) R) : Group (Fin 2 ⊕ Fin 2) R :=
  root (Sum.inl 0) (Sum.inr 0) (by simp) (A 0 0) *
  root (Sum.inl 0) (Sum.inr 1) (by simp) (A 0 1) *
  root (Sum.inl 1) (Sum.inr 0) (by simp) (A 1 0) *
  root (Sum.inl 1) (Sum.inr 1) (by simp) (A 1 1)

def blockLower (A : Matrix (Fin 2) (Fin 2) R) : Group (Fin 2 ⊕ Fin 2) R :=
  root (Sum.inr 0) (Sum.inl 0) (by simp) (A 0 0) *
  root (Sum.inr 0) (Sum.inl 1) (by simp) (A 0 1) *
  root (Sum.inr 1) (Sum.inl 0) (by simp) (A 1 0) *
  root (Sum.inr 1) (Sum.inl 1) (by simp) (A 1 1)

lemma matrix_blockUpper (A : Matrix (Fin 2) (Fin 2) R) :
    (matrix (blockUpper A)).val = Matrix.fromBlocks 1 A 0 1 := by
  ext x y
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockUpper, matrix_root, Matrix.mul_apply, Fintype.sum_sum_type,
          Fin.sum_univ_two, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]
    | inr y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockUpper, matrix_root, Matrix.mul_apply, Fintype.sum_sum_type,
          Fin.sum_univ_two, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]
  | inr x =>
    cases y with
    | inl y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockUpper, matrix_root, Matrix.mul_apply, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]
    | inr y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockUpper, matrix_root, Matrix.mul_apply, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]

lemma matrix_blockLower (A : Matrix (Fin 2) (Fin 2) R) :
    (matrix (blockLower A)).val = Matrix.fromBlocks 1 0 A 1 := by
  ext x y
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockLower, matrix_root, Matrix.mul_apply, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]
    | inr y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockLower, matrix_root, Matrix.mul_apply, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]
  | inr x =>
    cases y with
    | inl y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockLower, matrix_root, Matrix.mul_apply, Fintype.sum_sum_type,
          Fin.sum_univ_two, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]
    | inr y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockLower, matrix_root, Matrix.mul_apply, Fintype.sum_sum_type,
          Fin.sum_univ_two, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]

def blockBalanced (U : (Matrix (Fin 2) (Fin 2) R)ˣ) : Group (Fin 2 ⊕ Fin 2) R :=
  blockUpper U.val * blockLower (-U.inv) * blockUpper U.val *
    blockUpper (-1) * blockLower 1 * blockUpper (-1)

lemma matrix_blockBalanced (U : (Matrix (Fin 2) (Fin 2) R)ˣ) :
    (matrix (blockBalanced U)).val = Matrix.fromBlocks U.val 0 0 U.inv := by
  simp only [blockBalanced, map_mul, Units.val_mul, matrix_blockUpper, matrix_blockLower]
  simp [Matrix.fromBlocks_multiply]

end Steinberg

namespace RingExchange.Data
variable {R : Type*} [Ring R] (D : RingExchange.Data R)

def flipMatrix : Matrix (Fin 2) (Fin 2) R := !![1-D.F,D.a; D.b,1-D.E]

lemma flipMatrix_square : D.flipMatrix * D.flipMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flipMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    simp only [sub_mul, mul_sub, one_mul, mul_one, D.FF, D.EE, D.Fa, D.aE,
      D.bF, D.Eb, D.ab, D.ba]
    abel

def flipUnit : (Matrix (Fin 2) (Fin 2) R)ˣ :=
  ⟨D.flipMatrix,D.flipMatrix,D.flipMatrix_square,D.flipMatrix_square⟩

lemma flip_bad_row (η : R →ₙ+* R) (hE : ∀ x, D.E*η x=η x) (x : R) (j : Fin 2) :
    D.flipMatrix 1 j * η x=0 := by
  have hb : D.b*η x=0 := by rw [← hE x,← mul_assoc,D.bE,zero_mul]
  fin_cases j <;> simp [flipMatrix,sub_mul,hE,hb]

lemma flip_bad_col (η : R →ₙ+* R) (hE : ∀ x, η x*D.E=η x) (x : R) (j : Fin 2) :
    η x * D.flipMatrix j 1=0 := by
  have ha : η x*D.a=0 := by rw [← hE x,mul_assoc,D.Ea,mul_zero]
  fin_cases j <;> simp [flipMatrix,mul_sub,hE,ha]

end RingExchange.Data

namespace Steinberg
section
variable {R : Type*} [Ring R]

abbrev SixIndices := (Fin 2 ⊕ Fin 2) ⊕ Fin 2

def retainedIndices : Set SixIndices := fun i => match i with
  | Sum.inl (Sum.inl a) => a=0
  | Sum.inl (Sum.inr a) => a=0
  | Sum.inr _ => True

lemma flip_kernel_central (D : RingExchange.Data R) (η : R →ₙ+* R)
    (hleft : ∀ x, D.E*η x=η x) (hright : ∀ x, η x*D.E=η x)
    (w : Group SixIndices R) (hw : pi w=1) (v : Group SixIndices R) :
    Commute (map η w) v := by
  let z := blockBalanced D.flipUnit
  let f : (Fin 2 ⊕ Fin 2) ↪ SixIndices := Function.Embedding.inl
  have hz : (matrix z).val = Matrix.fromBlocks D.flipMatrix 0 0 D.flipMatrix :=
    matrix_blockBalanced D.flipUnit
  have hi : ((matrix z)⁻¹).val = Matrix.fromBlocks D.flipMatrix 0 0 D.flipMatrix := by
    have hs : (Matrix.fromBlocks D.flipMatrix 0 0 D.flipMatrix :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
        Matrix.fromBlocks D.flipMatrix 0 0 D.flipMatrix = 1 := by
      simp [Matrix.fromBlocks_multiply,D.flipMatrix_square,Matrix.fromBlocks_one]
    have he : (matrix z) * (matrix z) = 1 := Units.ext (by simpa only [Units.val_mul,Units.val_one,hz] using hs)
    exact (congrArg Units.val (inv_eq_of_mul_eq_one_left he)).trans hz
  apply localized_coefficient_kernel_central retainedIndices f z (Sum.inr 0)
    (by intro i; simp [f]) η ?_ ?_ ?_ (Sum.inl (Sum.inl 1)) (by change (1 : Fin 2) ≠ 0; decide) w hw v
  · intro k hk
    cases k with
    | inl a => exact False.elim (hk a rfl)
    | inr a => trivial
  · intro i hiA j a
    rw [hz]
    cases i with
    | inl i =>
      have hi0 : i ≠ 0 := hiA
      have hi1 : i=1 := by fin_cases i <;> simp_all
      subst i
      cases j with
      | inl j => exact D.flip_bad_row η hleft a j
      | inr j => simp
    | inr i =>
      have hi0 : i ≠ 0 := hiA
      have hi1 : i=1 := by fin_cases i <;> simp_all
      subst i
      cases j with
      | inl j => simp
      | inr j => exact D.flip_bad_row η hleft a j
  · intro i hiA j a
    rw [hi]
    cases i with
    | inl i =>
      have hi0 : i ≠ 0 := hiA
      have hi1 : i=1 := by fin_cases i <;> simp_all
      subst i
      cases j with
      | inl j => exact D.flip_bad_col η hright a j
      | inr j => simp
    | inr i =>
      have hi0 : i ≠ 0 := hiA
      have hi1 : i=1 := by fin_cases i <;> simp_all
      subst i
      cases j with
      | inl j => simp
      | inr j => exact D.flip_bad_col η hright a j

end

section
variable {R n m : Type*} [Ring R]

def diagonalAction (d : n → Rˣ) : Group n R →* Group n R :=
  lift (fun i j hij a => root i j hij ((d i).val*a*(d j).inv))
    (by intros; rw [root_add,mul_add,add_mul])
    (by
      intro i j k hij hjk hik a b
      rw [root_commutator i j k hij hjk hik]
      congr 1
      simp [mul_assoc])
    (by intros; apply root_commute <;> assumption)

@[simp] lemma diagonalAction_root (d : n → Rˣ) (i j : n) (hij : i≠j) (a : R) :
    diagonalAction d (root i j hij a)=root i j hij ((d i).val*a*(d j).inv) := lift_root _ _ _ _ _ _ _ _

lemma diagonalAction_mul (d e : n → Rˣ) :
    diagonalAction (d*e) = (diagonalAction d).comp (diagonalAction e) := by
  apply hom_ext
  intro i j hij a
  simp [mul_assoc]

lemma diagonalAction_one : diagonalAction (1 : n → Rˣ) = MonoidHom.id _ := by
  apply hom_ext
  intro i j hij a
  simp

variable [Fintype n] [DecidableEq n]

lemma conjugate_diagonal_column (f : n ↪ m) (z : Group n R) (d : n → Rˣ)
    (hz : matrix z=NoncommElementary.diagonal d) (k : m) (hk : ∀ i, f i ≠ k)
    (j : n) (a : R) :
    reindex f z * root (f j) k (hk j) a * (reindex f z)⁻¹ =
      root (f j) k (hk j) ((d j).val*a) := by
  have h := conjugate_column f k hk z (Pi.mulSingle j (Multiplicative.ofAdd a))
  have he : matrixVector (matrix z).val (Pi.mulSingle j (Multiplicative.ofAdd a)) =
      Pi.mulSingle j (Multiplicative.ofAdd ((d j).val*a)) := by
    funext i
    apply Multiplicative.toAdd.injective
    rw [matrixVector_single_apply,hz]
    change Matrix.diagonal (fun i => (d i).val) i j*a = _
    by_cases hi : i=j
    · subst i; simp
    · simp [hi]
  rw [he,column_single,column_single] at h
  exact h

lemma conjugate_diagonal_row (f : n ↪ m) (z : Group n R) (d : n → Rˣ)
    (hz : matrix z=NoncommElementary.diagonal d) (k : m) (hk : ∀ i, f i ≠ k)
    (j : n) (a : R) :
    reindex f z * root k (f j) (Ne.symm (hk j)) a * (reindex f z)⁻¹ =
      root k (f j) (Ne.symm (hk j)) (a*(d j).inv) := by
  have h := conjugate_row f k hk z (Pi.mulSingle j (Multiplicative.ofAdd a))
  have he : vectorMatrix ((matrix z)⁻¹).val (Pi.mulSingle j (Multiplicative.ofAdd a)) =
      Pi.mulSingle j (Multiplicative.ofAdd (a*(d j).inv)) := by
    funext i
    apply Multiplicative.toAdd.injective
    rw [vectorMatrix_single_apply,hz,← map_inv]
    change a*Matrix.diagonal (fun i => (d i).inv) j i = _
    by_cases hi : i=j
    · subst i; simp
    · simp [hi,Ne.symm hi]
  rw [he,row_single,row_single] at h
  exact h

lemma conjugate_block_diagonal (f : n ↪ m) (z : Group n R) (d : m → Rˣ)
    (hz : matrix z=NoncommElementary.diagonal (fun i => d (f i)))
    (k : m) (hk : ∀ i, f i≠k) (hd : ∀ j, (∀ i, f i≠j) → d j=1) :
    (MulAut.conj (reindex f z)).toMonoidHom = diagonalAction d := by
  apply hom_ext
  intro i j hij a
  simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,MulAut.conj_apply,
    diagonalAction_root]
  by_cases hi : ∃ p, f p=i
  · obtain ⟨p,rfl⟩ := hi
    by_cases hj : ∃ q, f q=j
    · obtain ⟨q,rfl⟩ := hj
      have he : root (f p) (f q) hij a =
          ⁅root (f p) k (hk p) a,root k (f q) (Ne.symm (hk q)) 1⁆ := by
        rw [root_commutator _ _ _ (hk p) (Ne.symm (hk q)) hij,mul_one]
      rw [he]
      have hconj := map_commutatorElement (MulAut.conj (reindex f z)).toMonoidHom
        (root (f p) k (hk p) a) (root k (f q) (Ne.symm (hk q)) 1)
      change reindex f z * _ * (reindex f z)⁻¹ = _ at hconj
      rw [hconj]
      change ⁅reindex f z * root (f p) k (hk p) a * (reindex f z)⁻¹,
        reindex f z * root k (f q) (Ne.symm (hk q)) 1 * (reindex f z)⁻¹⁆ = _
      rw [conjugate_diagonal_column f z _ hz k hk p a,
        conjugate_diagonal_row f z _ hz k hk q 1,
        root_commutator (f p) k (f q) (hk p) (Ne.symm (hk q)) hij,one_mul]
    · have hj' : ∀ q, f q≠j := by simpa only [not_exists] using hj
      simpa [hd j hj'] using conjugate_diagonal_column f z _ hz j hj' p a
  · have hi' : ∀ p, f p≠i := by simpa only [not_exists] using hi
    by_cases hj : ∃ q, f q=j
    · obtain ⟨q,rfl⟩ := hj
      rw [hd i hi',Units.val_one,one_mul]
      exact conjugate_diagonal_row f z _ hz i hi' q a
    · have hj' : ∀ q, f q≠j := by simpa only [not_exists] using hj
      simp [(reindex_commute_disjoint f i j hij hi' hj' z a).mul_inv_cancel,
        hd i hi',hd j hj']

end

section
variable {R : Type*} [Ring R]

def transportWord (d s : R) : Group (Fin 2) R :=
  (root 0 1 (by decide) 1 * root 1 0 (by decide) (-1) * root 0 1 (by decide) 1)⁻¹ *
    (root 0 1 (by decide) d * root 1 0 (by decide) (-s) * root 0 1 (by decide) d)

lemma matrix_transportWord (d s : R) (hdsd : d*s*d=d) :
    (matrix (transportWord d s)).val = !![s, s*d-1; 1-d*s, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transportWord, map_mul, map_inv, matrix_root, mul_inv_rev,
      NoncommElementary.root_inv, NoncommElementary.root_val, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.single, Matrix.one_apply] <;>
    noncomm_ring [hdsd]

lemma matrix_transportWord_inv (d s : R) (hdsd : d*s*d=d) :
    ((matrix (transportWord d s))⁻¹).val = !![d, 1-d*s; s*d-1, s] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transportWord, map_mul, map_inv, matrix_root, mul_inv_rev,
      NoncommElementary.root_inv, NoncommElementary.root_val, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.single, Matrix.one_apply] <;>
    noncomm_ring [hdsd]
  all_goals simp_all [← mul_assoc]

end

variable {R m : Type*} [Ring R]

lemma constantPair_inner (u : Rˣ) (hu : u.inv=u.val) (f : Fin 2 ↪ m)
    (d : m → Rˣ) (hd : ∀ i, d (f i)=u) (t : m) (ht : ∀ i, f i≠t)
    (hout : ∀ j, (∀ i, f i≠j) → d j=1) :
    ∃ z : Group m R, (MulAut.conj z).toMonoidHom=diagonalAction d := by
  let z := transportWord u.inv u.val
  refine ⟨reindex f z,conjugate_block_diagonal f z d ?_ t ht hout⟩
  apply Units.ext
  change (matrix (transportWord u.inv u.val)).val = _
  rw [matrix_transportWord u.inv u.val (by simp)]
  have hu' : (u⁻¹).val=u.val := hu
  have hu2 : u.val*u.val=1 := (congrArg (fun x => u.val*x) hu).symm.trans u.val_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NoncommElementary.diagonal,hd,hu',hu2]

lemma innerWeights_mul (d e : m → Rˣ)
    (hd : ∃ z : Group m R, (MulAut.conj z).toMonoidHom=diagonalAction d)
    (he : ∃ z : Group m R, (MulAut.conj z).toMonoidHom=diagonalAction e) :
    ∃ z : Group m R, (MulAut.conj z).toMonoidHom=diagonalAction (d*e) := by
  obtain ⟨x,hx⟩ := hd
  obtain ⟨y,hy⟩ := he
  refine ⟨x*y,?_⟩
  rw [diagonalAction_mul,← hx,← hy]
  ext v
  simp [MulAut.conj_apply,mul_assoc]

def scalarWeight₀ (u : Rˣ) : SixIndices → Rˣ
  | Sum.inl (Sum.inl _) => u
  | _ => 1

def scalarWeight₁ (u : Rˣ) : SixIndices → Rˣ
  | Sum.inl (Sum.inr _) => u
  | _ => 1

def scalarWeight₂ (u : Rˣ) : SixIndices → Rˣ
  | Sum.inr _ => u
  | _ => 1

lemma scalarWeight_product (u : Rˣ) :
    scalarWeight₀ u * scalarWeight₁ u * scalarWeight₂ u = fun _ => u := by
  funext i
  rcases i with (i|i)|i <;> simp [scalarWeight₀,scalarWeight₁,scalarWeight₂]

lemma scalar_involution_inner (u : Rˣ) (hu : u.inv=u.val) :
    ∃ z : Group SixIndices R,
      (MulAut.conj z).toMonoidHom=diagonalAction (fun _ => u) := by
  have h₀ : ∃ z : Group SixIndices R,
      (MulAut.conj z).toMonoidHom=diagonalAction (scalarWeight₀ u) := by
    let f : Fin 2 ↪ SixIndices := Function.Embedding.inl.trans Function.Embedding.inl
    apply constantPair_inner u hu f (scalarWeight₀ u) (by intro i; rfl)
      (Sum.inr 0) (by intro i; simp [f])
    intro j hj
    rcases j with (j|j)|j
    · exact False.elim (hj j rfl)
    · rfl
    · rfl
  have h₁ : ∃ z : Group SixIndices R,
      (MulAut.conj z).toMonoidHom=diagonalAction (scalarWeight₁ u) := by
    let f : Fin 2 ↪ SixIndices := Function.Embedding.inr.trans Function.Embedding.inl
    apply constantPair_inner u hu f (scalarWeight₁ u) (by intro i; rfl)
      (Sum.inr 0) (by intro i; simp [f])
    intro j hj
    rcases j with (j|j)|j
    · rfl
    · exact False.elim (hj j rfl)
    · rfl
  have h₂ : ∃ z : Group SixIndices R,
      (MulAut.conj z).toMonoidHom=diagonalAction (scalarWeight₂ u) := by
    let f : Fin 2 ↪ SixIndices := Function.Embedding.inr
    apply constantPair_inner u hu f (scalarWeight₂ u) (by intro i; rfl)
      (Sum.inl (Sum.inl 0)) (by intro i; simp [f])
    intro j hj
    cases j with
    | inl j => rfl
    | inr j => exact False.elim (hj j rfl)
  have h := innerWeights_mul _ _ (innerWeights_mul _ _ h₀ h₁) h₂
  rwa [scalarWeight_product] at h

lemma central_conjugated_coefficients (u : Rˣ) (hu : u.inv=u.val)
    (η θ : R →ₙ+* R) (hη : ∀ a, θ a=u.val*η a*u.inv)
    (w : Group SixIndices R) (hc : ∀ v : Group SixIndices R, Commute (map η w) v) :
    map θ w=map η w := by
  obtain ⟨z,hz⟩ := scalar_involution_inner u hu
  have he : map θ = (diagonalAction (fun _ : SixIndices => u)).comp (map η) := by
    apply hom_ext
    intro i j hij a
    simp [hη]
  rw [he,← hz]
  change z * map η w * z⁻¹=map η w
  exact (hc z).symm.mul_inv_cancel

end Steinberg

end

end OAI
