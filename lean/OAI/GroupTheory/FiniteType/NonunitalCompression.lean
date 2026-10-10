import Mathlib
import OAI.GroupTheory.FiniteType.Steinberg

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace NonunitalCompression
variable {R S : Type*} [Ring R] [Ring S]
variable (φ : R →ₙ+* S)

def unitValue (x : R) : S := 1+φ (x-1)

@[simp] lemma unitValue_one : unitValue φ 1=1 := by simp [unitValue]

lemma unitValue_mul (x y : R) : unitValue φ (x*y)=unitValue φ x*unitValue φ y := by
  have hp : φ 1*φ 1=φ 1 := by rw [← map_mul,one_mul]
  have hl : φ 1*φ y=φ y := by rw [← map_mul,one_mul]
  have hr : φ x*φ 1=φ x := by rw [← map_mul,mul_one]
  simp only [unitValue,map_sub,map_mul]
  noncomm_ring [hp,hl,hr]

def units : Rˣ →* Sˣ where
  toFun u := {
    val := unitValue φ u.val
    inv := unitValue φ u.inv
    val_inv := by rw [← unitValue_mul,u.val_inv,unitValue_one]
    inv_val := by rw [← unitValue_mul,u.inv_val,unitValue_one] }
  map_one' := Units.ext (unitValue_one φ)
  map_mul' u v := Units.ext (unitValue_mul φ u.val v.val)

@[simp] lemma units_val (u : Rˣ) : (units φ u).val=1+φ (u.val-1) := rfl

end NonunitalCompression

namespace Steinberg
section
variable {n R S : Type*} [Ring R] [Ring S] [Fintype n] [DecidableEq n]

def matrixCoefficient (φ : R →ₙ+* S) : Matrix n n R →ₙ+* Matrix n n S where
  toFun A := A.map φ
  map_zero' := by ext; simp
  map_add' A B := by ext; simp
  map_mul' A B := Matrix.map_mul

omit [DecidableEq n] in
@[simp] lemma matrixCoefficient_apply (φ : R →ₙ+* S) (A : Matrix n n R) (i j : n) :
    matrixCoefficient φ A i j = φ (A i j) := rfl

lemma matrix_map (φ : R →ₙ+* S) (z : Group n R) :
    matrix (map φ z) = NonunitalCompression.units (matrixCoefficient φ) (matrix z) := by
  have he : (matrix (n:=n) (R:=S)).comp (map φ) =
      (NonunitalCompression.units (matrixCoefficient φ)).comp matrix := by
    apply hom_ext
    intro i j hij a
    simp only [MonoidHom.comp_apply, map_root, matrix_root]
    apply Units.ext
    simp only [NoncommElementary.root_val, NonunitalCompression.units_val,
      add_sub_cancel_left]
    change 1 + Matrix.single i j (φ a) = 1 + (Matrix.single i j a).map φ
    rw [Matrix.map_single _ _ _ φ]
  exact DFunLike.congr_fun he z

lemma matrix_map_val (φ : R →ₙ+* S) (z : Group n R) :
    (matrix (map φ z)).val = 1 + ((matrix z).val - 1).map φ := by
  rw [matrix_map]
  rfl

lemma map_preserves_kernel (φ : R →ₙ+* S) (z : Group n R) (hz : pi z = 1) :
    pi (map φ z) = 1 := by
  apply Subtype.ext
  change matrix (map φ z) = 1
  rw [matrix_map]
  have hm : matrix z = 1 := congrArg Subtype.val hz
  rw [hm, map_one]

end

variable {n m R : Type*} [Ring R] [Fintype n] [DecidableEq n]

def columnRoot (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k) (i : n) (a : R) :
    Group m R := root (f i) k (hk i) a

omit [Fintype n] [DecidableEq n] in
lemma columnRoot_commute (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (i j : n) (a b : R) : Commute (columnRoot f k hk i a) (columnRoot f k hk j b) :=
  root_commute _ _ _ _ _ _ (hk i) (Ne.symm (hk j)) a b

def column (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k) :
    (n → Multiplicative R) →* Group m R where
  toFun v := Finset.univ.noncommProd (fun i => columnRoot f k hk i (v i).toAdd)
    (by intro i _ j _ _; exact columnRoot_commute f k hk i j _ _)
  map_one' := by
    apply (Finset.noncommProd_eq_pow_card _ _ _ 1 ?_).trans (one_pow _)
    intro i _
    exact root_zero _ _ _
  map_mul' v w := by
    let c (u : n → Multiplicative R) := fun i => columnRoot f k hk i (u i).toAdd
    have he : c (v*w) = c v * c w := by
      ext i
      exact (root_add _ _ _ _ _).symm
    change Finset.univ.noncommProd (c (v*w)) _ = _
    simp only [he]
    exact Finset.noncommProd_mul_distrib _ _ _ _
      (by intro i _ j _ _; exact columnRoot_commute f k hk i j _ _)

lemma column_single (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k) (i : n) (a : R) :
    column f k hk (Pi.mulSingle i (Multiplicative.ofAdd a)) = columnRoot f k hk i a := by
  let c : n → Group m R := fun j =>
    columnRoot f k hk j ((Pi.mulSingle i (Multiplicative.ofAdd a) : n → Multiplicative R) j).toAdd
  have hc : ((Finset.univ : Finset n) : Set n).Pairwise (fun a b => Commute (c a) (c b)) := by
    intro j _ l _ _
    exact columnRoot_commute f k hk j l _ _
  change Finset.univ.noncommProd c hc = _
  have he : (Finset.univ.erase i).noncommProd c
      (hc.mono (by intro j hj; exact Finset.mem_univ _)) = 1 := by
    apply (Finset.noncommProd_eq_pow_card _ _ _ 1 ?_).trans (one_pow _)
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [c, Pi.mulSingle_eq_of_ne hji, toAdd_one, columnRoot, root_zero]
  exact (Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i) c hc).symm.trans
    (by rw [he, mul_one]; simp [c])

omit [Fintype n] [DecidableEq n] in
lemma root_conjugate_columnRoot (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (i j : n) (hij : i ≠ j) (a b : R) :
    root (f i) (f j) (f.injective.ne hij) a * columnRoot f k hk j b *
      (root (f i) (f j) (f.injective.ne hij) a)⁻¹ =
        columnRoot f k hk i (a*b) * columnRoot f k hk j b := by
  have h := root_commutator (f i) (f j) k (f.injective.ne hij) (hk j) (hk i) a b
  have := congrArg (fun z => z * root (f j) k (hk j) b) h
  simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one, columnRoot]
    using this

def matrixVector (A : Matrix n n R) : (n → Multiplicative R) →* (n → Multiplicative R) where
  toFun v i := Multiplicative.ofAdd (A.mulVec (fun j => (v j).toAdd) i)
  map_one' := by
    ext i
    exact congrFun (Matrix.mulVec_zero A) i
  map_mul' v w := by
    ext i
    exact congrFun (Matrix.mulVec_add A (fun j => (v j).toAdd) (fun j => (w j).toAdd)) i

omit [DecidableEq n] in
@[simp] lemma matrixVector_apply (A : Matrix n n R) (v : n → Multiplicative R) (i : n) :
    (matrixVector A v i).toAdd = A.mulVec (fun j => (v j).toAdd) i := rfl

@[simp] lemma matrixVector_one (v : n → Multiplicative R) : matrixVector (1 : Matrix n n R) v = v := by
  ext i
  simp [matrixVector]

omit [DecidableEq n] in
lemma matrixVector_mul (A B : Matrix n n R) (v : n → Multiplicative R) :
    matrixVector (A*B) v = matrixVector A (matrixVector B v) := by
  ext i
  simp only [matrixVector_apply, ← Matrix.mulVec_mulVec]

lemma matrixVector_root_single (i j : n) (hij : i ≠ j) (a : R) (t : n) (b : R) :
    matrixVector (NoncommElementary.root i j hij a).val
        (Pi.mulSingle t (Multiplicative.ofAdd b)) =
      Pi.mulSingle i (Multiplicative.ofAdd (if t=j then a*b else 0)) *
        Pi.mulSingle t (Multiplicative.ofAdd b) := by
  ext q
  change ((1 + Matrix.single i j a).mulVec (Pi.single t b)) q =
    ((Pi.single i (if t=j then a*b else 0) : n → R) + (Pi.single t b : n → R)) q
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  simp [Function.update_apply, Pi.single_apply, eq_comm, add_comm]

lemma root_conjugate_column (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (i j : n) (hij : i ≠ j) (a : R) (v : n → Multiplicative R) :
    root (f i) (f j) (f.injective.ne hij) a * column f k hk v *
      (root (f i) (f j) (f.injective.ne hij) a)⁻¹ =
        column f k hk (matrixVector (NoncommElementary.root i j hij a).val v) := by
  let x := root (f i) (f j) (f.injective.ne hij) a
  have he : (MulAut.conj x).toMonoidHom.comp (column f k hk) =
      (column f k hk).comp (matrixVector (NoncommElementary.root i j hij a).val) := by
    apply MonoidHom.pi_ext
    intro t b
    obtain ⟨b, rfl⟩ := Multiplicative.ofAdd.surjective b
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, column_single, matrixVector_root_single, map_mul]
    by_cases ht : t = j
    · subst t
      simp only [ite_true]
      exact root_conjugate_columnRoot f k hk i j hij a b
    · simp only [ht, ite_false, columnRoot, root_zero, one_mul]
      change x * root (f t) k (hk t) b * x⁻¹ = _
      rw [(root_commute (f i) (f j) (f t) k (f.injective.ne hij) (hk t)
        (hk i) (f.injective.ne (Ne.symm ht)) a b).eq, mul_inv_cancel_right]
  exact DFunLike.congr_fun he v

lemma conjugate_column (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (z : Group n R) (v : n → Multiplicative R) :
    reindex f z * column f k hk v * (reindex f z)⁻¹ =
      column f k hk (matrixVector (matrix z).val v) := by
  let H : Subgroup (Group n R) := {
    carrier := {z | ∀ v : n → Multiplicative R,
      reindex f z * column f k hk v * (reindex f z)⁻¹ =
        column f k hk (matrixVector (matrix z).val v)}
    one_mem' := by intro v; simp
    mul_mem' := by
      intro a b ha hb v
      simp only [map_mul, Units.val_mul]
      calc
        (reindex f a * reindex f b) * column f k hk v *
            (reindex f a * reindex f b)⁻¹ =
            reindex f a * (reindex f b * column f k hk v * (reindex f b)⁻¹) *
                (reindex f a)⁻¹ := by group
        _ = column f k hk (matrixVector (matrix a).val
              (matrixVector (matrix b).val v)) := by rw [hb, ha]
        _ = _ := by rw [matrixVector_mul]
    inv_mem' := by
      intro a ha v
      have h := ha (matrixVector (matrix a⁻¹).val v)
      have hv : matrixVector (matrix a).val (matrixVector (matrix a⁻¹).val v) = v := by
        rw [← matrixVector_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel]
        simp
      rw [hv] at h
      simp only [map_inv] at h ⊢
      rw [← h]
      group }
  have hz : z ∈ H := by
    apply PresentedGroup.generated_by
    intro r v
    change reindex f (root r.i r.j r.different r.coefficient) * _ *
      (reindex f (root r.i r.j r.different r.coefficient))⁻¹ =
        column f k hk (matrixVector (matrix (root r.i r.j r.different r.coefficient)).val v)
    simpa only [reindex_root, matrix_root] using
      root_conjugate_column f k hk r.i r.j r.different r.coefficient v
  exact hz v

lemma kernel_commute_column (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (z : Group n R) (hz : pi z = 1) (v : n → Multiplicative R) :
    Commute (reindex f z) (column f k hk v) := by
  have hm : matrix z = 1 := congrArg Subtype.val hz
  have h := conjugate_column f k hk z v
  rw [hm] at h
  simp only [Units.val_one, matrixVector_one] at h
  change reindex f z * column f k hk v = column f k hk v * reindex f z
  calc
    _ = (reindex f z * column f k hk v * (reindex f z)⁻¹) * reindex f z := by group
    _ = _ := by rw [h]

lemma kernel_commute_outside_root (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (z : Group n R) (hz : pi z = 1) (i : n) (a : R) :
    Commute (reindex f z) (root (f i) k (hk i) a) := by
  have h := kernel_commute_column f k hk z hz (Pi.mulSingle i (Multiplicative.ofAdd a))
  rwa [column_single] at h

def rowRoot (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k) (i : n) (a : R) :
    Group m R := root k (f i) (Ne.symm (hk i)) a

omit [Fintype n] [DecidableEq n] in
lemma rowRoot_commute (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (i j : n) (a b : R) : Commute (rowRoot f k hk i a) (rowRoot f k hk j b) :=
  root_commute _ _ _ _ _ _ (Ne.symm (hk j)) (hk i) a b

def row (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k) :
    (n → Multiplicative R) →* Group m R where
  toFun v := Finset.univ.noncommProd (fun i => rowRoot f k hk i (v i).toAdd)
    (by intro i _ j _ _; exact rowRoot_commute f k hk i j _ _)
  map_one' := by
    apply (Finset.noncommProd_eq_pow_card _ _ _ 1 ?_).trans (one_pow _)
    intro i _
    exact root_zero _ _ _
  map_mul' v w := by
    let c (u : n → Multiplicative R) := fun i => rowRoot f k hk i (u i).toAdd
    have he : c (v*w) = c v * c w := by
      ext i
      exact (root_add _ _ _ _ _).symm
    change Finset.univ.noncommProd (c (v*w)) _ = _
    simp only [he]
    exact Finset.noncommProd_mul_distrib _ _ _ _
      (by intro i _ j _ _; exact rowRoot_commute f k hk i j _ _)

lemma row_single (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k) (i : n) (a : R) :
    row f k hk (Pi.mulSingle i (Multiplicative.ofAdd a)) = rowRoot f k hk i a := by
  let c : n → Group m R := fun j =>
    rowRoot f k hk j ((Pi.mulSingle i (Multiplicative.ofAdd a) : n → Multiplicative R) j).toAdd
  have hc : ((Finset.univ : Finset n) : Set n).Pairwise (fun a b => Commute (c a) (c b)) := by
    intro j _ l _ _
    exact rowRoot_commute f k hk j l _ _
  change Finset.univ.noncommProd c hc = _
  have he : (Finset.univ.erase i).noncommProd c
      (hc.mono (by intro j hj; exact Finset.mem_univ _)) = 1 := by
    apply (Finset.noncommProd_eq_pow_card _ _ _ 1 ?_).trans (one_pow _)
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [c, Pi.mulSingle_eq_of_ne hji, toAdd_one, rowRoot, root_zero]
  exact (Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i) c hc).symm.trans
    (by rw [he, mul_one]; simp [c])

omit [Fintype n] [DecidableEq n] in
lemma root_conjugate_rowRoot (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (i j : n) (hij : i ≠ j) (a b : R) :
    root (f i) (f j) (f.injective.ne hij) a * rowRoot f k hk i b *
      (root (f i) (f j) (f.injective.ne hij) a)⁻¹ =
        rowRoot f k hk j (-(b*a)) * rowRoot f k hk i b := by
  have h := root_commutator_reverse k (f i) (f j) (Ne.symm (hk i))
    (f.injective.ne hij) (Ne.symm (hk j)) b a
  have := congrArg (fun z => z * root k (f i) (Ne.symm (hk i)) b) h
  simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one, rowRoot]
    using this

def vectorMatrix (A : Matrix n n R) : (n → Multiplicative R) →* (n → Multiplicative R) where
  toFun v i := Multiplicative.ofAdd (Matrix.vecMul (fun j => (v j).toAdd) A i)
  map_one' := by
    ext i
    exact congrFun (Matrix.zero_vecMul A) i
  map_mul' v w := by
    ext i
    exact congrFun (Matrix.add_vecMul A (fun j => (v j).toAdd) (fun j => (w j).toAdd)) i

omit [DecidableEq n] in
@[simp] lemma vectorMatrix_apply (A : Matrix n n R) (v : n → Multiplicative R) (i : n) :
    (vectorMatrix A v i).toAdd = Matrix.vecMul (fun j => (v j).toAdd) A i := rfl

@[simp] lemma vectorMatrix_one (v : n → Multiplicative R) : vectorMatrix (1 : Matrix n n R) v = v := by
  ext i
  simp [vectorMatrix]

omit [DecidableEq n] in
lemma vectorMatrix_mul (A B : Matrix n n R) (v : n → Multiplicative R) :
    vectorMatrix (A*B) v = vectorMatrix B (vectorMatrix A v) := by
  ext i
  simp only [vectorMatrix_apply, ← Matrix.vecMul_vecMul]

lemma vectorMatrix_root_single (i j : n) (hij : i ≠ j) (a : R) (t : n) (b : R) :
    vectorMatrix ((NoncommElementary.root i j hij a)⁻¹).val
        (Pi.mulSingle t (Multiplicative.ofAdd b)) =
      Pi.mulSingle j (Multiplicative.ofAdd (if t=i then -(b*a) else 0)) *
        Pi.mulSingle t (Multiplicative.ofAdd b) := by
  ext q
  change (Matrix.vecMul (Pi.single t b) (1 + Matrix.single i j (-a))) q =
    ((Pi.single j (if t=i then -(b*a) else 0) : n → R) + (Pi.single t b : n → R)) q
  rw [Matrix.vecMul_add, Matrix.vecMul_one]
  simp [Matrix.single, Pi.single_apply, eq_comm, add_comm]
  split_ifs <;> simp_all

lemma root_conjugate_row (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (i j : n) (hij : i ≠ j) (a : R) (v : n → Multiplicative R) :
    root (f i) (f j) (f.injective.ne hij) a * row f k hk v *
      (root (f i) (f j) (f.injective.ne hij) a)⁻¹ =
        row f k hk (vectorMatrix ((NoncommElementary.root i j hij a)⁻¹).val v) := by
  let x := root (f i) (f j) (f.injective.ne hij) a
  have he : (MulAut.conj x).toMonoidHom.comp (row f k hk) =
      (row f k hk).comp (vectorMatrix ((NoncommElementary.root i j hij a)⁻¹).val) := by
    apply MonoidHom.pi_ext
    intro t b
    obtain ⟨b, rfl⟩ := Multiplicative.ofAdd.surjective b
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, row_single, vectorMatrix_root_single, map_mul]
    by_cases ht : t = i
    · subst t
      simp only [ite_true]
      exact root_conjugate_rowRoot f k hk i j hij a b
    · simp only [ht, ite_false, rowRoot, root_zero, one_mul]
      change x * root k (f t) (Ne.symm (hk t)) b * x⁻¹ = _
      rw [(root_commute (f i) (f j) k (f t) (f.injective.ne hij) (Ne.symm (hk t))
        (f.injective.ne (Ne.symm ht)) (hk j) a b).eq, mul_inv_cancel_right]
  exact DFunLike.congr_fun he v

lemma conjugate_row (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (z : Group n R) (v : n → Multiplicative R) :
    reindex f z * row f k hk v * (reindex f z)⁻¹ =
      row f k hk (vectorMatrix ((matrix z)⁻¹).val v) := by
  let H : Subgroup (Group n R) := {
    carrier := {z | ∀ v : n → Multiplicative R,
      reindex f z * row f k hk v * (reindex f z)⁻¹ =
        row f k hk (vectorMatrix ((matrix z)⁻¹).val v)}
    one_mem' := by intro v; simp
    mul_mem' := by
      intro a b ha hb v
      simp only [map_mul, mul_inv_rev, Units.val_mul]
      calc
        (reindex f a * reindex f b) * row f k hk v *
            ((reindex f b)⁻¹ * (reindex f a)⁻¹) =
            reindex f a * (reindex f b * row f k hk v * (reindex f b)⁻¹) *
                (reindex f a)⁻¹ := by group
        _ = row f k hk (vectorMatrix ((matrix a)⁻¹).val
              (vectorMatrix ((matrix b)⁻¹).val v)) := by rw [hb, ha]
        _ = _ := by rw [vectorMatrix_mul]
    inv_mem' := by
      intro a ha v
      have h := ha (vectorMatrix ((matrix a⁻¹)⁻¹).val v)
      have hv : vectorMatrix ((matrix a)⁻¹).val (vectorMatrix ((matrix a⁻¹)⁻¹).val v) = v := by
        rw [← vectorMatrix_mul, ← Units.val_mul]
        simp
      rw [hv] at h
      simp only [map_inv, inv_inv] at h ⊢
      rw [← h]
      group }
  have hz : z ∈ H := by
    apply PresentedGroup.generated_by
    intro r v
    change reindex f (root r.i r.j r.different r.coefficient) * _ *
      (reindex f (root r.i r.j r.different r.coefficient))⁻¹ =
        row f k hk (vectorMatrix ((matrix (root r.i r.j r.different r.coefficient))⁻¹).val v)
    simpa only [reindex_root, matrix_root] using
      root_conjugate_row f k hk r.i r.j r.different r.coefficient v
  exact hz v

lemma kernel_commute_row (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (z : Group n R) (hz : pi z = 1) (v : n → Multiplicative R) :
    Commute (reindex f z) (row f k hk v) := by
  have hm : matrix z = 1 := congrArg Subtype.val hz
  have h := conjugate_row f k hk z v
  rw [hm] at h
  simp only [inv_one, Units.val_one, vectorMatrix_one] at h
  change reindex f z * row f k hk v = row f k hk v * reindex f z
  calc
    _ = (reindex f z * row f k hk v * (reindex f z)⁻¹) * reindex f z := by group
    _ = _ := by rw [h]

lemma kernel_commute_outside_row_root (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (z : Group n R) (hz : pi z = 1) (i : n) (a : R) :
    Commute (reindex f z) (root k (f i) (Ne.symm (hk i)) a) := by
  have h := kernel_commute_row f k hk z hz (Pi.mulSingle i (Multiplicative.ofAdd a))
  rwa [row_single] at h

lemma reindex_kernel_central (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (z : Group n R) (hz : pi z = 1) (w : Group m R) :
    Commute (reindex f z) w := by
  classical
  suffices hs : ∀ i j hij a, Commute (root i j hij a) (reindex f z) from
    (commute_of_roots (MonoidHom.id (Group m R)) (reindex f z) hs w).symm
  intro i j hij a
  by_cases hi : ∃ p, f p = i
  · obtain ⟨p, rfl⟩ := hi
    by_cases hj : ∃ q, f q = j
    · obtain ⟨q, rfl⟩ := hj
      have hc := kernel_commute_outside_root f k hk z hz p a
      have hr := kernel_commute_outside_row_root f k hk z hz q (1:R)
      have h := ((hc.mul_right hr).mul_right hc.inv_right).mul_right hr.inv_right
      rw [← commutatorElement_def, root_commutator (f p) k (f q)
        (hk p) (Ne.symm (hk q)) hij, mul_one] at h
      exact h.symm
    · have hj' : ∀ p, f p ≠ j := by simpa only [not_exists] using hj
      exact (kernel_commute_outside_root f j hj' z hz p a).symm
  · have hi' : ∀ p, f p ≠ i := by simpa only [not_exists] using hi
    by_cases hj : ∃ q, f q = j
    · obtain ⟨q, rfl⟩ := hj
      exact (kernel_commute_outside_row_root f i hi' z hz q a).symm
    · have hj' : ∀ p, f p ≠ j := by simpa only [not_exists] using hj
      apply Commute.symm
      apply commute_of_roots (reindex f) (root i j hij a) _ z
      intro p q hpq b
      simp only [reindex_root]
      exact root_commute (f p) (f q) i j (f.injective.ne hpq) hij (hj' p) (hi' q) b a

def matrixBlock {p : Type*} [Fintype p] [DecidableEq p] :
    (Matrix n n R)ˣ →* (Matrix (n ⊕ p) (n ⊕ p) R)ˣ where
  toFun A := {
    val := Matrix.fromBlocks A.val 0 0 1
    inv := Matrix.fromBlocks A.inv 0 0 1
    val_inv := by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
    inv_val := by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one] }
  map_one' := Units.ext (by simp [Matrix.fromBlocks_one])
  map_mul' A B := by
    apply Units.ext
    change Matrix.fromBlocks (A * B).val 0 0 1 =
      Matrix.fromBlocks A.val 0 0 1 * Matrix.fromBlocks B.val 0 0 1
    rw [Matrix.fromBlocks_multiply]
    simp

lemma matrixBlock_root {p : Type*} [Fintype p] [DecidableEq p]
    (i j : n) (hij : i ≠ j) (a : R) :
    matrixBlock (p:=p) (NoncommElementary.root i j hij a) =
      NoncommElementary.root (Sum.inl i) (Sum.inl j) (Sum.inl_injective.ne hij) a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;>
    simp [matrixBlock, NoncommElementary.root_val, Matrix.single, Matrix.fromBlocks, Matrix.one_apply]

lemma matrix_reindex_inl {p : Type*} [Fintype p] [DecidableEq p] (z : Group n R) :
    matrix (reindex (Function.Embedding.inl : n ↪ n ⊕ p) z) = matrixBlock (matrix z) := by
  have he : (matrix (n:=n⊕p) (R:=R)).comp (reindex Function.Embedding.inl) =
      (matrixBlock (p:=p)).comp matrix := by
    apply hom_ext
    intro i j hij a
    simp only [MonoidHom.comp_apply, reindex_root, matrix_root, matrixBlock_root]
    rfl
  exact DFunLike.congr_fun he z

lemma pi_reindex_inl_one_iff {p : Type*} [Fintype p] [DecidableEq p] (z : Group n R) :
    pi (reindex (Function.Embedding.inl : n ↪ n ⊕ p) z) = 1 ↔ pi z = 1 := by
  constructor
  · intro hz
    apply Subtype.ext
    apply Units.ext
    ext i j
    have he := congrArg (fun g : NoncommElementary.elementary (R:=R) (n:=n⊕p) =>
      g.val.val (Sum.inl i) (Sum.inl j)) hz
    change (matrix (reindex Function.Embedding.inl z)).val (Sum.inl i) (Sum.inl j) = _ at he
    rw [matrix_reindex_inl] at he
    simpa [matrixBlock, Matrix.one_apply] using he
  · intro hz
    apply Subtype.ext
    change matrix (reindex Function.Embedding.inl z) = 1
    rw [matrix_reindex_inl]
    have hm : matrix z = 1 := congrArg Subtype.val hz
    rw [hm, map_one]

lemma block_kernel_central {p : Type*} [Fintype p] [DecidableEq p] [Nonempty p]
    (z : Group (n⊕p) R) (hmem : z ∈ (reindex (R:=R) (Function.Embedding.inl : n ↪ n⊕p)).range)
    (hz : pi z = 1) (w : Group (n⊕p) R) : Commute z w := by
  obtain ⟨v, rfl⟩ := hmem
  obtain ⟨t⟩ := ‹Nonempty p›
  exact reindex_kernel_central Function.Embedding.inl (Sum.inr t) (by simp) v
    ((pi_reindex_inl_one_iff v).mp hz) w

omit [Fintype n] [DecidableEq n] in
@[simp] lemma reindex_id (z : Group n R) :
    reindex (Function.Embedding.refl n) z = z := by
  have h : reindex (R:=R) (Function.Embedding.refl n) = MonoidHom.id (Group n R) := by
    apply hom_ext
    intros
    rfl
  exact DFunLike.congr_fun h z

omit [Fintype n] [DecidableEq n] in
lemma reindex_trans {p : Type*} (f : n ↪ m) (g : m ↪ p) (z : Group n R) :
    reindex (f.trans g) z = reindex g (reindex f z) := by
  have h : reindex (R:=R) (f.trans g) = (reindex g).comp (reindex f) := by
    apply hom_ext
    intros
    simp only [MonoidHom.comp_apply, reindex_root]
    rfl
  exact DFunLike.congr_fun h z

variable [Fintype m] [DecidableEq m]

def matrixRelabel (e : n ≃ m) : (Matrix n n R)ˣ →* (Matrix m m R)ˣ :=
  Units.map (Matrix.reindexRingEquiv R e).toMonoidHom

@[simp] lemma matrixRelabel_apply (e : n ≃ m) (A : (Matrix n n R)ˣ) (i j : m) :
    (matrixRelabel e A).val i j = A.val (e.symm i) (e.symm j) := rfl

lemma matrixRelabel_root (e : n ≃ m) (i j : n) (hij : i ≠ j) (a : R) :
    matrixRelabel e (NoncommElementary.root i j hij a) =
      NoncommElementary.root (e i) (e j) (e.injective.ne hij) a := by
  apply Units.ext
  ext x y
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨y, rfl⟩ := e.surjective y
  simp [matrixRelabel_apply, NoncommElementary.root_val, Matrix.single, Matrix.one_apply]

lemma matrix_reindex_equiv (e : n ≃ m) (z : Group n R) :
    matrix (reindex e.toEmbedding z) = matrixRelabel e (matrix z) := by
  have h : (matrix (n:=m) (R:=R)).comp (reindex e.toEmbedding) =
      (matrixRelabel e).comp matrix := by
    apply hom_ext
    intro i j hij a
    simp only [MonoidHom.comp_apply, reindex_root, matrix_root, matrixRelabel_root]
    rfl
  exact DFunLike.congr_fun h z

def embeddingCompletion (f : n ↪ m) : n ⊕ ((Set.range f)ᶜ : Set m) ≃ m := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range f))

omit [DecidableEq n] [Fintype m] in
@[simp] lemma embeddingCompletion_inl (f : n ↪ m) (i : n) :
    embeddingCompletion f (Sum.inl i) = f i := rfl

lemma matrix_reindex_entry (f : n ↪ m) (z : Group n R) (i j : n) :
    (matrix (reindex f z)).val (f i) (f j) = (matrix z).val i j := by
  classical
  let e := embeddingCompletion f
  have hf : f = (Function.Embedding.inl : n ↪ n ⊕ ((Set.range f)ᶜ : Set m)).trans e.toEmbedding := by
    ext x
    rfl
  rw [hf, reindex_trans, matrix_reindex_equiv, matrixRelabel_apply]
  change (matrix (reindex Function.Embedding.inl z)).val (e.symm (e (Sum.inl i)))
    (e.symm (e (Sum.inl j))) = _
  rw [e.symm_apply_apply, e.symm_apply_apply, matrix_reindex_inl]
  rfl

lemma kernel_of_reindex (f : n ↪ m) (z : Group n R) (hz : pi (reindex f z) = 1) :
    pi z = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h := congrArg (fun g : NoncommElementary.elementary (R:=R) (n:=m) =>
    g.val.val (f i) (f j)) hz
  change (matrix (reindex f z)).val (f i) (f j) = _ at h
  rw [matrix_reindex_entry] at h
  simpa [Matrix.one_apply, f.injective.eq_iff] using h

def supported (A : Set m) : Subgroup (Group m R) :=
  (reindex (R:=R) (Function.Embedding.subtype (fun x => x ∈ A))).range

omit [Fintype m] [DecidableEq m] in
lemma root_mem_supported (A : Set m) (i j : m) (hij : i ≠ j) (a : R)
    (hi : i ∈ A) (hj : j ∈ A) : root i j hij a ∈ supported A := by
  refine ⟨root (⟨i,hi⟩ : A) ⟨j,hj⟩ (by intro h; exact hij (congrArg Subtype.val h)) a, ?_⟩
  simp only [reindex_root]
  rfl

lemma supported_kernel_central (A : Set m) (k : m) (hk : k ∉ A)
    (z : Group m R) (hmem : z ∈ supported A) (hz : pi z = 1) (w : Group m R) :
    Commute z w := by
  classical
  obtain ⟨v, rfl⟩ := hmem
  exact reindex_kernel_central (Function.Embedding.subtype _) k
    (by intro i he; exact hk (he ▸ i.property)) v
    (kernel_of_reindex _ v hz) w

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
lemma column_mem_supported (A : Set m) (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (v : n → Multiplicative R) (hA : k ∈ A) (hv : ∀ i, f i ∉ A → (v i).toAdd = 0) :
    column f k hk v ∈ supported A := by
  refine (supported A).noncommProd_mem
    (by intro i _ j _ _; exact columnRoot_commute f k hk i j _ _) ?_
  intro i _
  by_cases hi : f i ∈ A
  · exact root_mem_supported A (f i) k (hk i) _ hi hA
  · change root (f i) k (hk i) ((v i).toAdd) ∈ _
    rw [hv i hi, root_zero]
    exact (supported A).one_mem

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
lemma row_mem_supported (A : Set m) (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (v : n → Multiplicative R) (hA : k ∈ A) (hv : ∀ i, f i ∉ A → (v i).toAdd = 0) :
    row f k hk v ∈ supported A := by
  refine (supported A).noncommProd_mem
    (by intro i _ j _ _; exact rowRoot_commute f k hk i j _ _) ?_
  intro i _
  by_cases hi : f i ∈ A
  · exact root_mem_supported A k (f i) (Ne.symm (hk i)) _ hA hi
  · change root k (f i) (Ne.symm (hk i)) ((v i).toAdd) ∈ _
    rw [hv i hi, root_zero]
    exact (supported A).one_mem

lemma matrixVector_single_apply (A : Matrix n n R) (j : n) (a : R) (i : n) :
    (matrixVector A (Pi.mulSingle j (Multiplicative.ofAdd a)) i).toAdd = A i j*a := by
  change (A.mulVec (Pi.single j a)) i = _
  simp

lemma vectorMatrix_single_apply (A : Matrix n n R) (j : n) (a : R) (i : n) :
    (vectorMatrix A (Pi.mulSingle j (Multiplicative.ofAdd a)) i).toAdd = a*A j i := by
  change (Matrix.vecMul (Pi.single j a) A) i = _
  simp

omit [Fintype m] [DecidableEq m] in
lemma conjugate_column_root_mem_supported (A : Set m) (f : n ↪ m) (z : Group n R)
    (k : m) (hk : ∀ i, f i ≠ k) (hA : k ∈ A) (j : n) (a : R)
    (hcol : ∀ i, f i ∉ A → (matrix z).val i j*a=0) :
    reindex f z * root (f j) k (hk j) a * (reindex f z)⁻¹ ∈ supported A := by
  have h := conjugate_column f k hk z (Pi.mulSingle j (Multiplicative.ofAdd a))
  rw [column_single] at h
  change reindex f z * root (f j) k (hk j) a * (reindex f z)⁻¹ = _ at h
  rw [h]
  apply column_mem_supported A f k hk _ hA
  intro i hi
  rw [matrixVector_single_apply]
  exact hcol i hi

omit [Fintype m] [DecidableEq m] in
lemma conjugate_row_root_mem_supported (A : Set m) (f : n ↪ m) (z : Group n R)
    (k : m) (hk : ∀ i, f i ≠ k) (hA : k ∈ A) (j : n) (a : R)
    (hrow : ∀ i, f i ∉ A → a*((matrix z)⁻¹).val j i=0) :
    reindex f z * root k (f j) (Ne.symm (hk j)) a * (reindex f z)⁻¹ ∈ supported A := by
  have h := conjugate_row f k hk z (Pi.mulSingle j (Multiplicative.ofAdd a))
  rw [row_single] at h
  change reindex f z * root k (f j) (Ne.symm (hk j)) a * (reindex f z)⁻¹ = _ at h
  rw [h]
  apply row_mem_supported A f k hk _ hA
  intro i hi
  rw [vectorMatrix_single_apply]
  exact hrow i hi

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
lemma reindex_commute_disjoint (f : n ↪ m) (i j : m) (hij : i ≠ j)
    (hi : ∀ p, f p ≠ i) (hj : ∀ p, f p ≠ j) (z : Group n R) (a : R) :
    Commute (reindex f z) (root i j hij a) := by
  apply commute_of_roots (reindex f) (root i j hij a) _ z
  intro p q hpq b
  simp only [reindex_root]
  exact root_commute _ _ _ _ _ _ (hj p) (hi q) b a

omit [Fintype m] in

lemma conjugate_coefficient_supported (A : Set m) (f : n ↪ m) (z : Group n R)
    (t : m) (ht : ∀ i, f i ≠ t) (η : R →ₙ+* R)
    (houtside : ∀ k, (∀ i, f i ≠ k) → k ∈ A)
    (hcol : ∀ i, f i ∉ A → ∀ j a, (matrix z).val i j * η a=0)
    (hrow : ∀ i, f i ∉ A → ∀ j a, η a * ((matrix z)⁻¹).val j i=0)
    (w : Group m R) :
    reindex f z * map η w * (reindex f z)⁻¹ ∈ supported A := by
  let C : Group m R →* Group m R := (MulAut.conj (reindex f z)).toMonoidHom
  have hroots : ∀ p q hpq a, C (root p q hpq (η a)) ∈ supported A := by
    intro p q hpq a
    by_cases hp : ∃ i, f i = p
    · obtain ⟨i, rfl⟩ := hp
      by_cases hq : ∃ j, f j = q
      · obtain ⟨j, rfl⟩ := hq
        have he : root (f i) (f j) hpq (η a) =
            ⁅root (f i) t (ht i) (η a), root t (f j) (Ne.symm (ht j)) (η 1)⁆ := by
          rw [root_commutator _ _ _ (ht i) (Ne.symm (ht j)) hpq, ← map_mul, mul_one]
        rw [he, map_commutatorElement]
        have h₁ : C (root (f i) t (ht i) (η a)) ∈ supported A :=
          conjugate_column_root_mem_supported A f z t ht (houtside t ht) i (η a)
            (fun k hk => hcol k hk i a)
        have h₂ : C (root t (f j) (Ne.symm (ht j)) (η 1)) ∈ supported A :=
          conjugate_row_root_mem_supported A f z t ht (houtside t ht) j (η 1)
            (fun k hk => hrow k hk j 1)
        exact (supported A).mul_mem
          ((supported A).mul_mem ((supported A).mul_mem h₁ h₂) ((supported A).inv_mem h₁))
          ((supported A).inv_mem h₂)
      · have hq' : ∀ j, f j ≠ q := by simpa only [not_exists] using hq
        exact conjugate_column_root_mem_supported A f z q hq' (houtside q hq') i (η a)
          (fun k hk => hcol k hk i a)
    · have hp' : ∀ i, f i ≠ p := by simpa only [not_exists] using hp
      by_cases hq : ∃ j, f j = q
      · obtain ⟨j, rfl⟩ := hq
        exact conjugate_row_root_mem_supported A f z p hp' (houtside p hp') j (η a)
          (fun k hk => hrow k hk j a)
      · have hq' : ∀ j, f j ≠ q := by simpa only [not_exists] using hq
        change reindex f z * root p q hpq (η a) * (reindex f z)⁻¹ ∈ _
        rw [(reindex_commute_disjoint f p q hpq hp' hq' z (η a)).mul_inv_cancel]
        exact root_mem_supported A p q hpq (η a) (houtside p hp') (houtside q hq')
  have hw : w ∈ (supported A).comap (C.comp (map η)) := by
    apply PresentedGroup.generated_by
    intro r
    change C (map η (root r.i r.j r.different r.coefficient)) ∈ supported A
    rw [map_root]
    exact hroots r.i r.j r.different r.coefficient
  exact hw

lemma localized_coefficient_kernel_central (A : Set m) (f : n ↪ m) (z : Group n R)
    (t : m) (ht : ∀ i, f i ≠ t) (η : R →ₙ+* R)
    (houtside : ∀ k, (∀ i, f i ≠ k) → k ∈ A)
    (hcol : ∀ i, f i ∉ A → ∀ j a, (matrix z).val i j * η a=0)
    (hrow : ∀ i, f i ∉ A → ∀ j a, η a * ((matrix z)⁻¹).val j i=0)
    (b : m) (hb : b ∉ A) (w : Group m R) (hw : pi w=1) (v : Group m R) :
    Commute (map η w) v := by
  let c := reindex f z * map η w * (reindex f z)⁻¹
  have hmem : c ∈ supported A :=
    conjugate_coefficient_supported A f z t ht η houtside hcol hrow w
  have hc : pi c=1 := by
    simp [c, map_preserves_kernel η w hw]
  have hcentral : ∀ v, Commute c v := supported_kernel_central A b hb c hmem hc
  have he : map η w = c := by
    calc
      map η w = (reindex f z)⁻¹ * c * ((reindex f z)⁻¹)⁻¹ := by dsimp [c]; group
      _ = c := (hcentral (reindex f z)).symm.inv_left.mul_inv_cancel
  rw [he]
  exact hcentral v

end Steinberg

end

end OAI
