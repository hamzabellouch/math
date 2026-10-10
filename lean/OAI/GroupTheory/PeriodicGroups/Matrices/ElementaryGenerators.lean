import Mathlib
import OAI.GroupTheory.PeriodicGroups.Steinberg.MatrixUnits

namespace OAI

section
namespace SourceBurnside.Stability.MatrixGenerators
noncomputable section
open Classical Matrix
variable {R : Type*} [Ring R]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def elementary (i j : ι) (hij : i ≠ j) (a : R) : (Matrix ι ι R)ˣ where
  val := 1 + Matrix.single i j a
  inv := 1 + Matrix.single i j (-a)
  val_inv := by simp [add_mul, mul_add, hij.symm, ← Matrix.single_neg, add_assoc]
  inv_val := by simp [add_mul, mul_add, hij.symm, ← Matrix.single_neg, add_assoc]

@[simp] lemma elementary_val (i j : ι) (hij : i ≠ j) (a : R) :
    (elementary i j hij a : Matrix ι ι R) = 1 + Matrix.single i j a := rfl

def diagonal (d : ι → Rˣ) : (Matrix ι ι R)ˣ where
  val := Matrix.diagonal (fun i => (d i).val)
  inv := Matrix.diagonal (fun i => (d i).inv)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp

@[simp] lemma diagonal_val (d : ι → Rˣ) :
    (diagonal d : Matrix ι ι R) = Matrix.diagonal (fun i => (d i).val) := rfl

@[simp] lemma diagonal_one : diagonal (fun _ : ι => (1 : Rˣ)) = 1 := by
  apply Units.ext
  simp

@[simp] lemma diagonal_mul (d e : ι → Rˣ) : diagonal (fun i => d i * e i) = diagonal d * diagonal e := by
  apply Units.ext
  simp

def singleDiagonal (i : ι) (u : Rˣ) : (Matrix ι ι R)ˣ :=
  diagonal (fun j => if j = i then u else 1)

def generated : Subgroup (Matrix ι ι R)ˣ :=
  Subgroup.closure ({g | ∃i j h a, g = elementary i j h a} ∪ {g | ∃i u, g = singleDiagonal i u})

lemma elementary_mem (i j : ι) (hij : i ≠ j) (a : R) : elementary i j hij a ∈ generated :=
  Subgroup.subset_closure (Or.inl ⟨i, j, hij, a, rfl⟩)

lemma singleDiagonal_mem (i : ι) (u : Rˣ) : singleDiagonal i u ∈ generated :=
  Subgroup.subset_closure (Or.inr ⟨i, u, rfl⟩)

lemma diagonal_mem (d : ι → Rˣ) : diagonal d ∈ generated := by
  have he (s : Finset ι) : diagonal (fun i => if i ∈ s then d i else 1) ∈ generated := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have hh : diagonal (fun j => if j ∈ insert i s then d j else 1) =
          singleDiagonal i (d i) * diagonal (fun j => if j ∈ s then d j else 1) := by
        rw [singleDiagonal, ← diagonal_mul]
        congr 1
        funext j
        by_cases he : j = i
        · subst j; simp [hi]
        · simp [he]
      rw [hh]
      exact (generated (ι := ι) (R := R)).mul_mem (singleDiagonal_mem i (d i)) ih
  simpa using he Finset.univ

def relabel (e : ι ≃ κ) : (Matrix ι ι R)ˣ →* (Matrix κ κ R)ˣ :=
  Units.map (Matrix.reindexRingEquiv R e).toMonoidHom

@[simp] lemma relabel_elementary (e : ι ≃ κ) (i j : ι) (hij : i ≠ j) (a : R) :
    relabel e (elementary i j hij a) = elementary (e i) (e j) (e.injective.ne hij) a := by
  apply Units.ext
  ext x y
  simp [relabel, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Equiv.eq_symm_apply]

@[simp] lemma relabel_diagonal (e : ι ≃ κ) (d : ι → Rˣ) :
    relabel e (diagonal d) = diagonal (d ∘ e.symm) := by
  apply Units.ext
  simp [relabel, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]

@[simp] lemma relabel_singleDiagonal (e : ι ≃ κ) (i : ι) (u : Rˣ) :
    relabel e (singleDiagonal i u) = singleDiagonal (e i) u := by
  rw [singleDiagonal, relabel_diagonal, singleDiagonal]
  congr 1
  funext j
  simp [Equiv.symm_apply_eq]

lemma relabel_mem (e : ι ≃ κ) {g : (Matrix ι ι R)ˣ} (hg : g ∈ generated) :
    relabel e g ∈ generated := by
  have hh : generated (ι := ι) (R := R) ≤ (generated (ι := κ) (R := R)).comap (relabel e) := by
    apply (Subgroup.closure_le _).mpr
    rintro x (⟨i, j, h, a, rfl⟩ | ⟨i, u, rfl⟩)
    · change relabel e (elementary i j h a) ∈ generated
      rw [relabel_elementary]
      exact elementary_mem _ _ _ _
    · change relabel e (singleDiagonal i u) ∈ generated
      rw [relabel_singleDiagonal]
      exact singleDiagonal_mem _ _
  exact hh hg

def blockInclusion : (Matrix ι ι R)ˣ →* (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ where
  toFun u :=
    { val := Matrix.fromBlocks u.val 0 0 1
      inv := Matrix.fromBlocks u.inv 0 0 1
      val_inv := by simp [Matrix.fromBlocks_multiply]
      inv_val := by simp [Matrix.fromBlocks_multiply] }
  map_one' := by apply Units.ext; simp
  map_mul' u v := by apply Units.ext; simp [Matrix.fromBlocks_multiply]

@[simp] lemma blockInclusion_val (u : (Matrix ι ι R)ˣ) :
    (blockInclusion (κ := κ) u : Matrix (ι ⊕ κ) (ι ⊕ κ) R) = Matrix.fromBlocks u.val 0 0 1 := rfl

@[simp] lemma blockInclusion_elementary (i j : ι) (hij : i ≠ j) (a : R) :
    blockInclusion (κ := κ) (elementary i j hij a) =
      elementary (Sum.inl i) (Sum.inl j) (Sum.inl_injective.ne hij) a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply]

@[simp] lemma blockInclusion_diagonal (d : ι → Rˣ) :
    blockInclusion (κ := κ) (diagonal d) = diagonal (Sum.elim d (fun _ => 1)) := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;> simp [Matrix.fromBlocks, Matrix.diagonal_apply, Matrix.one_apply]

lemma blockInclusion_mem {g : (Matrix ι ι R)ˣ} (hg : g ∈ generated) :
    blockInclusion (κ := κ) g ∈ generated := by
  have hh : generated (ι := ι) (R := R) ≤
      (generated (ι := ι ⊕ κ) (R := R)).comap blockInclusion := by
    apply (Subgroup.closure_le _).mpr
    rintro x (⟨i, j, h, a, rfl⟩ | ⟨i, u, rfl⟩)
    · change blockInclusion (κ := κ) (elementary i j h a) ∈ generated
      rw [blockInclusion_elementary]
      exact elementary_mem _ _ _ _
    · change blockInclusion (κ := κ) (singleDiagonal i u) ∈ generated
      rw [singleDiagonal, blockInclusion_diagonal]
      exact diagonal_mem _
  exact hh hg

def column (b : ι → R) : Matrix ι (Fin 1) R := Matrix.of (fun i _ => b i)
def row (c : ι → R) : Matrix (Fin 1) ι R := Matrix.of (fun _ j => c j)
def scalarOne (u : R) : Matrix (Fin 1) (Fin 1) R := Matrix.of (fun _ _ => u)

def upperStrip (b : ι → R) : (Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R)ˣ where
  val := Matrix.fromBlocks 1 (column b) 0 1
  inv := Matrix.fromBlocks 1 (-column b) 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

@[simp] lemma upperStrip_val (b : ι → R) :
    (upperStrip b : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R) =
      Matrix.fromBlocks 1 (column b) 0 1 := rfl

@[simp] lemma upperStrip_zero : upperStrip (fun _ : ι => (0 : R)) = 1 := by
  apply Units.ext
  exact Matrix.fromBlocks_one

lemma upperStrip_add (b c : ι → R) : upperStrip (b+c) = upperStrip b * upperStrip c := by
  apply Units.ext
  simp only [Units.val_mul, upperStrip_val, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  congr 1
  ext i j
  simp [column, Pi.add_apply, add_comm]

lemma upperStrip_single (i : ι) (a : R) :
    upperStrip (fun j => if j = i then a else 0) =
      elementary (Sum.inl i) (Sum.inr 0) (by simp) a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, eq_comm, column, Fin.eq_zero]

lemma upperStrip_mem (b : ι → R) : upperStrip b ∈ generated := by
  have hs (s : Finset ι) : upperStrip (fun i => if i ∈ s then b i else 0) ∈ generated := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have he : (fun j => if j ∈ insert i s then b j else 0) =
          (fun j => if j = i then b i else 0) + (fun j => if j ∈ s then b j else 0) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [hi]
        · simp [hj]
      rw [he, upperStrip_add, upperStrip_single]
      exact (generated (ι := ι ⊕ Fin 1) (R := R)).mul_mem (elementary_mem _ _ _ _) ih
  simpa using hs Finset.univ

def lowerStrip (c : ι → R) : (Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R)ˣ where
  val := Matrix.fromBlocks 1 0 (row c) 1
  inv := Matrix.fromBlocks 1 0 (-row c) 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

@[simp] lemma lowerStrip_val (c : ι → R) :
    (lowerStrip c : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R) =
      Matrix.fromBlocks 1 0 (row c) 1 := rfl

@[simp] lemma lowerStrip_zero : lowerStrip (fun _ : ι => (0 : R)) = 1 := by
  apply Units.ext
  exact Matrix.fromBlocks_one

lemma lowerStrip_add (b c : ι → R) : lowerStrip (b+c) = lowerStrip b * lowerStrip c := by
  apply Units.ext
  simp only [Units.val_mul, lowerStrip_val, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  congr 1

lemma lowerStrip_single (i : ι) (a : R) :
    lowerStrip (fun j => if j = i then a else 0) =
      elementary (Sum.inr 0) (Sum.inl i) (by simp) a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, eq_comm, row, Fin.eq_zero]

lemma lowerStrip_mem (b : ι → R) : lowerStrip b ∈ generated := by
  have hs (s : Finset ι) : lowerStrip (fun i => if i ∈ s then b i else 0) ∈ generated := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have he : (fun j => if j ∈ insert i s then b j else 0) =
          (fun j => if j = i then b i else 0) + (fun j => if j ∈ s then b j else 0) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [hi]
        · simp [hj]
      rw [he, lowerStrip_add, lowerStrip_single]
      exact (generated (ι := ι ⊕ Fin 1) (R := R)).mul_mem (elementary_mem _ _ _ _) ih
  simpa using hs Finset.univ

lemma block_diagonal_val (U : (Matrix ι ι R)ˣ) (u : Rˣ) :
    (blockInclusion (κ := Fin 1) U * singleDiagonal (Sum.inr 0) u :
      (Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R)ˣ).val =
    Matrix.fromBlocks U.val 0 0 (scalarOne u.val) := by
  have hd : (singleDiagonal (ι := ι ⊕ Fin 1) (Sum.inr 0) u).val =
      Matrix.fromBlocks 1 0 0 (scalarOne u.val) := by
    ext x y
    cases x <;> cases y <;>
      simp [singleDiagonal, Matrix.fromBlocks, Matrix.diagonal_apply, Matrix.one_apply, scalarOne, Fin.eq_zero]
  rw [Units.val_mul, blockInclusion_val, hd]
  simp [Matrix.fromBlocks_multiply]

lemma schur_factorization (A : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R)
    (u : Rˣ) (hu : A (Sum.inr 0) (Sum.inr 0) = u.val)
    (S : (Matrix ι ι R)ˣ)
    (hS : S.val = Matrix.of (fun i j => A (Sum.inl i) (Sum.inl j) -
      A (Sum.inl i) (Sum.inr 0) * u.inv * A (Sum.inr 0) (Sum.inl j))) :
    (upperStrip (fun i => A (Sum.inl i) (Sum.inr 0) * u.inv) *
      (blockInclusion (κ := Fin 1) S * singleDiagonal (Sum.inr 0) u) *
      lowerStrip (fun j => u.inv * A (Sum.inr 0) (Sum.inl j))).val = A := by
  rw [Units.val_mul, Units.val_mul, block_diagonal_val, upperStrip_val, lowerStrip_val]
  simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add]
  ext x y
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      simp [Matrix.fromBlocks, Matrix.mul_apply, hS, mul_assoc, column, row, scalarOne]
    | inr j =>
      fin_cases j
      simp [Matrix.fromBlocks, Matrix.mul_apply, mul_assoc, column, row, scalarOne]
  | inr i =>
    fin_cases i
    cases y with
    | inl j =>
      simp [Matrix.fromBlocks, Matrix.mul_apply, ← mul_assoc, column, row, scalarOne]
    | inr j =>
      fin_cases j
      exact hu.symm

end
end SourceBurnside.Stability.MatrixGenerators

end
section
namespace SourceBurnside.Stability.LinearAlgebra
noncomputable section
open Classical Matrix
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
include hI

lemma matrix_nil {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (hA : ∀ i j, ε (A i j) = 0) : IsNilpotent A := by
  let e := Fintype.equivFin ι
  let f := Matrix.reindexRingEquiv R e
  apply (IsNilpotent.map_iff f.injective).mp
  exact hI _ (f A) (fun i j => hA (e.symm i) (e.symm j))

lemma nil_of_reduce_zero {a : R} (ha : ε a = 0) : IsNilpotent a := by
  let f : R →+* Matrix (Fin 1) (Fin 1) R := Matrix.scalar (Fin 1)
  have hf : Function.Injective f := by
    intro x y he
    simpa [f] using congrArg (fun M : Matrix (Fin 1) (Fin 1) R => M 0 0) he
  apply (IsNilpotent.map_iff hf).mp
  exact hI 1 _ (fun i j => by fin_cases i; fin_cases j; simpa [f] using ha)

lemma isUnit_of_reduce_one {a : R} (ha : ε a = 1) : IsUnit a := by
  have hn := nil_of_reduce_zero ε hI (a := a-1) (by simp [ha])
  simpa using hn.isUnit_add_one

lemma isUnit_iff_reduce_ne_zero (a : R) : IsUnit a ↔ ε a ≠ 0 := by
  constructor
  · intro h
    exact (h.map ε.toRingHom).ne_zero
  · intro ha
    have hh : ε a = 1 := by
      have hh : ∀x : ZMod 2, x ≠ 0 → x = 1 := by decide
      exact hh _ ha
    exact isUnit_of_reduce_one ε hI hh

lemma isUnit_matrix_of_reduce_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι R} (hA : ε.toRingHom.mapMatrix A = 1) : IsUnit A := by
  have hnil : IsNilpotent (A-1) := matrix_nil ε hI (A-1) (by
    intro i j
    have he := congrArg (fun M : Matrix ι ι (ZMod 2) => M i j)
      (show ε.toRingHom.mapMatrix (A-1) = 0 by rw [map_sub, hA, map_one, sub_self])
    exact he)
  simpa using hnil.isUnit_add_one

theorem isUnit_matrix_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) : IsUnit A ↔ IsUnit (ε.toRingHom.mapMatrix A) := by
  constructor
  · exact fun h => h.map ε.toRingHom.mapMatrix
  · rintro ⟨U, hU⟩
    let B : (Matrix ι ι R)ˣ := Units.map (algebraMap (ZMod 2) R).mapMatrix.toMonoidHom U⁻¹
    have hB : ε.toRingHom.mapMatrix (B : Matrix ι ι R) = (U⁻¹ : (Matrix ι ι (ZMod 2))ˣ) := by
      ext i j
      simp [B, RingHom.mapMatrix_apply]
    have hBA : ε.toRingHom.mapMatrix ((B : Matrix ι ι R)*A) = 1 := by
      rw [map_mul, hB, ← hU]
      exact U.inv_val
    have hu := isUnit_matrix_of_reduce_one ε hI hBA
    have he : (↑B⁻¹ : Matrix ι ι R) * ((B : Matrix ι ι R)*A) = A := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [← he]
    exact B⁻¹.isUnit.mul hu

open MatrixGenerators

omit hI in
lemma relabel_reduce_one {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (U : (Matrix ι ι R)ˣ) (hU : ε.toRingHom.mapMatrix U.val = 1) :
    ε.toRingHom.mapMatrix (relabel e U).val = 1 := by
  ext i j
  have he := congrArg (fun M : Matrix ι ι (ZMod 2) => M (e.symm i) (e.symm j)) hU
  simpa [relabel, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply] using he

omit hI [Algebra (ZMod 2) R] in
lemma relabel_symm_apply {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (U : (Matrix κ κ R)ˣ) : relabel e (relabel e.symm U) = U := by
  apply Units.ext
  ext i j
  simp [relabel, Matrix.reindex_apply, Matrix.submatrix_apply]

lemma identity_residue_generated : ∀ (n : ℕ) (U : (Matrix (Fin n) (Fin n) R)ˣ),
    ε.toRingHom.mapMatrix U.val = 1 → U ∈ generated
  | 0, U, hU => by
    have he : U = 1 := Subsingleton.elim _ _
    rw [he]
    exact Subgroup.one_mem _
  | n+1, U, hU => by
    let e : Fin n ⊕ Fin 1 ≃ Fin (n+1) := finSumFinEquiv
    let V := relabel e.symm U
    have hV : ε.toRingHom.mapMatrix V.val = 1 := relabel_reduce_one ε e.symm U hU
    have hp : ε (V.val (Sum.inr 0) (Sum.inr 0)) = 1 := by
      have hh := congrArg (fun M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) (ZMod 2) =>
        M (Sum.inr 0) (Sum.inr 0)) hV
      simpa using hh
    obtain ⟨u, hu⟩ := isUnit_of_reduce_one ε hI hp
    let B : Matrix (Fin n) (Fin n) R := Matrix.of (fun i j =>
      V.val (Sum.inl i) (Sum.inl j) - V.val (Sum.inl i) (Sum.inr 0) * u.inv * V.val (Sum.inr 0) (Sum.inl j))
    have hB : ε.toRingHom.mapMatrix B = 1 := by
      ext i j
      have hh := congrArg (fun M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) (ZMod 2) =>
        M (Sum.inl i) (Sum.inl j)) hV
      have ho : ε (V.val (Sum.inl i) (Sum.inr 0)) = 0 := by
        have hh := congrArg (fun M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) (ZMod 2) =>
          M (Sum.inl i) (Sum.inr 0)) hV
        simpa using hh
      simpa [B, map_sub, map_mul, ho, Matrix.one_apply] using hh
    obtain ⟨S, hS⟩ := isUnit_matrix_of_reduce_one ε hI hB
    have hSgen : S ∈ generated := identity_residue_generated n S (by rw [hS]; exact hB)
    have he : upperStrip (fun i => V.val (Sum.inl i) (Sum.inr 0) * u.inv) *
        (blockInclusion (κ := Fin 1) S * singleDiagonal (Sum.inr 0) u) *
        lowerStrip (fun j => u.inv * V.val (Sum.inr 0) (Sum.inl j)) = V :=
      Units.ext (schur_factorization V.val u hu.symm S hS)
    have hvg : V ∈ generated := by
      rw [← he]
      apply Subgroup.mul_mem
      · exact Subgroup.mul_mem _ (upperStrip_mem _) (Subgroup.mul_mem _
          (blockInclusion_mem hSgen) (singleDiagonal_mem _ _))
      · exact lowerStrip_mem _
    have hh := relabel_mem e hvg
    simpa only [V, relabel_symm_apply] using hh

omit hI [Algebra (ZMod 2) R] in
lemma representation_mem_generated {n : ℕ} (g : Steinberg n R) :
    Elementary.representation g ∈ generated := by
  have H : (⊤ : Subgroup (Steinberg n R)) ≤
      (generated (ι := Fin n) (R := R)).comap Elementary.representation := by
    rw [← Steinberg.closure_range_x]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨⟨p,a⟩, rfl⟩
    change Elementary.representation (Steinberg.x p a) ∈ generated
    rw [Elementary.representation_x]
    exact elementary_mem p.row p.col p.ne a
  exact H (Subgroup.mem_top g)

theorem full_matrix_generated (n : ℕ) (U : (Matrix (Fin n) (Fin n) R)ˣ) :
    U ∈ generated := by
  let red : (Matrix (Fin n) (Fin n) R)ˣ →* (Matrix (Fin n) (Fin n) (ZMod 2))ˣ :=
    Units.map ε.toRingHom.mapMatrix.toMonoidHom
  let N : (Matrix (Fin n) (Fin n) R)ˣ := Kernel.numericUnits (red U)
  obtain ⟨g, hg⟩ := Kernel.numerical_lift (R := R) (red U)
  have hN : red N = red U := by
    apply Units.ext
    ext i j
    simp [red, N, Kernel.numericUnits]
  have hid : ε.toRingHom.mapMatrix (N⁻¹*U).val = 1 := by
    have hh : red (N⁻¹*U) = 1 := by rw [map_mul, map_inv, hN, inv_mul_cancel]
    exact congrArg Units.val hh
  have hgen := identity_residue_generated ε hI n (N⁻¹*U) hid
  have hngen : N ∈ generated := by
    change Kernel.numericUnits (red U) ∈ generated
    rw [← hg]
    exact representation_mem_generated g
  have hh := Subgroup.mul_mem _ hngen hgen
  simpa only [mul_inv_cancel_left] using hh

theorem all_matrix_generated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : (Matrix ι ι R)ˣ) : U ∈ generated := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hh := relabel_mem e (full_matrix_generated ε hI _ (relabel e.symm U))
  simpa only [relabel_symm_apply] using hh

end
end SourceBurnside.Stability.LinearAlgebra

end

end OAI
