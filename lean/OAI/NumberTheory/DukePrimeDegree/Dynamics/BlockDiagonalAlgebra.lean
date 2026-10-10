import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Matrix.Basis

namespace OAI

/-!
# The algebra of scalars on root blocks

For a partition of the coordinate indices, the block-scalar algebra is
the actual diagonal matrix algebra whose diagonal is constant on each
block. Its dimension is the number of blocks. It is also the common
centralizer of the full diagonal algebra and the elementary root
matrices within the blocks. These are algebraic statements, without
any homogeneous-measure classification assumption.
-/

noncomputable section
open Matrix
open scoped Classical

namespace DukePrimeDegree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal representation of functions on the coordinate blocks. -/
def blockScalarAlgHom (r : Setoid ι) :
    (Quotient r → ℝ) →ₐ[ℝ] Matrix ι ι ℝ where
  toFun c := Matrix.diagonal (fun i => c (Quotient.mk r i))
  map_zero' := by ext i j; simp
  map_one' := by ext i j; simp [Matrix.one_apply]
  map_add' a b := (Matrix.diagonal_add _ _).symm
  map_mul' := by
    intro a b
    rw [Matrix.diagonal_mul_diagonal]
    rfl
  commutes' := by intro c; rfl

@[simp] lemma blockScalarAlgHom_apply (r : Setoid ι) (c : Quotient r → ℝ) :
    blockScalarAlgHom r c = Matrix.diagonal (fun i => c (Quotient.mk r i)) := rfl

lemma blockScalarAlgHom_injective (r : Setoid ι) :
    Function.Injective (blockScalarAlgHom r) := by
  intro a b h
  funext x
  induction x using Quotient.inductionOn with
  | h i =>
    have he := congrArg (fun M : Matrix ι ι ℝ => M i i) h
    simpa only [blockScalarAlgHom_apply, Matrix.diagonal_apply_eq] using he

/-- The real algebra of diagonal matrices constant on each root block. -/
def blockScalarAlgebra (r : Setoid ι) : Subalgebra ℝ (Matrix ι ι ℝ) :=
  (blockScalarAlgHom r).range

lemma mem_blockScalarAlgebra_iff (r : Setoid ι) (M : Matrix ι ι ℝ) :
    M ∈ blockScalarAlgebra r ↔
      M = Matrix.diagonal (fun i => M i i) ∧ ∀ i j, r i j → M i i = M j j := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨?_, ?_⟩
    · change Matrix.diagonal (fun i => c (Quotient.mk r i)) =
        Matrix.diagonal (fun i => Matrix.diagonal (fun k => c (Quotient.mk r k)) i i)
      simp only [Matrix.diagonal_apply_eq]
    · intro i j hij
      change Matrix.diagonal (fun k => c (Quotient.mk r k)) i i =
        Matrix.diagonal (fun k => c (Quotient.mk r k)) j j
      simpa only [Matrix.diagonal_apply_eq] using congrArg c (Quotient.sound hij)
  · rintro ⟨hd, hr⟩
    let c : Quotient r → ℝ := Quotient.lift (fun i => M i i) (fun i j hij => hr i j hij)
    refine ⟨c, ?_⟩
    change Matrix.diagonal (fun i => M i i) = M
    exact hd.symm

/-- The dimension counts the actual coordinate blocks. -/
theorem finrank_blockScalarAlgebra (r : Setoid ι) :
    Module.finrank ℝ (blockScalarAlgebra r) = Nat.card (Quotient r) := by
  let : Fintype (Quotient r) := Fintype.ofFinite _
  let e := AlgEquiv.ofInjective (blockScalarAlgHom r) (blockScalarAlgHom_injective r)
  change Module.finrank ℝ (blockScalarAlgHom r).range = _
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

/-- Commutation with all diagonal matrices forces a matrix to be diagonal. -/
theorem matrix_eq_diagonal_of_commute_diagonals (M : Matrix ι ι ℝ)
    (hM : ∀ c : ι → ℝ, Commute M (Matrix.diagonal c)) :
    M = Matrix.diagonal (fun i => M i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · have he := congrArg (fun A : Matrix ι ι ℝ => A i j)
      (hM (fun k => if k = i then 1 else 0)).eq
    rw [Matrix.diagonal_apply_ne _ hij]
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Ne.symm hij] using he.symm

/-- A diagonal matrix commutes with an elementary root exactly when
its two corresponding diagonal entries coincide. -/
theorem diagonal_commute_transvection_iff (c : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    Commute (Matrix.diagonal c) (Matrix.transvection i j 1) ↔ c i = c j := by
  constructor
  · intro h
    have he := congrArg (fun A : Matrix ι ι ℝ => A i j) h.eq
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply, hij] using he
  · intro hc
    change Matrix.diagonal c * Matrix.transvection i j 1 =
      Matrix.transvection i j 1 * Matrix.diagonal c
    ext a b
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hab : a = b
    · subst b
      rw [mul_comm]
    · by_cases hai : a = i
      · subst a
        by_cases hbj : b = j
        · subst b
          rw [hc, mul_comm]
        · simp [Matrix.transvection, hab, Ne.symm hbj]
      · simp [Matrix.transvection, hab, Ne.symm hai]

/-- The block-scalar algebra is the exact common matrix centralizer of
diagonals and within-block root generators. -/
theorem mem_blockScalarAlgebra_iff_commutes (r : Setoid ι) (M : Matrix ι ι ℝ) :
    M ∈ blockScalarAlgebra r ↔
      (∀ c : ι → ℝ, Commute M (Matrix.diagonal c)) ∧
      ∀ i j, i ≠ j → r i j → Commute M (Matrix.transvection i j 1) := by
  rw [mem_blockScalarAlgebra_iff]
  constructor
  · rintro ⟨hd, hr⟩
    constructor
    · intro c
      rw [hd]
      exact Matrix.commute_diagonal _ _
    · intro i j hij hrij
      rw [hd]
      exact (diagonal_commute_transvection_iff _ hij).mpr (hr i j hrij)
  · rintro ⟨hd, hr⟩
    have hdiag := matrix_eq_diagonal_of_commute_diagonals M hd
    refine ⟨hdiag, ?_⟩
    intro i j hrij
    by_cases hij : i = j
    · subst j
      rfl
    · apply (diagonal_commute_transvection_iff _ hij).mp
      rw [← hdiag]
      exact hr i j hij hrij

/-- A matrix commuting with every block scalar has no entries between
different coordinate blocks. -/
theorem commute_blockScalars_iff (r : Setoid ι) (M : Matrix ι ι ℝ) :
    (∀ A ∈ blockScalarAlgebra r, Commute M A) ↔
      ∀ i j, ¬ r i j → M i j = 0 := by
  constructor
  · intro h i j hij
    let c : Quotient r → ℝ := fun q => if q = Quotient.mk r i then 1 else 0
    have hq : Quotient.mk r j ≠ Quotient.mk r i := by
      intro he
      exact hij (r.symm (Quotient.exact he))
    have he := congrArg (fun A : Matrix ι ι ℝ => A i j)
      (h (blockScalarAlgHom r c) ⟨c, rfl⟩).eq
    change (M * Matrix.diagonal (fun k => c (Quotient.mk r k))) i j =
      (Matrix.diagonal (fun k => c (Quotient.mk r k)) * M) i j at he
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, c, hq] using he.symm
  · intro h A hA
    obtain ⟨c, rfl⟩ := hA
    change M * blockScalarAlgHom r c = blockScalarAlgHom r c * M
    ext i j
    change (M * Matrix.diagonal (fun k => c (Quotient.mk r k))) i j =
      (Matrix.diagonal (fun k => c (Quotient.mk r k)) * M) i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : r i j
    · rw [Quotient.sound hij, mul_comm]
    · rw [h i j hij, zero_mul, mul_zero]

/-- A single root block has only scalar matrices in its centralizer. -/
theorem blockScalarAlgebra_eq_bot_of_universal [Nonempty ι] (r : Setoid ι)
    (hr : ∀ i j, r i j) : blockScalarAlgebra r = ⊥ := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  apply le_antisymm ?_ bot_le
  intro M hM
  obtain ⟨hd, hc⟩ := (mem_blockScalarAlgebra_iff r M).mp hM
  apply Algebra.mem_bot.mpr
  refine ⟨M i₀ i₀, ?_⟩
  change Matrix.diagonal (fun _ => M i₀ i₀) = M
  calc
    Matrix.diagonal (fun _ => M i₀ i₀) = Matrix.diagonal (fun i => M i i) := by
      congr 1
      funext i
      exact (hc i i₀ (hr i i₀)).symm
    _ = M := hd.symm

/-- Conversely, a proper partition always has a non-scalar block
projection. This turns a scalar-centralizer conclusion into one block. -/
theorem universal_of_blockScalarAlgebra_eq_bot (r : Setoid ι)
    (hbot : blockScalarAlgebra r = ⊥) : ∀ i j, r i j := by
  intro i j
  by_contra hij
  let c : Quotient r → ℝ := fun q => if q = Quotient.mk r i then 1 else 0
  have hq : Quotient.mk r j ≠ Quotient.mk r i := by
    intro he
    exact hij (r.symm (Quotient.exact he))
  have hM : blockScalarAlgHom r c ∈ (⊥ : Subalgebra ℝ (Matrix ι ι ℝ)) := by
    rw [← hbot]
    exact ⟨c, rfl⟩
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hM
  have hi : a = c (Quotient.mk r i) := by
    simpa [Matrix.algebraMap_matrix_apply] using congrArg (fun M : Matrix ι ι ℝ => M i i) ha
  have hj : a = c (Quotient.mk r j) := by
    simpa [Matrix.algebraMap_matrix_apply] using congrArg (fun M : Matrix ι ι ℝ => M j j) ha
  have he := hi.symm.trans hj
  simp [c, hq] at he

end DukePrimeDegree

end

end OAI
