import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Instances.Matrix

namespace OAI

/-! Rectangular matrix comparison, block sums, and reindexing of positive matrices. -/

noncomputable section
open scoped Topology Matrix
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {ι κ ν : Type*} [Fintype κ] [Fintype ν]

/-- Rectangular Cuntz comparison: norm closure of actual conjugations.
The finite product topology here is the topology of the C*-matrix norm. -/
def CuntzLE (a : Matrix ι ι A) (b : Matrix κ κ A) : Prop :=
  a ∈ closure (Set.range fun v : Matrix ι κ A => v * b * v.conjTranspose)

namespace CuntzLE

theorem exact (b : Matrix κ κ A) (v : Matrix ι κ A) :
    CuntzLE (v * b * v.conjTranspose) b := subset_closure ⟨v, rfl⟩

theorem refl [Fintype ι] (a : Matrix ι ι A) : CuntzLE a a := by
  classical
  simpa using exact a (1 : Matrix ι ι A)

theorem zero (b : Matrix κ κ A) : CuntzLE (0 : Matrix ι ι A) b := by
  simpa using exact b (0 : Matrix ι κ A)

theorem isClosed (b : Matrix κ κ A) : IsClosed {a : Matrix ι ι A | CuntzLE a b} :=
  isClosed_closure

theorem of_mem_closure {s : Set (Matrix ι ι A)} {a : Matrix ι ι A}
    {b : Matrix κ κ A} (ha : a ∈ closure s) (hs : ∀ x ∈ s, CuntzLE x b) :
    CuntzLE a b := (isClosed b).closure_subset_iff.mpr hs ha

theorem conjugate {a : Matrix κ κ A} {b : Matrix ν ν A} (h : CuntzLE a b)
    (v : Matrix ι κ A) : CuntzLE (v * a * v.conjTranspose) b := by
  have hc : Continuous (fun x : Matrix κ κ A => v * x * v.conjTranspose) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  apply of_mem_closure ((image_closure_subset_closure_image hc) ⟨a, h, rfl⟩)
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using exact b (v * w)

theorem trans {a : Matrix ι ι A} {b : Matrix κ κ A} {c : Matrix ν ν A}
    (hab : CuntzLE a b) (hbc : CuntzLE b c) : CuntzLE a c := by
  apply of_mem_closure hab
  rintro _ ⟨v, rfl⟩
  exact hbc.conjugate v

theorem of_eq {a a' : Matrix ι ι A} {b b' : Matrix κ κ A}
    (ha : a = a') (hb : b = b') (h : CuntzLE a' b') : CuntzLE a b := ha ▸ hb ▸ h

theorem le_zero_iff (a : Matrix ι ι A) : CuntzLE a (0 : Matrix κ κ A) ↔ a = 0 := by
  simp [CuntzLE]

/-- Explicit norm-approximation contract, using the actual C*-matrix norm. -/
theorem iff_approx [Fintype ι] (a : Matrix ι ι A) (b : Matrix κ κ A) :
    CuntzLE a b ↔ ∀ ε : ℝ, 0 < ε → ∃ v : Matrix ι κ A,
      ‖CStarMatrix.ofMatrix (a - v * b * v.conjTranspose)‖ < ε := by
  change CStarMatrix.ofMatrix a ∈ closure (Set.range fun v : Matrix ι κ A =>
    CStarMatrix.ofMatrix (v * b * v.conjTranspose)) ↔ _
  rw [Metric.mem_closure_iff]
  simp only [Set.mem_range, exists_exists_eq_and, dist_eq_norm]
  rfl

end CuntzLE

variable [Fintype ι]

/-- Mutual actual rectangular comparison; no order or state is assumed. -/
def CuntzEquivalent (a : Matrix ι ι A) (b : Matrix κ κ A) : Prop :=
  CuntzLE a b ∧ CuntzLE b a

namespace CuntzEquivalent

theorem refl (a : Matrix ι ι A) : CuntzEquivalent a a := ⟨.refl a, .refl a⟩
theorem symm {a : Matrix ι ι A} {b : Matrix κ κ A}
    (h : CuntzEquivalent a b) : CuntzEquivalent b a := ⟨h.2, h.1⟩

theorem trans {a : Matrix ι ι A} {b : Matrix κ κ A} {c : Matrix ν ν A}
    (h : CuntzEquivalent a b) (h' : CuntzEquivalent b c) : CuntzEquivalent a c :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

end CuntzEquivalent
end Kaplansky

end

noncomputable section
open scoped Topology Matrix
namespace Kaplansky
variable {A : Type*} [CStarAlgebra A]
variable {ι κ ν μ : Type*}

/-- Block addition before passing to Cuntz classes. -/
def cuntzBlock (a : Matrix ι ι A) (b : Matrix κ κ A) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) A := Matrix.fromBlocks a 0 0 b

theorem continuous_cuntzBlock : Continuous (fun p : Matrix ι ι A × Matrix κ κ A =>
    cuntzBlock p.1 p.2) := by
  apply continuous_matrix
  intro i j
  cases i <;> cases j <;> dsimp [cuntzBlock, Matrix.fromBlocks] <;> fun_prop

variable [Fintype κ] [Fintype μ]

theorem cuntzBlock_conjugate (a : Matrix κ κ A) (b : Matrix μ μ A)
    (v : Matrix ι κ A) (w : Matrix ν μ A) :
    (Matrix.fromBlocks v 0 0 w) * cuntzBlock a b *
      (Matrix.fromBlocks v 0 0 w).conjTranspose =
      cuntzBlock (v * a * v.conjTranspose) (w * b * w.conjTranspose) := by
  simp [cuntzBlock, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

/-- Actual rectangular comparison is compatible with block addition. -/
theorem CuntzLE.block {a : Matrix ι ι A} {b : Matrix κ κ A}
    {c : Matrix ν ν A} {d : Matrix μ μ A} (hab : CuntzLE a b) (hcd : CuntzLE c d) :
    CuntzLE (cuntzBlock a c) (cuntzBlock b d) := by
  have hp : (a, c) ∈ closure ((Set.range fun v : Matrix ι κ A => v * b * v.conjTranspose) ×ˢ
      (Set.range fun w : Matrix ν μ A => w * d * w.conjTranspose)) := by
    rw [closure_prod_eq]
    exact ⟨hab, hcd⟩
  apply CuntzLE.of_mem_closure ((image_closure_subset_closure_image continuous_cuntzBlock) ⟨(a,c), hp, rfl⟩)
  rintro _ ⟨⟨_, _⟩, ⟨⟨v, rfl⟩, ⟨w, rfl⟩⟩, rfl⟩
  simpa only [cuntzBlock_conjugate] using
    CuntzLE.exact (cuntzBlock b d) (Matrix.fromBlocks v 0 0 w)

variable [Fintype ι] [Fintype ν]

theorem CuntzEquivalent.block {a : Matrix ι ι A} {b : Matrix κ κ A}
    {c : Matrix ν ν A} {d : Matrix μ μ A} (hab : CuntzEquivalent a b)
    (hcd : CuntzEquivalent c d) : CuntzEquivalent (cuntzBlock a c) (cuntzBlock b d) :=
  ⟨hab.1.block hcd.1, hab.2.block hcd.2⟩

end Kaplansky

end

noncomputable section
open scoped Topology Matrix
namespace Kaplansky
variable {A : Type*} [CStarAlgebra A]
variable {ι κ ν : Type*} [Fintype ι] [Fintype ν]

/-- Taking the same row and column submatrix is an actual rectangular conjugation. -/
theorem CuntzLE.submatrix (a : Matrix ι ι A) (f : κ → ι) :
    CuntzLE (a.submatrix f f) a := by
  classical
  have he : (1 : Matrix ι ι A).submatrix f id * a *
      ((1 : Matrix ι ι A).submatrix f id).conjTranspose = a.submatrix f f := by
    rw [Matrix.conjTranspose_submatrix]
    simp only [Matrix.conjTranspose_one]
    have hleft : (1 : Matrix ι ι A).submatrix f id * a = a.submatrix f id := by
      simpa using Matrix.one_submatrix_mul f (Equiv.refl ι) a
    rw [hleft]
    simpa using Matrix.mul_submatrix_one (Equiv.refl ι) f (a.submatrix f id)
  rw [← he]
  exact CuntzLE.exact _ _

variable [Fintype κ]

/-- Relabeling the finite coordinates preserves the actual Cuntz class. -/
theorem cuntzEquivalent_submatrix_equiv (a : Matrix ι ι A) (e : κ ≃ ι) :
    CuntzEquivalent (a.submatrix e e) a := by
  refine ⟨CuntzLE.submatrix a e, ?_⟩
  simpa using CuntzLE.submatrix (a.submatrix e e) e.symm

theorem cuntzLE_submatrix_equiv_iff (a : Matrix ι ι A) (b : Matrix ν ν A)
    (e : κ ≃ ι) : CuntzLE (a.submatrix e e) b ↔ CuntzLE a b := by
  have he := cuntzEquivalent_submatrix_equiv a e
  exact ⟨fun h => he.2.trans h, fun h => he.1.trans h⟩

/-- Enlarging by an arbitrary zero corner does not change a Cuntz class. -/
theorem cuntzEquivalent_block_zero (a : Matrix ι ι A) :
    CuntzEquivalent (cuntzBlock a (0 : Matrix κ κ A)) a := by
  classical
  let v : Matrix (ι ⊕ κ) ι A := Matrix.fromRows 1 0
  have he : v * a * v.conjTranspose = cuntzBlock a (0 : Matrix κ κ A) := by
    simp [v, cuntzBlock, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromRows_mul]
    ext i j
    cases i <;> cases j <;> rfl
  refine ⟨he ▸ CuntzLE.exact a v, ?_⟩
  exact CuntzLE.submatrix (cuntzBlock a (0 : Matrix κ κ A)) Sum.inl

/-- The permutation exchanging the blocks witnesses commutativity. -/
theorem cuntzEquivalent_block_comm (a : Matrix ι ι A) (b : Matrix κ κ A) :
    CuntzEquivalent (cuntzBlock a b) (cuntzBlock b a) := by
  have h := cuntzEquivalent_submatrix_equiv (cuntzBlock b a) (Equiv.sumComm ι κ)
  convert h using 1
  ext i j
  cases i <;> cases j <;> rfl

/-- Rebracketing three blocks witnesses associativity. -/
theorem cuntzEquivalent_block_assoc (a : Matrix ι ι A) (b : Matrix κ κ A)
    (c : Matrix ν ν A) :
    CuntzEquivalent (cuntzBlock (cuntzBlock a b) c) (cuntzBlock a (cuntzBlock b c)) := by
  have h := cuntzEquivalent_submatrix_equiv (cuntzBlock a (cuntzBlock b c))
    (Equiv.sumAssoc ι κ ν)
  convert h using 1
  ext i j
  rcases i with (i | i) | i <;> rcases j with (j | j) | j <;> rfl

end Kaplansky

end

noncomputable section
open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem cuntzBlock_nonneg (a : Matrix ι ι A) (b : Matrix κ κ A)
    (ha : 0 ≤ CStarMatrix.ofMatrix a) (hb : 0 ≤ CStarMatrix.ofMatrix b) :
    0 ≤ CStarMatrix.ofMatrix (cuntzBlock a b) := by
  classical
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix ι ι A) := CStarAlgebra.instNonnegSpectrumClass'
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix κ κ A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix κ κ A) := CStarAlgebra.instNonnegSpectrumClass'
  obtain ⟨x, hx⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := CStarMatrix.ofMatrix a)).mp ha
  obtain ⟨y, hy⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := CStarMatrix.ofMatrix b)).mp hb
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A) := CStarAlgebra.instNonnegSpectrumClass'
  apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr
  refine ⟨CStarMatrix.ofMatrix (cuntzBlock (CStarMatrix.ofMatrix.symm x) (CStarMatrix.ofMatrix.symm y)), ?_⟩
  change cuntzBlock a b =
    (cuntzBlock (CStarMatrix.ofMatrix.symm x) (CStarMatrix.ofMatrix.symm y)).conjTranspose *
      cuntzBlock (CStarMatrix.ofMatrix.symm x) (CStarMatrix.ofMatrix.symm y)
  change a = (CStarMatrix.ofMatrix.symm x).conjTranspose * CStarMatrix.ofMatrix.symm x at hx
  change b = (CStarMatrix.ofMatrix.symm y).conjTranspose * CStarMatrix.ofMatrix.symm y at hy
  simp only [cuntzBlock, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.fromBlocks_inj]
  exact ⟨hx, True.intro, True.intro, hy⟩

theorem cuntzSubmatrix_nonneg (a : Matrix ι ι A) (e : κ ≃ ι)
    (ha : 0 ≤ CStarMatrix.ofMatrix a) :
    0 ≤ CStarMatrix.ofMatrix (a.submatrix e e) := by
  classical
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix ι ι A) := CStarAlgebra.instNonnegSpectrumClass'
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix κ κ A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix κ κ A) := CStarAlgebra.instNonnegSpectrumClass'
  obtain ⟨x, hx⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := CStarMatrix.ofMatrix a)).mp ha
  refine CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr
    ⟨CStarMatrix.ofMatrix ((CStarMatrix.ofMatrix.symm x).submatrix e e), ?_⟩
  change a.submatrix e e =
    ((CStarMatrix.ofMatrix.symm x).submatrix e e).conjTranspose *
      (CStarMatrix.ofMatrix.symm x).submatrix e e
  change a = (CStarMatrix.ofMatrix.symm x).conjTranspose * CStarMatrix.ofMatrix.symm x at hx
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hx]

/-- Every positive finite matrix is Cuntz below its own identity matrix.
The witness is its actual positive square root. -/
theorem cuntzLE_one_of_nonneg [DecidableEq ι] (a : Matrix ι ι A) (ha : 0 ≤ CStarMatrix.ofMatrix a) :
    CuntzLE a (1 : Matrix ι ι A) := by
  classical
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix ι ι A) := CStarAlgebra.instNonnegSpectrumClass'
  let x := CFC.sqrt (CStarMatrix.ofMatrix a)
  have hx : x * star x = CStarMatrix.ofMatrix a := by
    rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self _ ha
  change CStarMatrix.ofMatrix.symm x * (CStarMatrix.ofMatrix.symm x).conjTranspose = a at hx
  have h := CuntzLE.exact (1 : Matrix ι ι A) (CStarMatrix.ofMatrix.symm x)
  simpa only [Matrix.mul_one, hx] using h

/-- An actual positive matrix with a finite, explicitly stored size. -/
structure CuntzPositiveMatrix (A : Type*) [CStarAlgebra A] where
  size : ℕ
  matrix : Matrix (Fin size) (Fin size) A
  nonneg : 0 ≤ CStarMatrix.ofMatrix matrix

namespace CuntzPositiveMatrix

def zero : CuntzPositiveMatrix A := ⟨0, 0, le_rfl⟩

def unit (n : ℕ) : CuntzPositiveMatrix A := ⟨n, 1, zero_le_one⟩

/-- Actual block addition, relabeled by the standard finite-sum equivalence. -/
def add (a b : CuntzPositiveMatrix A) : CuntzPositiveMatrix A where
  size := a.size + b.size
  matrix := (cuntzBlock a.matrix b.matrix).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  nonneg := cuntzSubmatrix_nonneg _ _ (cuntzBlock_nonneg _ _ a.nonneg b.nonneg)

instance : Preorder (CuntzPositiveMatrix A) where
  le a b := CuntzLE a.matrix b.matrix
  le_refl a := .refl a.matrix
  le_trans _ _ _ := CuntzLE.trans

theorem add_equiv (a b : CuntzPositiveMatrix A) :
    CuntzEquivalent (add a b).matrix (cuntzBlock a.matrix b.matrix) :=
  cuntzEquivalent_submatrix_equiv _ _

theorem add_le_add {a b c d : CuntzPositiveMatrix A} (hab : a ≤ b) (hcd : c ≤ d) :
    add a c ≤ add b d :=
  (add_equiv a c).1.trans ((CuntzLE.block hab hcd).trans (add_equiv b d).2)

theorem zero_le (a : CuntzPositiveMatrix A) : zero ≤ a := .zero a.matrix

theorem le_unit (a : CuntzPositiveMatrix A) : a ≤ unit a.size :=
  cuntzLE_one_of_nonneg a.matrix a.nonneg

end CuntzPositiveMatrix
end Kaplansky

end

end OAI
