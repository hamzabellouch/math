import Mathlib
import OAI.Computability.MaxCut.Encoding.BinaryCoordinates

namespace OAI

/-! Trace characters on actual finite binary matrix spaces. -/

noncomputable section

namespace MaxCutGames.Fourier.MatrixCharacters

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear

abbrev F2 := MaxCutGames.Integration.BinaryLinear.F2

/-- The binary trace pairing between oppositely oriented matrices. -/
def tracePair {n m : Nat} (X : Matrix (Fin n) (Fin m) F2)
    (S : Matrix (Fin m) (Fin n) F2) : F2 := Matrix.trace (X * S)

theorem tracePair_eq_sum_entries {n m : Nat} (X : Matrix (Fin n) (Fin m) F2)
    (S : Matrix (Fin m) (Fin n) F2) :
    tracePair X S = ∑ i, ∑ j, X i j * S j i := rfl

theorem tracePair_swap {n m : Nat} (X : Matrix (Fin n) (Fin m) F2)
    (S : Matrix (Fin m) (Fin n) F2) : tracePair X S = tracePair S X :=
  Matrix.trace_mul_comm X S

@[simp] theorem tracePair_zero_left {n m : Nat} (S : Matrix (Fin m) (Fin n) F2) :
    tracePair (0 : Matrix (Fin n) (Fin m) F2) S = 0 := by simp [tracePair]

@[simp] theorem tracePair_zero_right {n m : Nat} (X : Matrix (Fin n) (Fin m) F2) :
    tracePair X (0 : Matrix (Fin m) (Fin n) F2) = 0 := by simp [tracePair]

theorem tracePair_add_left {n m : Nat} (X Y : Matrix (Fin n) (Fin m) F2)
    (S : Matrix (Fin m) (Fin n) F2) :
    tracePair (X + Y) S = tracePair X S + tracePair Y S := by
  simp [tracePair, Matrix.add_mul]

theorem tracePair_add_right {n m : Nat} (X : Matrix (Fin n) (Fin m) F2)
    (S T : Matrix (Fin m) (Fin n) F2) :
    tracePair X (S + T) = tracePair X S + tracePair X T := by
  simp [tracePair, Matrix.mul_add]

theorem tracePair_ext_right {n m : Nat} {S T : Matrix (Fin m) (Fin n) F2}
    (h : ∀ X, tracePair X S = tracePair X T) : S = T :=
  Matrix.ext_iff_trace_mul_left.mpr h

theorem tracePair_ext_left {n m : Nat} {X Y : Matrix (Fin n) (Fin m) F2}
    (h : ∀ S, tracePair X S = tracePair Y S) : X = Y :=
  Matrix.ext_iff_trace_mul_right.mpr h

/-- A nonzero matrix has trace pairing one with a dual matrix. -/
theorem exists_tracePair_eq_one {n m : Nat} (S : Matrix (Fin m) (Fin n) F2)
    (hS : S ≠ 0) : ∃ X, tracePair X S = 1 := by
  by_contra h
  apply hS
  apply tracePair_ext_right
  intro X
  rw [tracePair_zero_right]
  rcases scalar_cases (tracePair X S) with hzero | hone
  · exact hzero
  · exact False.elim (h ⟨X, hone⟩)

/-- The unique nontrivial complex-valued character of the binary field. -/
def binarySign (a : F2) : ℂ := if a = 0 then 1 else -1

@[simp] theorem binarySign_zero : binarySign 0 = 1 := by simp [binarySign]
@[simp] theorem binarySign_one : binarySign 1 = -1 := by simp [binarySign]

theorem binarySign_eq_neg_one_pow_val (a : F2) :
    binarySign a = (-1 : ℂ) ^ a.val := by
  rcases scalar_cases a with rfl | rfl <;>
    simp [show (1 : F2).val = 1 by decide]

theorem binarySign_add (a b : F2) : binarySign (a + b) = binarySign a * binarySign b := by
  have htwo : (1 : F2) + 1 = 0 := by decide
  rcases scalar_cases a with rfl | rfl <;>
    rcases scalar_cases b with rfl | rfl <;> simp [htwo]

theorem binarySign_sum {ι : Type*} (s : Finset ι) (f : ι → F2) :
    binarySign (∑ i ∈ s, f i) = ∏ i ∈ s, binarySign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, binarySign_add, ih]

theorem binarySign_injective : Function.Injective binarySign := by
  intro a b h
  rcases scalar_cases a with rfl | rfl <;>
    rcases scalar_cases b with rfl | rfl
  · rfl
  · have hf : (1 : ℂ) = -1 := by simpa using h
    exact False.elim (one_ne_zero ((CharZero.eq_neg_self_iff).mp hf))
  · have hf : (1 : ℂ) = -1 := by simpa using h.symm
    exact False.elim (one_ne_zero ((CharZero.eq_neg_self_iff).mp hf))
  · rfl

theorem binarySign_real (a : F2) : ((binarySign a).re : ℂ) = binarySign a := by
  unfold binarySign
  split <;> simp

@[simp] theorem binarySign_im (a : F2) : (binarySign a).im = 0 := by
  unfold binarySign
  split <;> simp

@[simp] theorem binarySign_mul_self (a : F2) : binarySign a * binarySign a = 1 := by
  unfold binarySign
  split <;> simp

section LinearFunctionals

variable {E : Type*} [AddCommGroup E] [Module F2 E]

/-- A binary linear functional determines a complex additive character. -/
def linearFunctionalCharacter (φ : E →ₗ[F2] F2) : AddChar E ℂ where
  toFun x := binarySign (φ x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [map_add, binarySign_add]

@[simp] theorem linearFunctionalCharacter_apply (φ : E →ₗ[F2] F2) (x : E) :
    linearFunctionalCharacter φ x = binarySign (φ x) := rfl

@[simp] theorem linearFunctionalCharacter_zero :
    linearFunctionalCharacter (0 : E →ₗ[F2] F2) = 0 := by
  ext x
  simp

theorem linearFunctionalCharacter_injective :
    Function.Injective (linearFunctionalCharacter (E := E)) := by
  intro φ ψ h
  ext x
  apply binarySign_injective
  exact congrArg (fun χ : AddChar E ℂ => χ x) h

theorem linearFunctionalCharacter_eq_zero_iff (φ : E →ₗ[F2] F2) :
    linearFunctionalCharacter φ = 0 ↔ φ = 0 := by
  rw [← linearFunctionalCharacter_zero, linearFunctionalCharacter_injective.eq_iff]

theorem sum_linearFunctionalCharacter [Fintype E] (φ : E →ₗ[F2] F2) :
    ∑ x, linearFunctionalCharacter φ x =
      if φ = 0 then (Fintype.card E : ℂ) else 0 := by
  rw [AddChar.sum_eq_ite]
  simp only [linearFunctionalCharacter_eq_zero_iff]

theorem expect_linearFunctionalCharacter [Fintype E] (φ : E →ₗ[F2] F2) :
    (𝔼 x, linearFunctionalCharacter φ x) = if φ = 0 then 1 else 0 := by
  rw [Fintype.expect_eq_sum_div_card, sum_linearFunctionalCharacter]
  split_ifs <;> simp [Fintype.card_ne_zero]

end LinearFunctionals

def traceCharacter {n m : Nat} (S : Matrix (Fin m) (Fin n) F2) :
    AddChar (Matrix (Fin n) (Fin m) F2) ℂ where
  toFun X := binarySign (tracePair X S)
  map_zero_eq_one' := by simp
  map_add_eq_mul' X Y := by rw [tracePair_add_left, binarySign_add]

@[simp] theorem traceCharacter_apply {n m : Nat} (S : Matrix (Fin m) (Fin n) F2)
    (X : Matrix (Fin n) (Fin m) F2) :
    traceCharacter S X = binarySign (tracePair X S) := rfl

theorem traceCharacter_eq_coordinate_sign {n m : Nat} (S : Matrix (Fin m) (Fin n) F2)
    (X : Matrix (Fin n) (Fin m) F2) :
    traceCharacter S X = if (∑ i, ∑ j, X i j * S j i) = 0 then 1 else -1 := rfl

theorem traceCharacter_eq_trace_exponent {n m : Nat} (S : Matrix (Fin m) (Fin n) F2)
    (X : Matrix (Fin n) (Fin m) F2) :
    traceCharacter S X = (-1 : ℂ) ^ (Matrix.trace (X * S)).val :=
  binarySign_eq_neg_one_pow_val _

theorem traceCharacter_eq_product_entries {n m : Nat} (S : Matrix (Fin m) (Fin n) F2)
    (X : Matrix (Fin n) (Fin m) F2) :
    traceCharacter S X = ∏ i, ∏ j, binarySign (X i j * S j i) := by
  simp only [traceCharacter_apply, tracePair_eq_sum_entries, binarySign_sum]

theorem traceCharacter_real {n m : Nat} (S : Matrix (Fin m) (Fin n) F2)
    (X : Matrix (Fin n) (Fin m) F2) :
    ((traceCharacter S X).re : ℂ) = traceCharacter S X := binarySign_real _

theorem traceCharacter_add {n m : Nat} (S T : Matrix (Fin m) (Fin n) F2) :
    traceCharacter (S + T) = traceCharacter S + traceCharacter T := by
  ext X
  simp only [traceCharacter_apply, tracePair_add_right, binarySign_add, AddChar.add_apply]

@[simp] theorem traceCharacter_zero {n m : Nat} :
    traceCharacter (0 : Matrix (Fin m) (Fin n) F2) = 0 := by
  ext X
  simp

theorem traceCharacter_injective {n m : Nat} :
    Function.Injective (traceCharacter (n := n) (m := m)) := by
  intro S T h
  apply tracePair_ext_right
  intro X
  apply binarySign_injective
  exact congrArg (fun ψ : AddChar (Matrix (Fin n) (Fin m) F2) ℂ => ψ X) h

theorem traceCharacter_eq_zero_iff {n m : Nat} (S : Matrix (Fin m) (Fin n) F2) :
    traceCharacter S = 0 ↔ S = 0 := by
  rw [← traceCharacter_zero, traceCharacter_injective.eq_iff]

theorem sum_traceCharacter {n m : Nat} (S : Matrix (Fin m) (Fin n) F2) :
    ∑ X, traceCharacter S X =
      if S = 0 then (Fintype.card (Matrix (Fin n) (Fin m) F2) : ℂ) else 0 := by
  classical
  rw [AddChar.sum_eq_ite]
  simp only [traceCharacter_eq_zero_iff]

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

/-- The basis-independent trace pairing in the statement of Lemma 2.1. -/
def linearTracePair (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) : F2 :=
  LinearMap.trace F2 F (X.comp S)

theorem linearTracePair_eq_matrix_tracePair {n m : Nat}
    (bE : Module.Basis (Fin m) F2 E) (bF : Module.Basis (Fin n) F2 F)
    (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair X S =
      tracePair (LinearMap.toMatrix bE bF X) (LinearMap.toMatrix bF bE S) := by
  change LinearMap.trace F2 F (X.comp S) =
    Matrix.trace (LinearMap.toMatrix bE bF X * LinearMap.toMatrix bF bE S)
  rw [LinearMap.trace_eq_matrix_trace F2 bF, LinearMap.toMatrix_comp bF bE bF]

@[simp] theorem linearTracePair_zero_left (S : F →ₗ[F2] E) :
    linearTracePair (0 : E →ₗ[F2] F) S = 0 := by simp [linearTracePair]

@[simp] theorem linearTracePair_zero_right (X : E →ₗ[F2] F) :
    linearTracePair X (0 : F →ₗ[F2] E) = 0 := by simp [linearTracePair]

theorem linearTracePair_add_left (X Y : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair (X + Y) S = linearTracePair X S + linearTracePair Y S := by
  simp [linearTracePair, LinearMap.add_comp]

theorem linearTracePair_add_right (X : E →ₗ[F2] F) (S T : F →ₗ[F2] E) :
    linearTracePair X (S + T) = linearTracePair X S + linearTracePair X T := by
  simp [linearTracePair, LinearMap.comp_add]

/-- The trace character on actual linear maps, with no choice of basis. -/
def linearTraceCharacter (S : F →ₗ[F2] E) : AddChar (E →ₗ[F2] F) ℂ where
  toFun X := binarySign (linearTracePair X S)
  map_zero_eq_one' := by simp
  map_add_eq_mul' X Y := by rw [linearTracePair_add_left, binarySign_add]

@[simp] theorem linearTraceCharacter_apply (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearTraceCharacter S X = binarySign (linearTracePair X S) := rfl

theorem linearTraceCharacter_real (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    ((linearTraceCharacter S X).re : ℂ) = linearTraceCharacter S X := binarySign_real _

theorem linearTraceCharacter_add (S T : F →ₗ[F2] E) :
    linearTraceCharacter (S + T) = linearTraceCharacter S + linearTraceCharacter T := by
  ext X
  simp only [linearTraceCharacter_apply, linearTracePair_add_right, binarySign_add,
    AddChar.add_apply]

@[simp] theorem linearTraceCharacter_zero :
    linearTraceCharacter (0 : F →ₗ[F2] E) = 0 := by
  ext X
  simp

theorem linearTraceCharacter_eq_matrix_traceCharacter {n m : Nat}
    (bE : Module.Basis (Fin m) F2 E) (bF : Module.Basis (Fin n) F2 F)
    (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearTraceCharacter S X =
      traceCharacter (LinearMap.toMatrix bF bE S) (LinearMap.toMatrix bE bF X) := by
  simp only [linearTraceCharacter_apply, traceCharacter_apply,
    linearTracePair_eq_matrix_tracePair bE bF]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

theorem linearTracePair_swap (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair X S = linearTracePair S X :=
  LinearMap.trace_comp_comm' S X

theorem linearTraceCharacter_swap (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearTraceCharacter S X = linearTraceCharacter X S := by
  simp only [linearTraceCharacter_apply, linearTracePair_swap X S]

/-- The actual trace pairing is nondegenerate in its dual-map argument. -/
theorem linearTracePair_ext_right {S T : F →ₗ[F2] E}
    (h : ∀ X, linearTracePair X S = linearTracePair X T) : S = T := by
  classical
  let bE := Module.finBasis F2 E
  let bF := Module.finBasis F2 F
  apply (LinearMap.toMatrix bF bE).injective
  apply tracePair_ext_right
  intro X
  obtain ⟨X', rfl⟩ := (LinearMap.toMatrix bE bF).surjective X
  exact (linearTracePair_eq_matrix_tracePair bE bF X' S).symm.trans
    ((h X').trans (linearTracePair_eq_matrix_tracePair bE bF X' T))

/-- Nondegeneracy also holds in the primal-map argument. -/
theorem linearTracePair_ext_left {X Y : E →ₗ[F2] F}
    (h : ∀ S, linearTracePair X S = linearTracePair Y S) : X = Y := by
  classical
  let bE := Module.finBasis F2 E
  let bF := Module.finBasis F2 F
  apply (LinearMap.toMatrix bE bF).injective
  apply tracePair_ext_left
  intro S
  obtain ⟨S', rfl⟩ := (LinearMap.toMatrix bF bE).surjective S
  exact (linearTracePair_eq_matrix_tracePair bE bF X S').symm.trans
    ((h S').trans (linearTracePair_eq_matrix_tracePair bE bF Y S'))

theorem exists_linearTracePair_eq_one (S : F →ₗ[F2] E) (hS : S ≠ 0) :
    ∃ X, linearTracePair X S = 1 := by
  by_contra h
  apply hS
  apply linearTracePair_ext_right
  intro X
  rw [linearTracePair_zero_right]
  rcases scalar_cases (linearTracePair X S) with hzero | hone
  · exact hzero
  · exact False.elim (h ⟨X, hone⟩)

theorem linearTraceCharacter_injective :
    Function.Injective (linearTraceCharacter (E := E) (F := F)) := by
  intro S T h
  apply linearTracePair_ext_right
  intro X
  apply binarySign_injective
  exact congrArg (fun ψ : AddChar (E →ₗ[F2] F) ℂ => ψ X) h

theorem linearTraceCharacter_eq_zero_iff (S : F →ₗ[F2] E) :
    linearTraceCharacter S = 0 ↔ S = 0 := by
  rw [← linearTraceCharacter_zero, linearTraceCharacter_injective.eq_iff]

theorem sum_linearTraceCharacter [Fintype (E →ₗ[F2] F)] (S : F →ₗ[F2] E) :
    ∑ X, linearTraceCharacter S X =
      if S = 0 then (Fintype.card (E →ₗ[F2] F) : ℂ) else 0 := by
  classical
  rw [AddChar.sum_eq_ite]
  simp only [linearTraceCharacter_eq_zero_iff]

end MaxCutGames.Fourier.MatrixCharacters
end

end OAI
