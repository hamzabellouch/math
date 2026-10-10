import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.FormulaEncoding

namespace OAI

noncomputable section

namespace DFVSGames.Fourier.MatrixCharacters

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear

abbrev F2 := DFVSGames.Integration.BinaryLinear.F2

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

end DFVSGames.Fourier.MatrixCharacters
end

noncomputable section

namespace DFVSGames.Fourier.MatrixParity

open DFVSGames.Integration.BinaryLinear
open scoped Matrix BigOperators Classical

theorem trace_rankOne {m n : Nat} (c : Vector n) (τ : Vector m)
    (S : Matrix (Fin m) (Fin n) F2) :
    Matrix.trace (Matrix.vecMulVec c τ * S) = τ ⬝ᵥ (S *ᵥ c) := by
  rw [Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, dotProduct_comm,
    ← Matrix.dotProduct_mulVec]

def MatrixValid {m n : Nat} (τ : Vector m) (S : Matrix (Fin m) (Fin n) F2) : Prop :=
  τ ᵥ* S ≠ 0

theorem matrixValid_iff_exists {m n : Nat} (τ : Vector m)
    (S : Matrix (Fin m) (Fin n) F2) :
    MatrixValid τ S ↔ ∃ c : Vector n, τ ⬝ᵥ (S *ᵥ c) = 1 := by
  constructor
  · intro h
    have he : ∃ i, (τ ᵥ* S) i ≠ 0 := by
      by_contra he
      apply h
      funext i
      by_contra hi
      exact he ⟨i, hi⟩
    obtain ⟨i, hi⟩ := he
    have hone : (τ ᵥ* S) i = 1 := (scalar_cases _).resolve_left hi
    exact ⟨Pi.single i 1, by rw [Matrix.dotProduct_mulVec, dotProduct_single_one, hone]⟩
  · rintro ⟨c, hc⟩ hzero
    rw [Matrix.dotProduct_mulVec, hzero] at hc
    simp at hc

theorem exists_matrixValid {m n : Nat} (τ : Vector m) (hτ : τ ≠ 0) (hn : 0 < n) :
    ∃ S : Matrix (Fin m) (Fin n) F2, MatrixValid τ S := by
  classical
  have he : ∃ i, τ i ≠ 0 := by
    by_contra he
    apply hτ
    funext i
    by_contra hi
    exact he ⟨i, hi⟩
  obtain ⟨i, hi⟩ := he
  have hone : τ i = 1 := (scalar_cases _).resolve_left hi
  let j : Fin n := ⟨0, hn⟩
  refine ⟨Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1), ?_⟩
  unfold MatrixValid
  rw [Matrix.vecMul_vecMulVec, dotProduct_single_one, hone, one_smul]
  intro hz
  have := congrFun hz j
  simp at this

theorem comp_ne_zero_iff_exists {E C : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup C] [Module F2 C]
    (τ : E →ₗ[F2] F2) (T : C →ₗ[F2] E) :
    τ.comp T ≠ 0 ↔ ∃ c, τ (T c) = 1 := by
  constructor
  · intro h
    have he : ∃ c, τ (T c) ≠ 0 := by
      by_contra he
      apply h
      ext c
      by_contra hc
      exact he ⟨c, hc⟩
    obtain ⟨c, hc⟩ := he
    exact ⟨c, (scalar_cases _).resolve_left hc⟩
  · rintro ⟨c, hc⟩ hz
    have hv := LinearMap.congr_fun hz c
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hc] at hv
    exact one_ne_zero hv

section LinearMaps

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

def Valid (τ : E →ₗ[F2] F2) (S : C →ₗ[F2] E) : Prop := τ.comp S ≠ 0

theorem valid_iff_exists (τ : E →ₗ[F2] F2) (S : C →ₗ[F2] E) :
    Valid τ S ↔ ∃ c, τ (S c) = 1 := comp_ne_zero_iff_exists τ S

theorem exists_valid [Nontrivial C] (τ : E →ₗ[F2] F2) (hτ : τ ≠ 0) :
    ∃ S : C →ₗ[F2] E, Valid τ S := by
  classical
  have he : ∃ e, τ e ≠ 0 := by
    by_contra he
    apply hτ
    ext e
    by_contra he'
    exact he ⟨e, he'⟩
  obtain ⟨e, he⟩ := he
  obtain ⟨c, hc⟩ := exists_ne (0 : C)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F2 hc
  refine ⟨φ.smulRight e, (valid_iff_exists τ _).mpr ⟨c, ?_⟩⟩
  rw [LinearMap.smulRight_apply, hφ, one_smul]
  exact (scalar_cases _).resolve_left he

theorem trace_smulRight_comp [FiniteDimensional F2 C]
    (τ : E →ₗ[F2] F2) (c : C) (S : C →ₗ[F2] E) :
    LinearMap.trace F2 C ((τ.smulRight c).comp S) = τ (S c) := by
  have heq : (τ.smulRight c).comp S = (τ.comp S).smulRight c := by
    ext x
    rfl
  rw [heq, LinearMap.trace_smulRight, LinearMap.comp_apply]

theorem card_linearMaps [FiniteDimensional F2 E] [FiniteDimensional F2 C]
    [Fintype (C →ₗ[F2] E)] :
    Fintype.card (C →ₗ[F2] E) =
      2 ^ (Module.finrank F2 C * Module.finrank F2 E) := by
  classical
  let bC := Module.finBasis F2 C
  let bE := Module.finBasis F2 E
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (LinearMap.toMatrix bC bE).toEquiv]
  change Nat.card (Fin (Module.finrank F2 E) → Fin (Module.finrank F2 C) → F2) = _
  rw [Nat.card_fun, Nat.card_fun]
  simp [F2, Integration.BinaryLinear.F2, Nat.card_eq_fintype_card, ← pow_mul,
    Nat.mul_comm]

theorem card_linearMaps_le [FiniteDimensional F2 E] [FiniteDimensional F2 C]
    [Fintype (C →ₗ[F2] E)] (r s : Nat)
    (hE : Module.finrank F2 E ≤ r) (hC : Module.finrank F2 C ≤ s) :
    Fintype.card (C →ₗ[F2] E) ≤ 2 ^ (r * s) := by
  rw [card_linearMaps]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  calc
    Module.finrank F2 C * Module.finrank F2 E ≤ s * r := Nat.mul_le_mul hC hE
    _ = r * s := Nat.mul_comm s r

end LinearMaps

section Folding

variable {E C D : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C] [Fintype C]
  [AddCommGroup D] [Module F2 D]

theorem folded_indicator_sum_le_one (τ : E →ₗ[F2] F2)
    (inclusion : C →ₗ[F2] D) (inclusion_injective : Function.Injective inclusion)
    (F : (E →ₗ[F2] C) → D)
    (folded : ∀ X c, F (X + τ.smulRight c) = F X + inclusion c)
    (X : E →ₗ[F2] C) (y : D) :
    (∑ c : C, if F (X + τ.smulRight c) = y then (1 : ℝ) else 0) ≤ 1 := by
  classical
  let hits : Finset C := Finset.univ.filter fun c => F (X + τ.smulRight c) = y
  have hcard : hits.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' : F (X + τ.smulRight a) = y := (Finset.mem_filter.mp ha).2
    have hb' : F (X + τ.smulRight b) = y := (Finset.mem_filter.mp hb).2
    apply inclusion_injective
    apply add_left_cancel (a := F X)
    simpa only [folded] using ha'.trans hb'.symm
  have hsum : (∑ c : C, if F (X + τ.smulRight c) = y then (1 : ℝ) else 0) =
      (hits.card : ℝ) := by
    simp only [hits, Finset.sum_boole]
  rw [hsum]
  exact_mod_cast hcard

theorem folded_indicator_average_le (τ : E →ₗ[F2] F2)
    (inclusion : C →ₗ[F2] D) (inclusion_injective : Function.Injective inclusion)
    (F : (E →ₗ[F2] C) → D)
    (folded : ∀ X c, F (X + τ.smulRight c) = F X + inclusion c)
    (X : E →ₗ[F2] C) (y : D) :
    (∑ c : C, if F (X + τ.smulRight c) = y then (1 : ℝ) else 0) /
        Fintype.card C ≤ 1 / (Fintype.card C : ℝ) := by
  exact div_le_div_of_nonneg_right
    (folded_indicator_sum_le_one τ inclusion inclusion_injective F folded X y)
    (Nat.cast_nonneg _)

end Folding

open MatrixCharacters hiding F2

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

def parityCharacter (τ : E →ₗ[F2] F2) (S : C →ₗ[F2] E) : AddChar C ℂ where
  toFun c := binarySign (τ (S c))
  map_zero_eq_one' := by simp
  map_add_eq_mul' c d := by simp only [map_add, binarySign_add]

theorem parityCharacter_eq_zero_iff (τ : E →ₗ[F2] F2) (S : C →ₗ[F2] E) :
    parityCharacter τ S = 0 ↔ τ.comp S = 0 := by
  constructor
  · intro h
    ext c
    apply binarySign_injective
    have hc := congrArg (fun ψ : AddChar C ℂ => ψ c) h
    simpa [parityCharacter] using hc
  · intro h
    ext c
    have hc := LinearMap.congr_fun h c
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hc
    simp [parityCharacter, hc]

theorem linearTrace_shift_sum [Fintype C] [FiniteDimensional F2 C]
    (τ : E →ₗ[F2] F2) (S : C →ₗ[F2] E) :
    (∑ c : C, linearTraceCharacter S (τ.smulRight c)) =
      if τ.comp S = 0 then (Fintype.card C : ℂ) else 0 := by
  classical
  simp only [linearTraceCharacter_apply, linearTracePair, trace_smulRight_comp]
  change (∑ c : C, parityCharacter τ S c) = _
  rw [AddChar.sum_eq_ite]
  simp only [parityCharacter_eq_zero_iff]

theorem linearTrace_shift_average [Fintype C] [FiniteDimensional F2 C]
    (τ : E →ₗ[F2] F2) (S : C →ₗ[F2] E) :
    (∑ c : C, linearTraceCharacter S (τ.smulRight c)) / (Fintype.card C : ℂ) =
      if τ.comp S = 0 then 1 else 0 := by
  classical
  rw [linearTrace_shift_sum]
  split <;> simp [Fintype.card_ne_zero]

end DFVSGames.Fourier.MatrixParity
end

noncomputable section

namespace DFVSGames.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open DFVSGames.Fourier.MatrixCharacters

section FiniteGroup

variable {G : Type*} [AddCommGroup G] [Fintype G]

def fourierCoeff (f : G → ℂ) (ψ : AddChar G ℂ) : ℂ :=
  𝔼 x, f x * star (ψ x)

theorem fourierCoeff_sum {J : Type*} (s : Finset J) (f : J → G → ℂ)
    (ψ : AddChar G ℂ) :
    fourierCoeff (∑ j ∈ s, f j) ψ = ∑ j ∈ s, fourierCoeff (f j) ψ := by
  simp only [fourierCoeff, Finset.sum_apply, Finset.sum_mul]
  exact Finset.expect_sum_comm _ _ _

theorem fourierCoeff_smul (c : ℂ) (f : G → ℂ) (ψ : AddChar G ℂ) :
    fourierCoeff (c • f) ψ = c * fourierCoeff f ψ := by
  simp only [fourierCoeff, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact Finset.mul_expect _ _ _ |>.symm

omit [AddCommGroup G] in
theorem star_expect (f : G → ℂ) :
    star (𝔼 x, f x) = 𝔼 x, star (f x) := by
  simp [Fintype.expect_eq_sum_div_card]

theorem star_fourierCoeff (f : G → ℂ) (ψ : AddChar G ℂ) :
    star (fourierCoeff f ψ) = 𝔼 x, star (f x) * ψ x := by
  rw [fourierCoeff, star_expect]
  simp [star_mul, mul_comm]

end FiniteGroup

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def linearCoeff (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) : ℝ :=
  𝔼 X, f X * (linearTraceCharacter S X).re

theorem card_linearMap_reverse :
    Fintype.card (F →ₗ[F2] E) = Fintype.card (E →ₗ[F2] F) := by
  classical
  let bE := Module.finBasis F2 E
  let bF := Module.finBasis F2 F
  calc
    Fintype.card (F →ₗ[F2] E) =
        Fintype.card (Matrix (Fin (Module.finrank F2 E))
          (Fin (Module.finrank F2 F)) F2) :=
      Fintype.card_congr (LinearMap.toMatrix bF bE).toEquiv
    _ = Fintype.card (Matrix (Fin (Module.finrank F2 F))
          (Fin (Module.finrank F2 E)) F2) := by
      exact Fintype.card_congr
        { toFun := Matrix.transpose
          invFun := Matrix.transpose
          left_inv := Matrix.transpose_transpose
          right_inv := Matrix.transpose_transpose }
    _ = Fintype.card (E →ₗ[F2] F) :=
      (Fintype.card_congr (LinearMap.toMatrix bE bF).toEquiv).symm

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearTraceCharacter_star (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    star (linearTraceCharacter S X) = linearTraceCharacter S X := by
  calc
    _ = star (((linearTraceCharacter S X).re : ℝ) : ℂ) :=
      congrArg star (linearTraceCharacter_real S X).symm
    _ = ((linearTraceCharacter S X).re : ℂ) := by simp
    _ = linearTraceCharacter S X := linearTraceCharacter_real S X

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearMap_add_eq_zero_iff (X Y : E →ₗ[F2] F) :
    X + Y = 0 ↔ X = Y := by
  have htwo : (1 + 1 : F2) = 0 := by decide
  have hself : Y + Y = 0 := by
    have h := congrArg (fun c : F2 => c • Y) htwo
    simpa only [add_smul, one_smul, zero_smul] using h
  have hneg : -Y = Y := neg_eq_iff_add_eq_zero.mpr hself
  rw [add_eq_zero_iff_eq_neg, hneg]

theorem linear_character_kernel (X Y : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, star (linearTraceCharacter S X) * linearTraceCharacter S Y =
      if X = Y then (Fintype.card (E →ₗ[F2] F) : ℂ) else 0 := by
  classical
  calc
    _ = ∑ S : F →ₗ[F2] E, linearTraceCharacter S (X + Y) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [linearTraceCharacter_star, AddChar.map_add_eq_mul]
    _ = ∑ S : F →ₗ[F2] E, linearTraceCharacter (X + Y) S := by
      apply Finset.sum_congr rfl
      intro S _
      exact linearTraceCharacter_swap S (X + Y)
    _ = if X + Y = 0 then (Fintype.card (F →ₗ[F2] E) : ℂ) else 0 :=
      sum_linearTraceCharacter (X + Y)
    _ = _ := by rw [linearMap_add_eq_zero_iff, card_linearMap_reverse]

omit [Fintype (F →ₗ[F2] E)] in
theorem linear_complexCoeff_character (S T : F →ₗ[F2] E) :
    fourierCoeff (linearTraceCharacter S : (E →ₗ[F2] F) → ℂ)
      (linearTraceCharacter T) = if T = S then 1 else 0 := by
  classical
  simp only [fourierCoeff, linearTraceCharacter_star, ← AddChar.add_apply,
    ← linearTraceCharacter_add, Fintype.expect_eq_sum_div_card,
    sum_linearTraceCharacter, linearMap_add_eq_zero_iff]
  by_cases h : S = T
  · subst T
    simp
  · simp [h, Ne.symm h]

theorem linear_complex_inversion (f : (E →ₗ[F2] F) → ℂ) (Y : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, fourierCoeff f (linearTraceCharacter S) *
      linearTraceCharacter S Y = f Y := by
  classical
  simp only [fourierCoeff]
  simp_rw [Finset.expect_mul, mul_assoc]
  rw [← Finset.expect_sum_comm]
  simp_rw [← Finset.mul_sum, linear_character_kernel]
  rw [Finset.expect_eq_sum_div_card]
  simp [mul_ite]

theorem linear_complex_parseval (f g : (E →ₗ[F2] F) → ℂ) :
    ∑ S : F →ₗ[F2] E, star (fourierCoeff f (linearTraceCharacter S)) *
      fourierCoeff g (linearTraceCharacter S) = 𝔼 X, star (f X) * g X := by
  simp_rw [star_fourierCoeff, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro X _
  calc
    (∑ S : F →ₗ[F2] E, (star (f X) * linearTraceCharacter S X) *
        fourierCoeff g (linearTraceCharacter S)) =
        star (f X) * ∑ S : F →ₗ[F2] E,
          fourierCoeff g (linearTraceCharacter S) * linearTraceCharacter S X := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ac_rfl
    _ = star (f X) * g X := by rw [linear_complex_inversion]

theorem complex_ofReal_expect {J : Type*} [Fintype J] (f : J → ℝ) :
    ((𝔼 j, f j : ℝ) : ℂ) = 𝔼 j, (f j : ℂ) := by
  simp only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_natCast]
  congr 1
  exact map_sum Complex.ofRealHom f Finset.univ

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_complex (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    (linearCoeff f S : ℂ) =
      fourierCoeff (fun X => (f X : ℂ)) (linearTraceCharacter S) := by
  rw [linearCoeff, complex_ofReal_expect, fourierCoeff]
  apply Finset.expect_congr rfl
  intro X _
  rw [Complex.ofReal_mul, linearTraceCharacter_real, linearTraceCharacter_star]

theorem linear_parseval_inner (f g : (E →ₗ[F2] F) → ℝ) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S =
      𝔼 X, f X * g X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          star (fourierCoeff (fun X => (f X : ℂ)) (linearTraceCharacter S)) *
            fourierCoeff (fun X => (g X : ℂ)) (linearTraceCharacter S) := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [← linearCoeff_complex, ← linearCoeff_complex]
      simp
    _ = 𝔼 X, star (f X : ℂ) * (g X : ℂ) := linear_complex_parseval _ _
    _ = ((𝔼 X, f X * g X : ℝ) : ℂ) := by
      rw [complex_ofReal_expect]
      simp

theorem linear_parseval (f : (E →ₗ[F2] F) → ℝ) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S ^ 2 = 𝔼 X, f X ^ 2 := by
  simpa only [pow_two] using linear_parseval_inner f f

theorem linear_fourier_inversion (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re = f X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          fourierCoeff (fun Y => (f Y : ℂ)) (linearTraceCharacter S) *
            linearTraceCharacter S X := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E,
        linearCoeff f S * (linearTraceCharacter S X).re) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      change ((linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) = _
      rw [Complex.ofReal_mul, linearCoeff_complex, linearTraceCharacter_real]
    _ = (f X : ℂ) := linear_complex_inversion _ X

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_sum {J : Type*} (s : Finset J)
    (f : J → (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (∑ j ∈ s, f j) S = ∑ j ∈ s, linearCoeff (f j) S := by
  simp only [linearCoeff, Finset.sum_apply, Finset.sum_mul]
  exact Finset.expect_sum_comm _ _ _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_smul (c : ℝ) (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (c • f) S = c * linearCoeff f S := by
  simp only [linearCoeff, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact Finset.mul_expect _ _ _ |>.symm

omit [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_character (S T : F →ₗ[F2] E) :
    linearCoeff (fun X => (linearTraceCharacter S X).re) T =
      if T = S then 1 else 0 := by
  classical
  apply Complex.ofReal_injective
  rw [linearCoeff_complex]
  simp only [linearTraceCharacter_real, linear_complexCoeff_character]
  split_ifs <;> simp

end DFVSGames.Fourier.MatrixFourier
end

end OAI
