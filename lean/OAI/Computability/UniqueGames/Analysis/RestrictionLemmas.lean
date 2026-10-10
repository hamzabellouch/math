import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Std
import OAI.Computability.UniqueGames.Analysis.A13IndexLemmas
import OAI.Computability.UniqueGames.Analysis.AntecedentCountLemmas
import OAI.Computability.UniqueGames.Analysis.BadConvolution
import OAI.Computability.UniqueGames.Analysis.FiberEnergyLemmas
import OAI.Computability.UniqueGames.Analysis.Identities
import OAI.Computability.UniqueGames.Analysis.MatrixCharactersLemmas
import OAI.Computability.UniqueGames.Analysis.MatrixNoiseLemmas
import OAI.Computability.UniqueGames.Analysis.MatrixRestrictions
import OAI.Computability.UniqueGames.Analysis.WeightedFourthMoment

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.Restriction

def isum {α : Type} : List α → (α → Int) → Int
  | [], _ => 0
  | a :: as, f => f a + isum as f

theorem isum_congr {α : Type} (as : List α) (f g : α → Int)
    (h : ∀ a, f a = g a) : isum as f = isum as g := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [isum, h, ih]

theorem isum_zero {α : Type} (as : List α) : isum as (fun _ => 0) = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [isum, ih, Int.zero_add]

theorem isum_add {α : Type} (as : List α) (f g : α → Int) :
    isum as (fun a => f a + g a) = isum as f + isum as g := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [isum, ih]; omega

theorem isum_mul_left {α : Type} (as : List α) (c : Int) (f : α → Int) :
    isum as (fun a => c * f a) = c * isum as f := by
  induction as with
  | nil => simp only [isum, Int.mul_zero]
  | cons a as ih => simp only [isum, ih, Int.mul_add]

theorem isum_mul_right {α : Type} (as : List α) (f : α → Int) (c : Int) :
    isum as (fun a => f a * c) = isum as f * c := by
  induction as with
  | nil => simp only [isum, Int.zero_mul]
  | cons a as ih => simp only [isum, ih, Int.add_mul]

theorem isum_const {α : Type} (as : List α) (c : Int) :
    isum as (fun _ => c) = (as.length : Int) * c := by
  induction as with
  | nil => simp only [isum, List.length_nil, Int.natCast_zero, Int.zero_mul]
  | cons a as ih =>
    simp only [isum, ih, List.length_cons, Int.natCast_add, Int.natCast_one,
      Int.add_mul, Int.one_mul]
    omega

theorem isum_swap {α β : Type} (as : List α) (bs : List β) (f : α → β → Int) :
    isum as (fun a => isum bs (f a)) = isum bs (fun b => isum as (fun a => f a b)) := by
  induction as with
  | nil => simp only [isum, isum_zero]
  | cons a as ih => simp only [isum, isum_add, ih]

theorem isum_map {α β : Type} (as : List α) (g : α → β) (f : β → Int) :
    isum (as.map g) f = isum as (fun a => f (g a)) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, isum, ih]

theorem isum_perm {α : Type} {as bs : List α} (h : as.Perm bs) (f : α → Int) :
    isum as f = isum bs f := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [isum, ih]
  | swap a b as => simp only [isum]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The binary character is multiplicative across addition of its exponents. -/
def binarySign (b : Bool) : Int := if b then -1 else 1

theorem binarySign_xor (a b : Bool) :
    binarySign (a.xor b) = binarySign a * binarySign b := by
  cases a <;> cases b <;> decide

/-- The character part of (A.1), given the trace-pairing compatibility equation.
`traceCompatibility` states the actual mathematical hypothesis still required
when instantiating this result with binary matrix spaces and quotient maps. -/
theorem binary_character_restriction {M N Y Z : Type}
    (translate : M → N → M) (compress : Y → Z)
    (ambientPair : Y → M → Bool) (restrictedPair : Z → N → Bool)
    (traceCompatibility : ∀ y t n,
      ambientPair y (translate t n) = (ambientPair y t).xor (restrictedPair (compress y) n))
    (y : Y) (t : M) (n : N) :
    binarySign (ambientPair y (translate t n)) =
      binarySign (ambientPair y t) * binarySign (restrictedPair (compress y) n) := by
  rw [traceCompatibility, binarySign_xor]

/-- Raw coefficient form of frequency merging in (A.1).

When `f` is synthesized as `sum_y coeff(y) * ambient(y, t+n)`, the raw
restricted coefficient at `z` is the cardinality of the restricted domain
times the sum of translated coefficients with `compress y = z`. Normalized
coefficients divide the displayed equation by that cardinality.
-/
theorem coefficient_merging {M N Y Z : Type} [DecidableEq Z]
    (ys : List Y) (ns : List N) (translate : M → N → M) (compress : Y → Z)
    (ambient : Y → M → Int) (restricted : Z → N → Int) (coeff : Y → Int)
    (compatibility : ∀ y t n,
      ambient y (translate t n) = ambient y t * restricted (compress y) n)
    (orthogonality : ∀ y z,
      isum ns (fun n => restricted (compress y) n * restricted z n) =
        if compress y = z then (ns.length : Int) else 0)
    (t : M) (z : Z) :
    isum ns (fun n =>
      isum ys (fun y => coeff y * ambient y (translate t n)) * restricted z n) =
    (ns.length : Int) *
      isum ys (fun y => if compress y = z then coeff y * ambient y t else 0) := by
  calc
    _ = isum ns (fun n => isum ys (fun y =>
        (coeff y * ambient y t) *
          (restricted (compress y) n * restricted z n))) := by
      apply isum_congr
      intro n
      rw [← isum_mul_right]
      apply isum_congr
      intro y
      rw [compatibility]
      simp only [Int.mul_assoc]
    _ = isum ys (fun y => isum ns (fun n =>
        (coeff y * ambient y t) *
          (restricted (compress y) n * restricted z n))) := isum_swap ns ys _
    _ = isum ys (fun y => (coeff y * ambient y t) *
        (if compress y = z then (ns.length : Int) else 0)) := by
      apply isum_congr
      intro y
      rw [isum_mul_left, orthogonality]
    _ = isum ys (fun y => (ns.length : Int) *
        (if compress y = z then coeff y * ambient y t else 0)) := by
      apply isum_congr
      intro y
      split <;> simp_all only [Int.mul_comm, Int.mul_zero]
    _ = _ := isum_mul_left ys _ _

/-- The raw finite-sum translation identity behind (A.2).

For every fixed restriction point `n`, translation permutes the ambient list.
Consequently summing an arbitrary integer observable over all translates and
restriction points multiplies its ambient sum by the restriction-domain size.
One may use an integer-valued moment as the observable.
-/
theorem restriction_average {M N : Type}
    (ms : List M) (ns : List N) (translate : M → N → M)
    (translationPermutes : ∀ n, (ms.map (fun t => translate t n)).Perm ms)
    (observable : M → Int) :
    isum ms (fun t => isum ns (fun n => observable (translate t n))) =
      (ns.length : Int) * isum ms observable := by
  rw [isum_swap]
  calc
    _ = isum ns (fun _ => isum ms observable) := by
      apply isum_congr
      intro n
      rw [← isum_map]
      exact isum_perm (translationPermutes n) observable
    _ = _ := isum_const ns _

/-- Concrete translation-permutation verification for the one-bit space. -/
theorem bool_translation_perm (n : Bool) :
    ([false, true].map (fun t => t.xor n)).Perm [false, true] := by
  cases n
  · exact List.Perm.refl _
  · exact List.Perm.swap false true []

/-- Fully instantiated one-bit averaging, with any list of restriction points. -/
theorem bool_restriction_average (ns : List Bool) (observable : Bool → Int) :
    isum [false, true] (fun t => isum ns (fun n => observable (t.xor n))) =
      (ns.length : Int) * isum [false, true] observable :=
  restriction_average [false, true] ns Bool.xor bool_translation_perm observable

/-- Character compatibility instantiated on the binary one-dimensional space. -/
theorem bool_character_compatibility (y t n : Bool) :
    binarySign (y && (t.xor n)) = binarySign (y && t) * binarySign (y && n) := by
  cases y <;> cases t <;> cases n <;> decide

/-- Fourier orthogonality instantiated on the binary one-dimensional space. -/
theorem bool_character_orthogonality (y z : Bool) :
    isum [false, true] (fun n => binarySign (y && n) * binarySign (z && n)) =
      if y = z then (2 : Int) else 0 := by
  cases y <;> cases z <;> decide

/-- A complete instance of the coefficient theorem with no character hypotheses. -/
theorem bool_coefficient_merging (coeff : Bool → Int) (t z : Bool) :
    isum [false, true] (fun n =>
      isum [false, true] (fun y => coeff y * binarySign (y && (t.xor n))) *
        binarySign (z && n)) =
      2 * (coeff z * binarySign (z && t)) := by
  have h := coefficient_merging [false, true] [false, true] Bool.xor id
    (fun y t => binarySign (y && t)) (fun y n => binarySign (y && n))
    coeff bool_character_compatibility bool_character_orthogonality t z
  cases z <;> simpa [isum] using h

end UniqueGamesTheorem.Appendix.Restriction

noncomputable section

namespace UniqueGamesTheorem.Appendix.Restriction

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

/-- Averaging any real observable over translates of any finite parametrized
perturbation preserves its normalized mean. -/
theorem real_translation_average {G N : Type*} [AddCommGroup G] [Fintype G]
    [Fintype N] [Nonempty N] (embed : N → G) (observable : G → ℝ) :
    (𝔼 t, 𝔼 n, observable (t + embed n)) = 𝔼 t, observable t := by
  rw [Finset.expect_comm]
  calc
    _ = 𝔼 _n : N, 𝔼 t, observable t := by
      apply Finset.expect_congr rfl
      intro n _
      exact Fintype.expect_equiv (Equiv.addRight (embed n)) _ _ (fun _ => rfl)
    _ = _ := Finset.expect_const Finset.univ_nonempty _

section ActualRestrictions

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

/-- The actual quotient-and-restriction map on Fourier indices in (A.1). -/
def compressFrequency (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) : B →ₗ[F2] (E ⧸ A) :=
  A.mkQ.comp (Y.comp B.subtype)

omit [FiniteDimensional F2 E] in
/-- Trace compatibility on the actual quotient restriction. -/
theorem linear_trace_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    linearTracePair (UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) Y =
      linearTracePair N (compressFrequency A B Y) := by
  unfold linearTracePair UniqueGamesTheorem.Fourier.MatrixRestrictions.embed compressFrequency
  simp only [LinearMap.comp_assoc]
  rw [LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_assoc]

omit [FiniteDimensional F2 E] in
/-- The complex character identity in (A.1), on actual binary linear maps. -/
theorem linear_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    linearTraceCharacter Y (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) =
      linearTraceCharacter Y T * linearTraceCharacter (compressFrequency A B Y) N := by
  simp only [linearTraceCharacter_apply, linearTracePair_add_left,
    linear_trace_restriction, UniqueGamesTheorem.Fourier.MatrixCharacters.binarySign_add]

omit [FiniteDimensional F2 E] in
theorem real_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    (linearTraceCharacter Y (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N)).re =
      (linearTraceCharacter Y T).re * (linearTraceCharacter (compressFrequency A B Y) N).re := by
  rw [linear_character_restriction, Complex.mul_re]
  simp only [linearTraceCharacter_apply,
    UniqueGamesTheorem.Fourier.MatrixCharacters.binarySign_im, mul_zero, sub_zero]

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem linear_restriction_average (A : Submodule F2 E) (B : Submodule F2 F)
    (h : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, 𝔼 N, UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict h A B T N) = 𝔼 T, h T :=
  real_translation_average (UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B) h

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
/-- The `p`th-moment form of (A.2). In fact the averaging identity holds for
every real exponent, whenever the observable is interpreted by real powers. -/
theorem linear_restriction_moment_average (A : Submodule F2 E) (B : Submodule F2 F)
    (h : (E →ₗ[F2] F) → ℝ) (p : ℝ) :
    (𝔼 T, 𝔼 N, |UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict h A B T N| ^ p) =
      𝔼 T, |h T| ^ p :=
  real_translation_average (UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B)
    (fun T => |h T| ^ p)

variable [Fintype (F →ₗ[F2] E)]

theorem linear_coefficient_merging (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (Z : B →ₗ[F2] (E ⧸ A)) :
    linearCoeff (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) Z =
      ∑ Y : F →ₗ[F2] E,
        if compressFrequency A B Y = Z then linearCoeff f Y * (linearTraceCharacter Y T).re
        else 0 := by
  classical
  have hexpansion : UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T =
      ∑ Y : F →ₗ[F2] E,
        (linearCoeff f Y * (linearTraceCharacter Y T).re) •
          (fun N => (linearTraceCharacter (compressFrequency A B Y) N).re) := by
    funext N
    change f (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) = _
    rw [← linear_fourier_inversion f (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro Y _
    rw [real_character_restriction]
    ring
  rw [hexpansion, linearCoeff_sum]
  apply Finset.sum_congr rfl
  intro Y _
  rw [linearCoeff_smul, linearCoeff_character]
  by_cases h : compressFrequency A B Y = Z
  · simp [h]
  · simp [h, Ne.symm h]

end ActualRestrictions

end UniqueGamesTheorem.Appendix.Restriction

end

end

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.Derivatives
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Actual normalized Fourier projector onto the indices satisfying `P`. -/
def spectralProjector (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F) → ℝ :=
  ∑ Y with P Y, linearCoeff f Y • (fun X => (linearTraceCharacter Y X).re)

theorem linearCoeff_spectralProjector (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (Y : F →ₗ[F2] E) :
    linearCoeff (spectralProjector P f) Y = if P Y then linearCoeff f Y else 0 := by
  classical
  unfold spectralProjector
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

theorem spectralProjector_energy (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, spectralProjector P f X ^ 2) = ∑ Y with P Y, linearCoeff f Y ^ 2 := by
  classical
  rw [← linear_parseval, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Y _
  rw [linearCoeff_spectralProjector]
  split_ifs <;> simp

theorem spectralProjector_energy_le (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, spectralProjector P f X ^ 2) ≤ 𝔼 X, f X ^ 2 := by
  classical
  rw [spectralProjector_energy, ← linear_parseval]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun Y _ _ => sq_nonneg _)

theorem function_eq_of_linearCoeff_eq {f g : (E →ₗ[F2] F) → ℝ}
    (h : ∀ Y, linearCoeff f Y = linearCoeff g Y) : f = g := by
  funext M
  rw [← linear_fourier_inversion f M, ← linear_fourier_inversion g M]
  apply Finset.sum_congr rfl
  intro Y _
  rw [h Y]

theorem spectralProjector_comp (P Q : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector P (spectralProjector Q f) =
      spectralProjector (fun Y => P Y ∧ Q Y) f := by
  classical
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [linearCoeff_spectralProjector]
  by_cases hP : P Y <;> by_cases hQ : Q Y <;> simp [hP, hQ]

def hybridProjector (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  spectralProjector (fun Y => LinearIdentities.Hybrid Y A B) f

def hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) :
    UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B → ℝ :=
  UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict (hybridProjector A B f) A B T

def rankProjector (X : F →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F) → ℝ :=
  spectralProjector (fun Y => RankAdditivity.RankBelow X Y) f

def mapDerivative (X : F →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter X.range X.ker → ℝ :=
  UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict (rankProjector X f) X.range X.ker 0

theorem rankProjector_energy (X : F →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, rankProjector X f M ^ 2) =
      ∑ Y, if RankAdditivity.RankBelow X Y then linearCoeff f Y ^ 2 else 0 := by
  classical
  unfold rankProjector
  rw [spectralProjector_energy, Finset.sum_filter]

def selectorMultiplicity {I : Type*} [Fintype I]
    (P : I → (F →ₗ[F2] E) → Prop) (Y : F →ₗ[F2] E) : ℕ :=
  (Finset.univ.filter (fun i : I => P i Y)).card

theorem selector_energy_sum {I : Type*} [Fintype I]
    (P : I → (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) :
    (∑ i : I, 𝔼 X, spectralProjector (P i) f X ^ 2) =
      ∑ Y : F →ₗ[F2] E, (selectorMultiplicity P Y : ℝ) * linearCoeff f Y ^ 2 := by
  classical
  simp_rw [spectralProjector_energy, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Y _
  calc
    (∑ i : I, if P i Y then linearCoeff f Y ^ 2 else 0) =
        ∑ i : I with P i Y, linearCoeff f Y ^ 2 := by rw [Finset.sum_filter]
    _ = _ := by simp [selectorMultiplicity]

theorem selector_energy_sum_le {I : Type*} [Fintype I]
    (P : I → (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) (M : ℝ)
    (hcount : ∀ Y : F →ₗ[F2] E, linearCoeff f Y ≠ 0 →
      (selectorMultiplicity P Y : ℝ) ≤ M) :
    (∑ i : I, 𝔼 X, spectralProjector (P i) f X ^ 2) ≤ M * (𝔼 X, f X ^ 2) := by
  classical
  rw [selector_energy_sum, ← linear_parseval, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Y _
  by_cases hY : linearCoeff f Y = 0
  · simp [hY]
  · exact mul_le_mul_of_nonneg_right (hcount Y hY) (sq_nonneg _)

variable [Finite E] [Finite F]

theorem linearCoeff_mapDerivative (X : F →ₗ[F2] E)
    [Fintype (X.ker →ₗ[F2] (E ⧸ X.range))]
    (f : (E →ₗ[F2] F) → ℝ) (Z : X.ker →ₗ[F2] (E ⧸ X.range)) :
    linearCoeff (mapDerivative X f) Z =
      ∑ Y : F →ₗ[F2] E,
        if RankAdditivity.RankBelow X Y ∧
            Restriction.compressFrequency X.range X.ker Y = Z then linearCoeff f Y else 0 := by
  classical
  unfold mapDerivative
  rw [Restriction.linear_coefficient_merging]
  apply Finset.sum_congr rfl
  intro Y _
  simp only [rankProjector, linearCoeff_spectralProjector]
  have hp : (linearTraceCharacter Y (0 : E →ₗ[F2] F)).re = 1 := by simp
  rw [hp]
  by_cases hR : RankAdditivity.RankBelow X Y <;>
    by_cases hC : Restriction.compressFrequency X.range X.ker Y = Z <;> simp [hR, hC]

theorem mapDerivative_energy_eq_coefficients (X : F →ₗ[F2] E)
    [Fintype (X.ker →ₗ[F2] (E ⧸ X.range))]
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 N, mapDerivative X f N ^ 2) =
      ∑ Z : X.ker →ₗ[F2] (E ⧸ X.range),
        (∑ Y : F →ₗ[F2] E, if RankAdditivity.RankBelow X Y ∧
          Restriction.compressFrequency X.range X.ker Y = Z then linearCoeff f Y else 0) ^ 2 := by
  rw [← linear_parseval]
  simp_rw [linearCoeff_mapDerivative]

/-- A.10 on actual normalized derivative norms. -/
theorem mapDerivative_energy_le (X : F →ₗ[F2] E)
    [Fintype (X.ker →ₗ[F2] (E ⧸ X.range))]
    (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (𝔼 N, mapDerivative X f N ^ 2) ≤
      (2 : ℝ) ^ (2 * Module.finrank F2 X.range * (d - Module.finrank F2 X.range)) *
        (𝔼 M, rankProjector X f M ^ 2) := by
  rw [mapDerivative_energy_eq_coefficients, rankProjector_energy]
  have hh := DerivativeEnergy.coefficient_energy X (linearCoeff f) d hdegree
  simp only [Restriction.compressFrequency, FullCompression.compression] at hh ⊢
  convert hh using 1
  congr 1

/-- The coefficient-energy definition from the weighted estimate is exactly
the normalized squared norm of the actual map derivative. -/
theorem mapDerivative_energy_eq_weighted_energy (X : F →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 N, mapDerivative X f N ^ 2) = WeightedFourthMoment.energy (linearCoeff f) X := by
  let := WeightedFourthMoment.compressedFintype X
  rw [mapDerivative_energy_eq_coefficients]
  unfold WeightedFourthMoment.energy
  simp only [Restriction.compressFrequency, FullCompression.compression]
  congr 1

/-- The corrected weighted fourth-moment estimate for genuine derivative
norms, with the normalized primal measure and counting frequency measure. -/
theorem weighted_fourth_derivative_energy (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (∑ X : F →ₗ[F2] E, ((2 : ℝ)⁻¹) ^ (8 * d * Module.finrank F2 X.range) *
      (𝔼 N, mapDerivative X f N ^ 2) ^ 2) ≤ 2 * (𝔼 M, f M ^ 2) ^ 2 := by
  calc
    _ = ∑ X : F →ₗ[F2] E, ((2 : ℝ)⁻¹) ^ (8 * d * Module.finrank F2 X.range) *
        WeightedFourthMoment.energy (linearCoeff f) X ^ 2 := by
      apply Finset.sum_congr rfl
      intro X _
      rw [mapDerivative_energy_eq_weighted_energy]
    _ ≤ _ := by
      simpa only [linear_parseval] using
        WeightedFourthMoment.weighted_fourth_coefficient_energy (linearCoeff f) d hdegree

theorem spectralProjector_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop) (f : (E →ₗ[F2] F) → ℝ)
    (T : E →ₗ[F2] F) :
    spectralProjector Q (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) =
      UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict
        (spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f) A B T := by
  classical
  apply function_eq_of_linearCoeff_eq
  intro Z
  rw [linearCoeff_spectralProjector,
    Restriction.linear_coefficient_merging, Restriction.linear_coefficient_merging]
  by_cases hQ : Q Z
  · simp only [ite_eq_left hQ]
    apply Finset.sum_congr rfl
    intro Y _
    rw [linearCoeff_spectralProjector]
    by_cases hC : Restriction.compressFrequency A B Y = Z <;> simp [hC, hQ]
  · simp only [ite_eq_right hQ]
    symm
    apply Finset.sum_eq_zero
    intro Y _
    rw [linearCoeff_spectralProjector]
    by_cases hC : Restriction.compressFrequency A B Y = Z <;> simp [hC, hQ]

theorem spectralProjector_restriction_moment_average
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop) (f : (E →ₗ[F2] F) → ℝ)
    {N : Type*} [Fintype N] [Nonempty N]
    (θ : N → UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) (p : ℕ) :
    (𝔼 T, 𝔼 n, spectralProjector Q
      (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) (θ n) ^ p) =
      𝔼 M, spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f M ^ p := by
  simp_rw [spectralProjector_restriction]
  exact Restriction.real_translation_average
    (fun n => UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B (θ n))
    (fun M => spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f M ^ p)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem hybridDerivative_energy_average (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, 𝔼 N, hybridDerivative A B T f N ^ 2) =
      𝔼 X, hybridProjector A B f X ^ 2 :=
  Restriction.real_translation_average (UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B)
    (fun X => hybridProjector A B f X ^ 2)

def HybridIndex (d : ℕ) :=
  {p : Submodule F2 E × Submodule F2 F //
    UniqueGamesTheorem.Fourier.MatrixRestrictions.order p.1 p.2 ≤ d}

noncomputable instance hybridIndexFintype (d : ℕ) :
    Fintype (HybridIndex (E := E) (F := F) d) := by
  letI : Finite (Submodule F2 E) :=
    Finite.of_injective (fun A : Submodule F2 E => (A : Set E)) SetLike.coe_injective
  letI : Finite (Submodule F2 F) :=
    Finite.of_injective (fun B : Submodule F2 F => (B : Set F)) SetLike.coe_injective
  unfold HybridIndex
  exact Fintype.ofFinite _

def hybridMomentSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ s : HybridIndex (E := E) (F := F) d,
    𝔼 T, (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) ^ 2

def hybridSelectorEnergy (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ s : HybridIndex (E := E) (F := F) d,
    𝔼 X, hybridProjector s.val.1 s.val.2 f X ^ 2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem hybridMomentSum_le_of_uniform_energy (d : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (ζ : ℝ)
    (hζ : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
      UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B ≤ d →
        (𝔼 N, hybridDerivative A B T f N ^ 2) ≤ ζ) :
    hybridMomentSum d f ≤ ζ * hybridSelectorEnergy d f := by
  classical
  unfold hybridMomentSum hybridSelectorEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    (𝔼 T, (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) ^ 2) ≤
        𝔼 T, ζ * (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) := by
      apply Finset.expect_le_expect
      intro T _
      have hn : 0 ≤ 𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2 :=
        Finset.expect_nonneg (fun N _ => sq_nonneg _)
      simpa only [pow_two] using
        mul_le_mul_of_nonneg_right (hζ s.val.1 s.val.2 T s.property) hn
    _ = ζ * (𝔼 T, 𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) :=
      (Finset.mul_expect _ _ _).symm
    _ = ζ * (𝔼 X, hybridProjector s.val.1 s.val.2 f X ^ 2) := by
      rw [hybridDerivative_energy_average]

end UniqueGamesTheorem.Appendix.Derivatives

end

end

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.A1Reduction
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier UniqueGamesTheorem.Fourier.MatrixProducts
open UniqueGamesTheorem.Appendix.Derivatives
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

def weakFourthSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ p : Submodule F2 E × Submodule F2 F,
    if p ≠ (⊥, ⊤) then
      (2:ℝ)^(7*d*(Module.finrank F2 p.1 + Module.finrank F2 (F ⧸ p.2))) *
        (𝔼 M, spectralProjector (fun Y => p.1 ≤ Y.range ∧ Y.ker ≤ p.2) f M^4)
    else 0

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem weakFourthSum_nonneg (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    0 ≤ weakFourthSum d f := by
  apply Finset.sum_nonneg
  intro p _
  split
  · exact mul_nonneg (by positivity) (Finset.expect_nonneg (fun _ _ => by positivity))
  · exact le_rfl

omit [Finite E] [Finite F] [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
theorem linearCoeff_weakProjector (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) (Y : F →ₗ[F2] E) :
    linearCoeff (spectralProjector (fun Z => A ≤ Z.range ∧ Z.ker ≤ B) f) Y =
      BadConvolution.filteredCoefficient A B (linearCoeff f) Y := by
  simp only [linearCoeff_spectralProjector, BadConvolution.filteredCoefficient,
    BadConvolution.Incidence]
  rfl

omit [Finite E] [Finite F] [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
/-- Actual Parseval/product identity for each signed weakly selected piece. -/
theorem piece_fourth_moment (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) :
    (∑ X : F →ₗ[F2] E, BadConvolution.pieceConvolution A B (linearCoeff f) X^2) =
      𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M^4 := by
  rw [expect_fourth_eq_sum_convolution_sq]
  simp only [coefficientConvolution, BadConvolution.pieceConvolution,
    linearCoeff_weakProjector]

omit [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
theorem actual_bad_cover (X Y : F →ₗ[F2] E) (hbad : ¬ BadConvolution.Bad X Y) :
    F1Energy.Good X Y := by
  apply F1Energy.good_of_trivial_intersections X Y
  · by_contra hi
    exact hbad (Or.inl hi)
  · by_contra hk
    exact hbad (Or.inr hk)

omit [FiniteDimensional F2 E] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]
  [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
theorem badConvolution_zero_of_degree_zero (a : (F →ₗ[F2] E) → ℝ)
    (ha : ∀ Y, 0 < Module.finrank F2 Y.range → a Y = 0) (X : F →ₗ[F2] E) :
    BadConvolution.badConvolution a X = 0 := by
  classical
  unfold BadConvolution.badConvolution
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hY : Y = 0
  · subst Y
    by_cases hX : X = 0
    · subst X
      simp [BadConvolution.Bad]
    · have hz := ha X (DegreeZero.rank_pos_of_ne_zero X hX)
      simp [hz]
  · have hz := ha Y (DegreeZero.rank_pos_of_ne_zero Y hY)
    simp [hz]

theorem badConvolution_energy_le_weakFourthSum (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (∑ X : F →ₗ[F2] E, BadConvolution.badConvolution (linearCoeff f) X^2) ≤
      weakFourthSum d f := by
  by_cases hd : d = 0
  · subst d
    have hz : ∀ X, BadConvolution.badConvolution (linearCoeff f) X = 0 :=
      badConvolution_zero_of_degree_zero (linearCoeff f) hdegree
    simpa only [hz, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      Finset.sum_const_zero] using weakFourthSum_nonneg 0 f
  · have h := BadConvolution.badConvolution_sq_sum_le (linearCoeff f) d (by omega) hdegree
    simpa only [weakFourthSum, piece_fourth_moment] using h

theorem fourth_moment_le_two (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (𝔼 M, f M^4) ≤ 2 * ((2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2) +
      2 * weakFourthSum d f := by
  have hcore : (𝔼 M, f M^4) ≤ 2 * ((2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2) +
      2 * ∑ X : F →ₗ[F2] E, BadConvolution.badConvolution (linearCoeff f) X^2 := by
    simpa only [BadConvolution.badConvolution] using
      F1Energy.fourth_moment_le_good_bad f d hdegree BadConvolution.Bad actual_bad_cover
  exact hcore.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (badConvolution_energy_le_weakFourthSum f d hdegree) (show (0:ℝ) ≤ 2 by norm_num)))

/-- Lemma A.1, Equation (A.6), for every degree d including zero. -/
theorem degree_reduction (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (𝔼 M, f M^4) / 162 ≤ (2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2 + weakFourthSum d f := by
  have h := fourth_moment_le_two f d hdegree
  have ha : 0 ≤ (2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2 := by positivity
  have hb := weakFourthSum_nonneg d f
  apply (div_le_iff₀ (show (0:ℝ) < 162 by norm_num)).mpr
  nlinarith

end UniqueGamesTheorem.Appendix.A1Reduction

end

end

section

/-! Actual Fourier degree loss for both derivative operators. The support
cutoffs apply to genuine binary linear maps, including the case where the
total derivative order is larger than the original degree. -/

noncomputable section
namespace UniqueGamesTheorem.Appendix.DerivativeDegree

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Fourier support is restricted to maps of rank at most `d`. -/
def DegreeAtMost (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ Y, d < frequencyRank Y → linearCoeff f Y = 0

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem DegreeAtMost.mono {d e : ℕ} {f : (E →ₗ[F2] F) → ℝ}
    (hf : DegreeAtMost d f) (hde : d ≤ e) : DegreeAtMost e f := by
  intro Y hY
  exact hf Y (lt_of_le_of_lt hde hY)

theorem degree_rankLevel (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    DegreeAtMost d (LevelInequality.rankLevel d f) :=
  LevelInequality.rankLevel_degree_le d f

theorem degree_spectralProjector (P : (F →ₗ[F2] E) → Prop)
    {d : ℕ} {f : (E →ₗ[F2] F) → ℝ} (hf : DegreeAtMost d f) :
    DegreeAtMost d (spectralProjector P f) := by
  intro Y hY
  rw [linearCoeff_spectralProjector, hf Y hY]
  split_ifs <;> rfl

theorem eq_zero_of_linearCoeff_zero {f : (E →ₗ[F2] F) → ℝ}
    (hf : ∀ Y, linearCoeff f Y = 0) : f = 0 := by
  funext M
  rw [← linear_fourier_inversion f M]
  simp [hf]

variable [Finite E] [Finite F]

local instance quotientFinite (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective

local instance compressedDualFintype (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (B →ₗ[F2] (E ⧸ A)) := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype (E ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) => (L : B → E ⧸ A))
    DFunLike.coe_injective

theorem hybridDerivative_coeff_zero_of_lt (A : Submodule F2 E)
    (B : Submodule F2 F) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (Z : B →ₗ[F2] (E ⧸ A))
    (hZ : d < frequencyRank Z + order A B) :
    linearCoeff (hybridDerivative A B T f) Z = 0 := by
  unfold hybridDerivative
  rw [Restriction.linear_coefficient_merging]
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hc : Restriction.compressFrequency A B Y = Z
  · rw [ite_eq_left hc]
    unfold hybridProjector
    rw [linearCoeff_spectralProjector]
    by_cases hY : LinearIdentities.Hybrid Y A B
    · rw [ite_eq_left hY]
      have hr := Level.LinearRank.hybrid_rank_loss A B Y hY.1 hY.2
      have he : Level.LinearRank.compress A B Y = Z := by
        simpa only [Level.LinearRank.compress, Restriction.compressFrequency,
          LinearMap.comp_assoc] using hc
      rw [he] at hr
      have hr' : frequencyRank Z + order A B = frequencyRank Y := by
        simpa only [frequencyRank, order, Nat.add_assoc] using hr
      have hdY : d < frequencyRank Y := hZ.trans_eq hr'
      rw [hf Y hdY, zero_mul]
    · rw [ite_eq_right hY, zero_mul]
  · rw [ite_eq_right hc]

theorem degree_hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) {d : ℕ} (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    DegreeAtMost (d - order A B) (hybridDerivative A B T f) := by
  intro Z hZ
  exact hybridDerivative_coeff_zero_of_lt A B T f hf Z (by omega)

theorem hybridDerivative_eq_zero_of_lt_order (A : Submodule F2 E)
    (B : Submodule F2 F) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B) : hybridDerivative A B T f = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  exact hybridDerivative_coeff_zero_of_lt A B T f hf Z (by omega)

theorem mapDerivative_coeff_zero_of_lt (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (Z : X.ker →ₗ[F2] (E ⧸ X.range))
    (hZ : d < frequencyRank Z + frequencyRank X) :
    linearCoeff (mapDerivative X f) Z = 0 := by
  rw [linearCoeff_mapDerivative]
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hY : RankAdditivity.RankBelow X Y ∧
      Restriction.compressFrequency X.range X.ker Y = Z
  · rw [ite_eq_left hY]
    have hc : FullCompression.compression X Y = Z := by
      simpa only [FullCompression.compression, Restriction.compressFrequency] using hY.2
    have hr := FullCompression.fiber_rank X Z
      (⟨Y, hY.1, hc⟩ : FullCompression.Fiber X Z)
    apply hf Y
    unfold frequencyRank at *
    change Module.finrank F2 Y.range =
      Module.finrank F2 X.range + Module.finrank F2 Z.range at hr
    omega
  · rw [ite_eq_right hY]

theorem degree_mapDerivative (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    DegreeAtMost (d - frequencyRank X) (mapDerivative X f) := by
  intro Z hZ
  exact mapDerivative_coeff_zero_of_lt X f hf Z (by omega)

theorem mapDerivative_eq_zero_of_lt_rank (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < frequencyRank X) : mapDerivative X f = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  exact mapDerivative_coeff_zero_of_lt X f hf Z (by omega)

theorem mapDerivative_zero (X : F →ₗ[F2] E) :
    mapDerivative X (0 : (E →ₗ[F2] F) → ℝ) = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  rw [linearCoeff_mapDerivative]
  simp [linearCoeff]

theorem degree_map_hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    DegreeAtMost (d - (order A B + frequencyRank X))
      (mapDerivative X (hybridDerivative A B T f)) := by
  simpa only [Nat.sub_sub] using
    degree_mapDerivative X (hybridDerivative A B T f)
      (degree_hybridDerivative A B T f hf)

/-- The support cutoff keeps the total order intact even when `order A B > d`. -/
theorem map_hybridDerivative_eq_zero_of_lt_order_rank
    (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B + Module.finrank F2 X.range) :
    mapDerivative X (hybridDerivative A B T f) = 0 := by
  by_cases hAB : d < order A B
  · rw [hybridDerivative_eq_zero_of_lt_order A B T f hf hAB, mapDerivative_zero]
  · apply mapDerivative_eq_zero_of_lt_rank X (hybridDerivative A B T f)
      (degree_hybridDerivative A B T f hf)
    unfold frequencyRank
    omega

theorem map_hybridDerivative_fourth_average_eq_zero_of_lt_order_rank
    (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B + Module.finrank F2 X.range) :
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) = 0 := by
  simp_rw [map_hybridDerivative_eq_zero_of_lt_order_rank A B X _ f hf h]
  simp

end UniqueGamesTheorem.Appendix.DerivativeDegree

end

end

end OAI
