import Mathlib
import OAI.Computability.MaxCut.Games.Deletion
import OAI.Computability.MaxCut.Games.MatrixFourier
import OAI.Computability.MaxCut.Games.RowErasureSliceQuotient

namespace OAI

namespace MaxCutGames.Appendix.Restriction

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

end MaxCutGames.Appendix.Restriction

noncomputable section

namespace MaxCutGames.Appendix.Restriction

open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
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
    (Y : F →ₗ[F2] E) (N : MaxCutGames.Fourier.MatrixRestrictions.Parameter A B) :
    linearTracePair (MaxCutGames.Fourier.MatrixRestrictions.embed A B N) Y =
      linearTracePair N (compressFrequency A B Y) := by
  unfold linearTracePair MaxCutGames.Fourier.MatrixRestrictions.embed compressFrequency
  simp only [LinearMap.comp_assoc]
  rw [LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_assoc]

omit [FiniteDimensional F2 E] in
/-- The complex character identity in (A.1), on actual binary linear maps. -/
theorem linear_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : MaxCutGames.Fourier.MatrixRestrictions.Parameter A B) :
    linearTraceCharacter Y (T + MaxCutGames.Fourier.MatrixRestrictions.embed A B N) =
      linearTraceCharacter Y T * linearTraceCharacter (compressFrequency A B Y) N := by
  simp only [linearTraceCharacter_apply, linearTracePair_add_left,
    linear_trace_restriction, MaxCutGames.Fourier.MatrixCharacters.binarySign_add]

omit [FiniteDimensional F2 E] in
theorem real_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : MaxCutGames.Fourier.MatrixRestrictions.Parameter A B) :
    (linearTraceCharacter Y (T + MaxCutGames.Fourier.MatrixRestrictions.embed A B N)).re =
      (linearTraceCharacter Y T).re * (linearTraceCharacter (compressFrequency A B Y) N).re := by
  rw [linear_character_restriction, Complex.mul_re]
  simp only [linearTraceCharacter_apply,
    MaxCutGames.Fourier.MatrixCharacters.binarySign_im, mul_zero, sub_zero]

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in

theorem linear_restriction_average (A : Submodule F2 E) (B : Submodule F2 F)
    (h : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, 𝔼 N, MaxCutGames.Fourier.MatrixRestrictions.restrict h A B T N) = 𝔼 T, h T :=
  real_translation_average (MaxCutGames.Fourier.MatrixRestrictions.embed A B) h

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
/-- The `p`th-moment form of (A.2). In fact the averaging identity holds for
every real exponent, whenever the observable is interpreted by real powers. -/
theorem linear_restriction_moment_average (A : Submodule F2 E) (B : Submodule F2 F)
    (h : (E →ₗ[F2] F) → ℝ) (p : ℝ) :
    (𝔼 T, 𝔼 N, |MaxCutGames.Fourier.MatrixRestrictions.restrict h A B T N| ^ p) =
      𝔼 T, |h T| ^ p :=
  real_translation_average (MaxCutGames.Fourier.MatrixRestrictions.embed A B)
    (fun T => |h T| ^ p)

variable [Fintype (F →ₗ[F2] E)]

theorem linear_coefficient_merging (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (Z : B →ₗ[F2] (E ⧸ A)) :
    linearCoeff (MaxCutGames.Fourier.MatrixRestrictions.restrict f A B T) Z =
      ∑ Y : F →ₗ[F2] E,
        if compressFrequency A B Y = Z then linearCoeff f Y * (linearTraceCharacter Y T).re
        else 0 := by
  classical
  have hexpansion : MaxCutGames.Fourier.MatrixRestrictions.restrict f A B T =
      ∑ Y : F →ₗ[F2] E,
        (linearCoeff f Y * (linearTraceCharacter Y T).re) •
          (fun N => (linearTraceCharacter (compressFrequency A B Y) N).re) := by
    funext N
    change f (T + MaxCutGames.Fourier.MatrixRestrictions.embed A B N) = _
    rw [← linear_fourier_inversion f (T + MaxCutGames.Fourier.MatrixRestrictions.embed A B N)]
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

end MaxCutGames.Appendix.Restriction
end

section

namespace MaxCutGames.Appendix.Level

/-- The unselected multiplier in factored form, after multiplying numerator
and denominator by `2^(2*r)`. Selected characters have multiplier one. -/
def rankFilter (d r : Nat) (selected : Bool) : Rat :=
  if selected then 1 else
    (((2 : Rat) ^ r - 2 ^ d) * (2 ^ r - 2 ^ (d - 1))) / ((2 : Rat) ^ r) ^ 2

theorem filter_polynomial_algebra (q x y : Rat) (hq : q ≠ 0) :
    (q - x) * (q - y) / q ^ 2 = 1 - (x + y) / q + x * y / q ^ 2 := by
  grind

theorem rankFilter_selected (d r : Nat) : rankFilter d r true = 1 := by
  simp [rankFilter]

theorem rankFilter_zero_at_d (d : Nat) : rankFilter d d false = 0 := by
  simp only [rankFilter, Bool.false_eq_true, ↓reduceIte]
  grind

theorem rankFilter_zero_at_pred (d : Nat) : rankFilter d (d - 1) false = 0 := by
  simp only [rankFilter, Bool.false_eq_true, ↓reduceIte]
  grind

/-- Only ranks `d-1` and `d` can restrict to rank `d-1`; no degree
bound on the original function is needed. -/
theorem only_two_source_ranks {d r s : Nat} (hd : 1 ≤ d)
    (hlo : s ≤ r) (hhi : r ≤ s + 1) (hs : s + 1 = d) :
    r = d ∨ r = d - 1 := by
  omega

/-- Selected characters lose exactly one rank. On an unselected character,
the two roots of the filter remove every possible unwanted contribution. -/
theorem rank_filter_character {d r s : Nat} (hd : 1 ≤ d)
    (selected : Bool) (c : Rat)
    (hlo : s ≤ r) (hhi : r ≤ s + 1)
    (hselected : selected = true → r = s + 1) :
    (if selected then if r = d then c else 0 else 0) =
      (if s + 1 = d then rankFilter d r selected * c else 0) := by
  cases selected with
  | true =>
    have hr := hselected rfl
    simp [rankFilter, hr]
  | false =>
    by_cases hs : s + 1 = d
    · have hr := only_two_source_ranks hd hlo hhi hs
      rcases hr with hr | hr
      · simp [hs, hr, rankFilter_zero_at_d]
      · simp [hs, hr, rankFilter_zero_at_pred]
    · simp [hs]

/-- A finite merged coefficient. `phase` can incorporate a translation
character and the indicator of one restriction fiber. -/
def mergedCoefficient {α : Type} (indices : List α)
    (phase coefficient : α → Rat) : Rat :=
  (indices.map (fun x => phase x * coefficient x)).sum

/-- The character identity survives arbitrary merging, signs, and
cancellation. No injectivity of the restriction of frequencies is assumed. -/
theorem rank_filter_commutes_with_merge {α : Type} (indices : List α)
    (d : Nat) (hd : 1 ≤ d) (rank restrictedRank : α → Nat)
    (selected : α → Bool) (phase coefficient : α → Rat)
    (hlo : ∀ x, restrictedRank x ≤ rank x)
    (hhi : ∀ x, rank x ≤ restrictedRank x + 1)
    (hselected : ∀ x, selected x = true → rank x = restrictedRank x + 1) :
    mergedCoefficient indices phase
        (fun x => if selected x then if rank x = d then coefficient x else 0 else 0) =
      mergedCoefficient indices phase
        (fun x => if restrictedRank x + 1 = d
          then rankFilter d (rank x) (selected x) * coefficient x else 0) := by
  unfold mergedCoefficient
  congr 1
  apply List.map_congr_left
  intro x _
  exact congrArg (fun c : Rat => phase x * c)
    (rank_filter_character hd (selected x) (coefficient x) (hlo x) (hhi x)
      (hselected x))

theorem higher_ranks_cannot_contaminate {d r s : Nat}
    (hhi : r ≤ s + 1) (hr : d < r) : s + 1 ≠ d := by
  omega

/-- Arithmetic in the iterated globality parameter
`4^k * 2^(4*k*d - 2*k*(k-1))`. -/
theorem iterated_globality_exponent {d k : Nat} (hd : 1 ≤ d) (hk : k ≤ d) :
    2 * k + 4 * k * d - 2 * k * (k - 1) ≤ 10 * d * d := by
  have hkd : k * d ≤ d * d := Nat.mul_le_mul_right d hk
  have hdd : d ≤ d * d := by
    have := Nat.mul_le_mul_left d hd
    simpa using this
  have hbasic : 2 * k + 4 * k * d ≤ 6 * d * d := by
    grind
  grind

theorem successor_le_two_pow (d : Nat) : d + 1 ≤ 2 ^ d := by
  induction d with
  | zero => decide
  | succ d ih =>
    rw [Nat.pow_succ]
    omega

/-- A deliberately coarse bound for the number of dimension-indexed
selector choices. The geometric subspace count is an explicit hypothesis. -/
theorem selector_multiplicity_bound {d count : Nat} (hd : 1 ≤ d)
    (hcount : count ≤ (d + 1) ^ 2 * 2 ^ (d * d)) :
    count ≤ 2 ^ (3 * d * d) := by
  have hs := Nat.pow_le_pow_left (successor_le_two_pow d) 2
  have hdd : d ≤ d * d := by
    have := Nat.mul_le_mul_left d hd
    simpa using this
  calc
    count ≤ (d + 1) ^ 2 * 2 ^ (d * d) := hcount
    _ ≤ (2 ^ d) ^ 2 * 2 ^ (d * d) := Nat.mul_le_mul_right _ hs
    _ = 2 ^ (d * 2 + d * d) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    _ ≤ 2 ^ (3 * d * d) := Nat.pow_le_pow_right (by decide) (by grind)

/-- The final fourth-root exponent has the advertised slack. -/
theorem final_exponent_slack (d : Nat) : 113 * d * d ≤ 4 * (30 * d * d) := by
  grind

end MaxCutGames.Appendix.Level

namespace MaxCutGames.Appendix.Level.LinearRank

open Module LinearMap
attribute [local instance] Classical.propDecidable

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V] [FiniteDimensional K W] [FiniteDimensional K V]

/-- Restriction in the domain and quotient in the codomain, as actual
linear maps. This is the Fourier-frequency map of an affine restriction. -/
def compress (A : Submodule K V) (B : Submodule K W) (Y : W →ₗ[K] V) :
    B →ₗ[K] V ⧸ A := A.mkQ.comp (Y.comp B.subtype)

theorem finrank_comap_subtype_le (A B : Submodule K V) :
    finrank K (A.comap B.subtype) ≤ finrank K A := by
  rw [← Submodule.finrank_map_subtype_eq B (A.comap B.subtype),
    Submodule.map_comap_subtype]
  exact Submodule.finrank_mono inf_le_right

theorem quotient_rank_bounds (A : Submodule K V) (Y : W →ₗ[K] V) :
    finrank K (range (A.mkQ.comp Y)) ≤ finrank K (range Y) ∧
      finrank K (range Y) ≤ finrank K (range (A.mkQ.comp Y)) + finrank K A := by
  have h := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
  have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
    simp only [range_comp, Submodule.range_subtype]
  rw [hr, ker_comp, Submodule.ker_mkQ] at h
  have hk := finrank_comap_subtype_le A (range Y)
  omega

omit [FiniteDimensional K V] in
theorem quotient_rank_selected (A : Submodule K V) (Y : W →ₗ[K] V)
    (hA : A ≤ range Y) :
    finrank K (range (A.mkQ.comp Y)) + finrank K A = finrank K (range Y) := by
  have h := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
  have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
    simp only [range_comp, Submodule.range_subtype]
  rw [hr, ker_comp, Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hA).finrank_eq] at h
  exact h

omit [FiniteDimensional K V] in
theorem domain_rank_bounds (B : Submodule K W) (Y : W →ₗ[K] V) :
    finrank K (range (Y.comp B.subtype)) ≤ finrank K (range Y) ∧
      finrank K (range Y) ≤
        finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) := by
  have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
  have h₂ := Y.finrank_range_add_finrank_ker
  have h₃ := B.finrank_quotient_add_finrank
  rw [ker_comp] at h₁
  have hk := finrank_comap_subtype_le (ker Y) B
  have hr : finrank K (range (Y.comp B.subtype)) ≤ finrank K (range Y) := by
    apply Submodule.finrank_mono
    exact LinearMap.range_comp_le_range _ _
  omega

omit [FiniteDimensional K V] in
theorem domain_rank_selected (B : Submodule K W) (Y : W →ₗ[K] V)
    (hB : ker Y ≤ B) :
    finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) =
      finrank K (range Y) := by
  have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
  have h₂ := Y.finrank_range_add_finrank_ker
  have h₃ := B.finrank_quotient_add_finrank
  rw [ker_comp, (Submodule.comapSubtypeEquivOfLe hB).finrank_eq] at h₁
  omega

omit [FiniteDimensional K V] in

theorem hybrid_rank_loss (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) (hA : A ≤ range Y) (hB : A.comap Y ≤ B) :
    finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) =
      finrank K (range Y) := by
  have hquot := quotient_rank_selected A Y hA
  have hdom := domain_rank_selected B (A.mkQ.comp Y) (by
    simpa only [ker_comp, Submodule.ker_mkQ] using hB)
  have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
  rw [hc] at hdom
  omega

/-- Equality in the dimension bound for a subspace intersection forces
the original subspace to lie in the restricting subspace. -/
theorem finrank_comap_subtype_eq_iff (A B : Submodule K V) :
    finrank K (A.comap B.subtype) = finrank K A ↔ A ≤ B := by
  constructor
  · intro h
    have hdim := Submodule.finrank_map_subtype_eq B (A.comap B.subtype)
    rw [Submodule.map_comap_subtype, h] at hdim
    have heq : B ⊓ A = A := Submodule.eq_of_le_of_finrank_eq inf_le_right hdim
    calc
      A = B ⊓ A := heq.symm
      _ ≤ B := inf_le_left
  · intro h
    exact (Submodule.comapSubtypeEquivOfLe h).finrank_eq

theorem quotient_rank_equality_iff (A : Submodule K V) (Y : W →ₗ[K] V) :
    finrank K (range (A.mkQ.comp Y)) + finrank K A = finrank K (range Y) ↔
      A ≤ range Y := by
  constructor
  · intro heq
    have hn := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
    have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
      simp only [range_comp, Submodule.range_subtype]
    rw [hr, ker_comp, Submodule.ker_mkQ] at hn
    apply (finrank_comap_subtype_eq_iff A (range Y)).mp
    omega
  · exact quotient_rank_selected A Y

omit [FiniteDimensional K V] in
theorem domain_rank_equality_iff (B : Submodule K W) (Y : W →ₗ[K] V) :
    finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) =
      finrank K (range Y) ↔ ker Y ≤ B := by
  constructor
  · intro heq
    have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
    have h₂ := Y.finrank_range_add_finrank_ker
    have h₃ := B.finrank_quotient_add_finrank
    rw [ker_comp] at h₁
    apply (finrank_comap_subtype_eq_iff (ker Y) B).mp
    omega
  · exact domain_rank_selected B Y

/-- Every genuine restriction loses at most its order in Fourier rank. -/
theorem compression_rank_bounds (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) :
    finrank K (range (compress A B Y)) ≤ finrank K (range Y) ∧
      finrank K (range Y) ≤
        finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) := by
  have hq := quotient_rank_bounds A Y
  have hd := domain_rank_bounds B (A.mkQ.comp Y)
  have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
  rw [hc] at hd
  omega

theorem hybrid_rank_loss_iff (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) :
    finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) =
      finrank K (range Y) ↔ A ≤ range Y ∧ A.comap Y ≤ B := by
  constructor
  · intro heq
    have hq := quotient_rank_bounds A Y
    have hd := domain_rank_bounds B (A.mkQ.comp Y)
    have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
    rw [hc] at hd
    constructor
    · apply (quotient_rank_equality_iff A Y).mp
      omega
    · have he : finrank K (range ((A.mkQ.comp Y).comp B.subtype)) +
          finrank K (W ⧸ B) = finrank K (range (A.mkQ.comp Y)) := by
        rw [hc]
        omega
      have hk := (domain_rank_equality_iff B (A.mkQ.comp Y)).mp he
      simpa only [ker_comp, Submodule.ker_mkQ] using hk
  · rintro ⟨hA, hB⟩
    exact hybrid_rank_loss A B Y hA hB

/-- Instantiation of (A.17)'s rank filter for quotient by an actual line.
The only dimension hypothesis is the line's dimension; no rank cutoff is
imposed on the original map `Y`. -/
theorem line_rank_filter (A : Submodule K V) (Y : W →ₗ[K] V)
    (hline : finrank K A = 1) (d : Nat) (hd : 1 ≤ d) (c : Rat) :
    (if A ≤ range Y then
      if finrank K (range Y) = d then c else 0 else 0) =
      (if finrank K (range (A.mkQ.comp Y)) + 1 = d then
        MaxCutGames.Appendix.Level.rankFilter d (finrank K (range Y))
          (decide (A ≤ range Y)) * c else 0) := by
  classical
  have hb := quotient_rank_bounds A Y
  have hhi : finrank K (range Y) ≤ finrank K (range (A.mkQ.comp Y)) + 1 := by
    simpa only [hline] using hb.2
  have hs : decide (A ≤ range Y) = true →
      finrank K (range Y) = finrank K (range (A.mkQ.comp Y)) + 1 := by
    intro h
    have hl := quotient_rank_selected A Y (of_decide_eq_true h)
    omega
  simpa only [decide_eq_true_eq] using
    MaxCutGames.Appendix.Level.rank_filter_character hd (decide (A ≤ range Y)) c hb.1 hhi hs

omit [FiniteDimensional K V] in
/-- The dual order-one instance: restriction to an actual hyperplane. -/
theorem hyperplane_rank_filter (B : Submodule K W) (Y : W →ₗ[K] V)
    (hhyperplane : finrank K (W ⧸ B) = 1) (d : Nat) (hd : 1 ≤ d) (c : Rat) :
    (if ker Y ≤ B then
      if finrank K (range Y) = d then c else 0 else 0) =
      (if finrank K (range (Y.comp B.subtype)) + 1 = d then
        MaxCutGames.Appendix.Level.rankFilter d (finrank K (range Y))
          (decide (ker Y ≤ B)) * c else 0) := by
  classical
  have hb := domain_rank_bounds B Y
  have hhi : finrank K (range Y) ≤ finrank K (range (Y.comp B.subtype)) + 1 := by
    simpa only [hhyperplane] using hb.2
  have hs : decide (ker Y ≤ B) = true →
      finrank K (range Y) = finrank K (range (Y.comp B.subtype)) + 1 := by
    intro h
    have hl := domain_rank_selected B Y (of_decide_eq_true h)
    omega
  simpa only [decide_eq_true_eq] using
    MaxCutGames.Appendix.Level.rank_filter_character hd (decide (ker Y ≤ B)) c hb.1 hhi hs

end MaxCutGames.Appendix.Level.LinearRank
end

/-! The arbitrary-dimensional linear-algebra cover in Appendix A.1. -/
namespace MaxCutGames.Appendix.DegreeCover

abbrev F2 := ZMod 2
variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

@[simp] theorem binary_add_self (v : V) : v + v = 0 := by
  have h : (1 + 1 : F2) = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : F2 => c • v) h

@[simp] theorem binary_neg (v : V) : -v = v := by
  apply neg_eq_iff_add_eq_zero.mpr
  exact binary_add_self v

/-- Glue a linear map on P to zero on Q when the restrictions agree. -/
theorem exists_glue_zero (P Q : Submodule F2 W) (f : W →ₗ[F2] V)
    (cover : P ⊔ Q = ⊤) (compatible : ∀ w ∈ P, w ∈ Q → f w = 0) :
    ∃ g : W →ₗ[F2] V,
      (∀ w ∈ P, g w = f w) ∧ (∀ w ∈ Q, g w = 0) := by
  let p : W →ₗ.[F2] V := ⟨P, f.comp P.subtype⟩
  let q : W →ₗ.[F2] V := ⟨Q, 0⟩
  have hc : ∀ (x : p.domain) (y : q.domain), (x : W) = y → p x = q y := by
    intro x y hxy
    exact compatible x x.property (hxy ▸ y.property)
  let t := p.sup q hc
  have ht : ∀ w : W, w ∈ t.domain := by
    intro w
    change w ∈ P ⊔ Q
    rw [cover]
    exact Submodule.mem_top
  let inc : W →ₗ[F2] t.domain := (LinearMap.id : W →ₗ[F2] W).codRestrict t.domain ht
  refine ⟨t.toFun.comp inc, ?_, ?_⟩
  · intro w hw
    exact ((p.left_le_sup q hc).2 (x := ⟨w, hw⟩) (y := inc w) rfl).symm
  · intro w hw
    exact ((p.right_le_sup q hc).2 (x := ⟨w, hw⟩) (y := inc w) rfl).symm

private theorem binary_cross_inline_DegreeCover {a b c d : V} (h : a + b = c + d) : c + a = d + b := by
  calc
    c + a = (c + a) + (b + b) := by simp
    _ = c + (a + b) + b := by abel
    _ = c + (c + d) + b := by rw [h]
    _ = (c + c) + (d + b) := by abel
    _ = d + b := by simp

theorem exists_cover_component (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R : W →ₗ[F2] V,
      (∀ w ∈ LinearMap.ker Z, R w = Y w) ∧
      (∀ w ∈ LinearMap.ker Y ⊔ LinearMap.ker (Y + Z), R w = 0) ∧
      LinearMap.range R ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Y := by
  have cov : LinearMap.ker Z ⊔ (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) = ⊤ := by
    simpa only [sup_assoc, sup_comm, sup_left_comm] using cover
  have compatible : ∀ w ∈ LinearMap.ker Z,
      w ∈ LinearMap.ker Y ⊔ LinearMap.ker (Y + Z) → Y w = 0 := by
    intro w hw hz
    change Z w = 0 at hw
    rcases Submodule.mem_sup.mp hz with ⟨a, ha, b, hb, hab⟩
    change Y a = 0 at ha
    change (Y + Z) b = 0 at hb
    have hYb : Y b = Z b := by
      have h := congrArg (fun v : V => v + Z b) hb
      simpa only [LinearMap.add_apply, add_assoc, binary_add_self, add_zero, zero_add] using h
    have hYw : Y w = Z b := by rw [← hab, map_add, ha, zero_add, hYb]
    have hmem : Y w ∈ (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z :=
      ⟨⟨⟨w, by simp only [LinearMap.add_apply, hw, add_zero]⟩, ⟨w, rfl⟩⟩,
        ⟨b, hYw.symm⟩⟩
    rw [triple] at hmem
    exact hmem
  obtain ⟨R, hRZ, hRYX⟩ := exists_glue_zero (LinearMap.ker Z)
    (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) Y cov compatible
  refine ⟨R, hRZ, hRYX, ?_⟩
  rintro v ⟨w, rfl⟩
  have hw : w ∈ LinearMap.ker Z ⊔ (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) := by
    rw [cov]
    exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hw with ⟨a, ha, b, hb, hab⟩
  have heq : R w = Y a := by rw [← hab, map_add, hRZ a ha, hRYX b hb, add_zero]
  refine ⟨⟨a, ?_⟩, ⟨a, heq.symm⟩⟩
  change Z a = 0 at ha
  rw [LinearMap.add_apply, ha, add_zero, heq]

/-- A general, dimension-free decomposition with pairwise disjoint images.
These are exactly the linear-algebra data used to establish the cover in A.1. -/
theorem exists_disjoint_decomposition (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R S C : W →ₗ[F2] V,
      Y + Z = R + S ∧ Y = R + C ∧ Z = S + C ∧
      Disjoint (LinearMap.range R) (LinearMap.range S) ∧
      Disjoint (LinearMap.range R) (LinearMap.range C) ∧
      Disjoint (LinearMap.range S) (LinearMap.range C) ∧
      LinearMap.range R ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Y ∧
      LinearMap.range S ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Z ∧
      LinearMap.range C ≤ LinearMap.range Y ⊓ LinearMap.range Z := by
  obtain ⟨R, hRZ, hRYX, rangeR⟩ := exists_cover_component Y Z triple cover
  obtain ⟨S, hSY, hSZX, rangeS⟩ := exists_cover_component Z Y
    (by simpa only [add_comm Z Y, inf_assoc, inf_comm, inf_left_comm] using triple)
    (by simpa only [add_comm Z Y, sup_assoc, sup_comm, sup_left_comm] using cover)
  rw [add_comm Z Y] at hSZX rangeS
  have eqX : Set.EqOn (R + S) (Y + Z) (LinearMap.ker (Y + Z)) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    rw [LinearMap.add_apply, hRYX w (Submodule.mem_sup_right hw), hSZX w (Submodule.mem_sup_right hw)]
    simpa only [zero_add] using hw.symm
  have eqY : Set.EqOn (R + S) (Y + Z) (LinearMap.ker Y) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    change Y w = 0 at hw
    simp only [LinearMap.add_apply, hRYX w (Submodule.mem_sup_left hw), hSY w hw, hw, zero_add]
  have eqZ : Set.EqOn (R + S) (Y + Z) (LinearMap.ker Z) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    change Z w = 0 at hw
    simp only [LinearMap.add_apply, hRZ w hw, hSZX w (Submodule.mem_sup_left hw), hw, add_zero]
  have hRS : R + S = Y + Z := by
    ext w
    exact LinearMap.eqOn_sup (LinearMap.eqOn_sup eqX eqY) eqZ (cover ▸ Submodule.mem_top)
  let C := Y + R
  have hC : C = Z + S := by
    ext w
    exact binary_cross_inline_DegreeCover (congrArg (fun f : W →ₗ[F2] V => f w) hRS)
  have hY : Y = R + C := by
    ext w
    change Y w = R w + (Y w + R w)
    rw [add_left_comm, binary_add_self, add_zero]
  have hZ : Z = S + C := by
    rw [hC]
    ext w
    change Z w = S w + (Z w + S w)
    rw [add_left_comm, binary_add_self, add_zero]
  have rangeC : LinearMap.range C ≤ LinearMap.range Y ⊓ LinearMap.range Z := by
    apply le_inf
    · exact (LinearMap.range_add_le Y R).trans (sup_le le_rfl (rangeR.trans inf_le_right))
    · rw [hC]
      exact (LinearMap.range_add_le Z S).trans (sup_le le_rfl (rangeS.trans inf_le_right))
  have kill : ∀ v, v ∈ LinearMap.range (Y + Z) → v ∈ LinearMap.range Y →
      v ∈ LinearMap.range Z → v = 0 := by
    intro v hx hy hz
    have h : v ∈ (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z := ⟨⟨hx, hy⟩, hz⟩
    rwa [triple] at h
  refine ⟨R, S, C, hRS.symm, hY, hZ, ?_, ?_, ?_, rangeR, rangeS, rangeC⟩
  · exact Submodule.disjoint_def.mpr (fun v hr hs => kill v (rangeR hr).1 (rangeR hr).2 (rangeS hs).2)
  · exact Submodule.disjoint_def.mpr (fun v hr hc => kill v (rangeR hr).1 (rangeR hr).2 (rangeC hc).2)
  · exact Submodule.disjoint_def.mpr (fun v hs hc => kill v (rangeS hs).1 (rangeC hc).1 (rangeS hs).2)

/-- Rank additivity needs image containment as well as disjointness. -/
theorem rank_add_of_disjoint [FiniteDimensional F2 V] (R S : W →ₗ[F2] V)
    (hd : Disjoint (LinearMap.range R) (LinearMap.range S))
    (hR : LinearMap.range R ≤ LinearMap.range (R + S))
    (hS : LinearMap.range S ≤ LinearMap.range (R + S)) :
    Module.finrank F2 (LinearMap.range (R + S)) =
      Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range S) := by
  have heq := le_antisymm (LinearMap.range_add_le R S) (sup_le hR hS)
  rw [heq]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range R) (LinearMap.range S)
  have hb : LinearMap.range R ⊓ LinearMap.range S = ⊥ := hd.eq_bot
  rw [hb, finrank_bot, add_zero] at h
  exact h

/-- The cover F(X) \ F₂(X) ⊆ F₁(X), with all three rank-additive decompositions.
There is no bound on dimension, and both bad-event exclusions are discharged. -/
theorem outside_bad_rank_cover [FiniteDimensional F2 V] (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R S C : W →ₗ[F2] V,
      Y + Z = R + S ∧ Y = R + C ∧ Z = S + C ∧
      Module.finrank F2 (LinearMap.range (Y + Z)) =
        Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range S) ∧
      Module.finrank F2 (LinearMap.range Y) =
        Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range C) ∧
      Module.finrank F2 (LinearMap.range Z) =
        Module.finrank F2 (LinearMap.range S) + Module.finrank F2 (LinearMap.range C) := by
  obtain ⟨R, S, C, hX, hY, hZ, dRS, dRC, dSC, rR, rS, rC⟩ :=
    exists_disjoint_decomposition Y Z triple cover
  refine ⟨R, S, C, hX, hY, hZ, ?_, ?_, ?_⟩
  · rw [hX]
    exact rank_add_of_disjoint R S dRS
      (hX ▸ rR.trans inf_le_left) (hX ▸ rS.trans inf_le_left)
  · rw [hY]
    exact rank_add_of_disjoint R C dRC
      (hY ▸ rR.trans inf_le_right) (hY ▸ rC.trans inf_le_left)
  · rw [hZ]
    exact rank_add_of_disjoint S C dSC
      (hZ ▸ rS.trans inf_le_right) (hZ ▸ rC.trans inf_le_right)

end MaxCutGames.Appendix.DegreeCover

end OAI
