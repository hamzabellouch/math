import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Std
import OAI.Computability.UniqueGames.PCP.SourceNoiseParameterLemmas
import OAI.Computability.UniqueGames.Reduction.EncodingLemmas
import OAI.Computability.UniqueGames.Reduction.RealTargetLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.Explicit

variable {α β : Type*}

/-- A Cartesian product that preserves repetitions in each input list. -/
def pairs (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap fun x => ys.map fun y => (x, y)

theorem length_pairs (xs : List α) (ys : List β) :
    (pairs xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [pairs]
  | cons x xs ih =>
    simp only [pairs, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons] at *
    rw [ih, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem mem_pairs {xs : List α} {ys : List β} {x : α} {y : β} :
    (x, y) ∈ pairs xs ys ↔ x ∈ xs ∧ y ∈ ys := by
  simp [pairs]

/-- Enumerate all words of length `k` over an explicitly listed alphabet. -/
def words (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | k + 1 => (pairs alphabet (words alphabet k)).map fun p => p.1 :: p.2

theorem length_words (alphabet : List α) (k : Nat) :
    (words alphabet k).length = alphabet.length ^ k := by
  induction k with
  | zero => simp [words]
  | succ k ih =>
    simp only [words, List.length_map, length_pairs, ih, Nat.pow_succ]
    exact Nat.mul_comm _ _

/-- The enumerator covers exactly the prescribed words. -/
theorem mem_words {alphabet : List α} {w : List α} {k : Nat} :
    w ∈ words alphabet k ↔ w.length = k ∧ ∀ a ∈ w, a ∈ alphabet := by
  induction k generalizing w with
  | zero => cases w <;> simp [words]
  | succ k ih =>
    cases w with
    | nil => simp [words, pairs]
    | cons a w =>
      simp only [words, List.mem_map]
      constructor
      · rintro ⟨⟨b, v⟩, h, heq⟩
        cases heq
        obtain ⟨ha, hw⟩ := mem_pairs.mp h
        obtain ⟨hlen, hall⟩ := ih.mp hw
        constructor
        · simp [hlen]
        · intro x hx
          rcases List.mem_cons.mp hx with hax | hxw
          · simpa [hax] using ha
          · exact hall x hxw
      · rintro ⟨hlen, hall⟩
        refine ⟨(a, w), mem_pairs.mpr ⟨hall a (by simp), ?_⟩, rfl⟩
        apply ih.mpr
        constructor
        · simpa using hlen
        · intro x hx
          exact hall x (List.mem_cons_of_mem a hx)

/-- `(question occurrences, binary map matrix, noise index, binary functional)`.
The matrix is flattened and has `(2*k+1)*dimR` bits. -/
abbrev CoordinateOutcome := (List Nat × List Nat) × (Nat × List Nat)

def edgeOutcomes (m k dimR noiseCount : Nat) : List CoordinateOutcome :=
  pairs
    (pairs (words (List.range m) k) (words [0, 1] ((2*k + 1)*dimR)))
    (pairs (List.range noiseCount) (words [0, 1] (2*k + 1)))

/-- The formula in Equation (4.21). -/
def edgeCount (m k dimR noiseCount : Nat) : Nat :=
  m^k * 2^((2*k + 1)*(dimR + 1)) * noiseCount

theorem length_edgeOutcomes (m k dimR noiseCount : Nat) :
    (edgeOutcomes m k dimR noiseCount).length = edgeCount m k dimR noiseCount := by
  simp only [edgeOutcomes, length_pairs, length_words, List.length_range,
    List.length_cons, List.length_nil, Nat.reduceAdd, edgeCount]
  simp only [Nat.mul_add, Nat.mul_one, Nat.pow_add]
  ring

theorem edgeCount_pos {m noiseCount : Nat} (hm : 0 < m) (hv : 0 < noiseCount)
    (k dimR : Nat) : 0 < edgeCount m k dimR noiseCount := by
  exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hm) (Nat.two_pow_pos _)) hv

theorem edgeOutcomes_nonempty {m noiseCount : Nat} (hm : 0 < m)
    (hv : 0 < noiseCount) (k dimR : Nat) : edgeOutcomes m k dimR noiseCount ≠ [] := by
  intro h
  have hp := edgeCount_pos hm hv k dimR
  rw [← length_edgeOutcomes, h] at hp
  exact Nat.not_lt_zero _ hp

theorem edgeCount_mono {m bound : Nat} (h : m ≤ bound) (k dimR noiseCount : Nat) :
    edgeCount m k dimR noiseCount ≤ edgeCount bound k dimR noiseCount := by
  exact Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h k))

theorem product_pow (a b k : Nat) : (a*b)^k = a^k*b^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Nat.pow_succ, ih]
    ac_rfl

theorem edgeCount_polynomial_bound {m n coefficient degree : Nat}
    (h : m ≤ coefficient * (n + 1)^degree) (k dimR noiseCount : Nat) :
    edgeCount m k dimR noiseCount ≤
      (coefficient^k * 2^((2*k + 1)*(dimR + 1)) * noiseCount) *
        (n + 1)^(degree*k) := by
  calc
    edgeCount m k dimR noiseCount ≤
        edgeCount (coefficient * (n + 1)^degree) k dimR noiseCount :=
      edgeCount_mono h k dimR noiseCount
    _ = _ := by
      simp only [edgeCount, product_pow, ← Nat.pow_mul]
      ac_rfl

end UniqueGamesTheorem.Reduction.Explicit

end

section

/-! Actual finite linear-map enumeration for the free homogeneous coordinates.
The lists contain linear maps themselves, constructed by finite coordinate sums.
Their exhaustiveness and lack of repetitions identify the list with the uniform
map experiment. No machine running-time claim follows just from their lengths.
-/

namespace UniqueGamesTheorem.Reduction.ActualEnumeration

open Integration.BinaryLinear
open ActualHomogeneous
open UniqueGamesTheorem.Reduction.Explicit
open scoped BigOperators

variable {α β N : Type*} {m n k s d noiseCount : Nat}

theorem nodup_pairs {xs : List α} {ys : List β} (hx : xs.Nodup) (hy : ys.Nodup) :
    (pairs xs ys).Nodup := hx.product hy

/-- Exhaustive finite-function enumeration with a specified value list. -/
def functions (values : List α) : (n : Nat) → List (Fin n → α)
  | 0 => [Fin.elim0]
  | n + 1 => (pairs values (functions values n)).map
      (fun p => Fin.cons p.1 p.2)

theorem length_functions (values : List α) (n : Nat) :
    (functions values n).length = values.length^n := by
  induction n with
  | zero => simp [functions]
  | succ n ih => simp [functions, length_pairs, ih, pow_succ, Nat.mul_comm]

theorem mem_functions {values : List α} (full : ∀ a, a ∈ values)
    (f : Fin n → α) : f ∈ functions values n := by
  induction n with
  | zero =>
    have : f = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [functions, this]
  | succ n ih =>
    apply List.mem_map.mpr
    exact ⟨(f 0, Fin.tail f), mem_pairs.mpr ⟨full _, ih _⟩, Fin.cons_self_tail f⟩

theorem nodup_functions {values : List α} (distinct : values.Nodup) (n : Nat) :
    (functions values n).Nodup := by
  induction n with
  | zero => simp [functions]
  | succ n ih =>
    apply (nodup_pairs distinct ih).map
    intro x y h
    apply Prod.ext
    · exact congrFun h 0
    · funext i
      exact congrFun h i.succ

section Coefficients

variable (k : Nat) (R : Type*) [AddCommGroup R] [Module F2 R]

abbrev Coefficients := R × (Fin k → R × R)

def fromCoefficients (a : Coefficients k R) : E k →ₗ[F2] R where
  toFun x := x.1 • a.1 + ∑ j : Fin k,
    ((x.2 j).1 • (a.2 j).1 + (x.2 j).2 • (a.2 j).2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul]
    simp only [add_add_add_comm, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      mul_smul, smul_add, Finset.smul_sum, RingHom.id_apply]

def toCoefficients (X : E k →ₗ[F2] R) : Coefficients k R :=
  (X (hBasis k), fun j => (X (firstBasis j), X (secondBasis j)))

theorem to_fromCoefficients (a : Coefficients k R) :
    toCoefficients k R (fromCoefficients k R a) = a := by
  apply Prod.ext
  · simp [toCoefficients, fromCoefficients, hBasis]
  · funext j
    apply Prod.ext <;>
      simp [toCoefficients, fromCoefficients, firstBasis, secondBasis, Pi.single_apply,
        apply_ite]

theorem from_toCoefficients (X : E k →ₗ[F2] R) :
    fromCoefficients k R (toCoefficients k R X) = X := by
  apply LinearMap.ext
  intro x
  exact (linearMap_expansion X x).symm

/-- Actual matrix-coefficient equivalence, rather than just a count model. -/
def coefficientEquiv : Coefficients k R ≃ (E k →ₗ[F2] R) where
  toFun := fromCoefficients k R
  invFun := toCoefficients k R
  left_inv := to_fromCoefficients k R
  right_inv := from_toCoefficients k R

def allLinearMaps (values : List R) : List (E k →ₗ[F2] R) :=
  (pairs values (functions (pairs values values) k)).map (coefficientEquiv k R)

theorem length_allLinearMaps (values : List R) :
    (allLinearMaps k R values).length = values.length^(2*k+1) := by
  simp only [allLinearMaps, List.length_map, length_pairs, length_functions]
  rw [show values.length * values.length = values.length^2 by simp [pow_two],
    ← pow_mul, pow_succ]
  exact Nat.mul_comm _ _

theorem mem_allLinearMaps {values : List R} (full : ∀ a, a ∈ values)
    (X : E k →ₗ[F2] R) : X ∈ allLinearMaps k R values := by
  apply List.mem_map.mpr
  refine ⟨toCoefficients k R X, ?_, from_toCoefficients k R X⟩
  apply mem_pairs.mpr
  exact ⟨full _, mem_functions (fun a => mem_pairs.mpr ⟨full _, full _⟩) _⟩

theorem nodup_allLinearMaps {values : List R} (distinct : values.Nodup) :
    (allLinearMaps k R values).Nodup :=
  (nodup_pairs distinct (nodup_functions (nodup_pairs distinct distinct) k)).map
    (coefficientEquiv k R).injective

theorem cardinal_linearMaps [Fintype R] [Fintype (E k →ₗ[F2] R)] :
    Fintype.card (E k →ₗ[F2] R) = (Fintype.card R)^(2*k+1) := by
  rw [← Fintype.card_congr (coefficientEquiv k R)]
  simp only [Coefficients, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [show Fintype.card R * Fintype.card R = (Fintype.card R)^2 by simp [pow_two],
    ← pow_mul, pow_succ]
  exact Nat.mul_comm _ _

end Coefficients

def vectors (s : Nat) : List (Integration.BinaryLinear.Vector s) :=
  (List.finRange (2^s)).map (Encoding.alphabetEquiv s).symm

theorem length_vectors (s : Nat) : (vectors s).length = 2^s := by
  simp [vectors]

theorem mem_vectors (v : Integration.BinaryLinear.Vector s) : v ∈ vectors s := by
  exact List.mem_map.mpr ⟨Encoding.alphabetEquiv s v, List.mem_finRange _,
    (Encoding.alphabetEquiv s).symm_apply_apply v⟩

theorem nodup_vectors (s : Nat) : (vectors s).Nodup :=
  (List.nodup_finRange _).map (Encoding.alphabetEquiv s).symm.injective

abbrev Ambient (s d : Nat) :=
  Integration.BinaryLinear.Vector s × Integration.BinaryLinear.Vector d

def ambientVectors (s d : Nat) : List (Ambient s d) := pairs (vectors s) (vectors d)

theorem length_ambientVectors (s d : Nat) : (ambientVectors s d).length = 2^(s+d) := by
  simp [ambientVectors, length_pairs, length_vectors, pow_add]

theorem mem_ambientVectors (v : Ambient s d) : v ∈ ambientVectors s d :=
  mem_pairs.mpr ⟨mem_vectors v.1, mem_vectors v.2⟩

theorem nodup_ambientVectors (s d : Nat) : (ambientVectors s d).Nodup :=
  nodup_pairs (nodup_vectors s) (nodup_vectors d)

abbrev Query (m k s d : Nat) := (Fin k → Fin m) × (E k →ₗ[F2] Ambient s d)

def queries (m k s d : Nat) : List (Query m k s d) :=
  pairs (functions (List.finRange m) k) (allLinearMaps k _ (ambientVectors s d))

theorem mem_queries (q : Query m k s d) : q ∈ queries m k s d :=
  mem_pairs.mpr ⟨mem_functions (fun i => List.mem_finRange i) _,
    mem_allLinearMaps k _ mem_ambientVectors _⟩

theorem nodup_queries (m k s d : Nat) : (queries m k s d).Nodup :=
  nodup_pairs (nodup_functions (List.nodup_finRange _) _)
    (nodup_allLinearMaps k _ (nodup_ambientVectors s d))

theorem length_queries (m k s d : Nat) :
    (queries m k s d).length = m^k * 2^((s+d)*(2*k+1)) := by
  simp [queries, length_pairs, length_functions, length_allLinearMaps,
    length_ambientVectors, ← pow_mul]

abbrev Outcome (m k s d noiseCount : Nat) :=
  Query m k s d ×
    (Fin noiseCount × (E k →ₗ[F2] F2))

def outcomes (m k s d noiseCount : Nat) : List (Outcome m k s d noiseCount) :=
  pairs
    (queries m k s d)
    (pairs (List.finRange noiseCount) (allLinearMaps k F2 [0, 1]))

theorem length_outcomes (m k s d noiseCount : Nat) :
    (outcomes m k s d noiseCount).length = edgeCount m k (s+d) noiseCount := by
  simp only [outcomes, queries, length_pairs, length_functions, List.length_finRange,
    length_allLinearMaps, length_ambientVectors, List.length_cons, List.length_nil,
    edgeCount, ← pow_mul]
  change m^k * 2^((s+d)*(2*k+1)) * (noiseCount * 2^(2*k+1)) =
    m^k * 2^((2*k+1)*(s+d+1)) * noiseCount
  rw [show (2*k+1)*(s+d+1) = (s+d)*(2*k+1)+(2*k+1) by ring, pow_add]
  ring

theorem mem_outcomes (ω : Outcome m k s d noiseCount) :
    ω ∈ outcomes m k s d noiseCount := by
  apply mem_pairs.mpr
  constructor
  · exact mem_pairs.mpr ⟨mem_functions (fun i => List.mem_finRange i) _,
      mem_allLinearMaps k _ mem_ambientVectors _⟩
  · exact mem_pairs.mpr ⟨List.mem_finRange _, mem_allLinearMaps k F2
      (fun a => by rcases scalar_cases a with rfl | rfl <;> simp) _⟩

theorem nodup_outcomes (m k s d noiseCount : Nat) :
    (outcomes m k s d noiseCount).Nodup := by
  apply nodup_pairs
  · exact nodup_pairs (nodup_functions (List.nodup_finRange _) _)
      (nodup_allLinearMaps k _ (nodup_ambientVectors s d))
  · exact nodup_pairs (List.nodup_finRange _)
      (nodup_allLinearMaps k F2 (by simp))

/-- The executable edge experiment for an arbitrary explicitly ordered noise
index type. Equal noise vectors still have separate indices and entries. -/
def indexedOutcomes (m k s d : Nat) (indices : List N) :
    List (Query m k s d × (N × (E k →ₗ[F2] F2))) :=
  pairs (queries m k s d) (pairs indices (allLinearMaps k F2 [0, 1]))

theorem length_indexedOutcomes (m k s d : Nat) (indices : List N) :
    (indexedOutcomes m k s d indices).length = edgeCount m k (s+d) indices.length := by
  rw [← length_outcomes m k s d indices.length]
  simp only [indexedOutcomes, outcomes, length_pairs, List.length_finRange]

theorem mem_indexedOutcomes {indices : List N} (full : ∀ i, i ∈ indices)
    (ω : Query m k s d × (N × (E k →ₗ[F2] F2))) :
    ω ∈ indexedOutcomes m k s d indices := by
  apply mem_pairs.mpr
  exact ⟨mem_queries _, mem_pairs.mpr ⟨full _, mem_allLinearMaps k F2
    (fun a => by rcases scalar_cases a with rfl | rfl <;> simp) _⟩⟩

theorem nodup_indexedOutcomes {indices : List N} (distinct : indices.Nodup)
    (m k s d : Nat) : (indexedOutcomes m k s d indices).Nodup :=
  nodup_pairs (nodup_queries m k s d)
    (nodup_pairs distinct (nodup_allLinearMaps k F2 (by simp)))

theorem indexedOutcomes_nonempty {m : Nat} (hm : 0 < m)
    (k s d : Nat) {indices : List N} (nonempty : indices ≠ []) :
    indexedOutcomes m k s d indices ≠ [] := by
  apply List.length_pos_iff.mp
  rw [length_indexedOutcomes]
  exact edgeCount_pos hm (List.length_pos_iff.mpr nonempty) k (s+d)

/-- A genuine polynomial size bound for the actual linear-map edge list.
This is deliberately separate from a certified machine running-time bound. -/
theorem length_indexedOutcomes_polynomial_bound {m n coefficient degree : Nat}
    (h : m ≤ coefficient * (n+1)^degree) (k s d : Nat) (indices : List N) :
    (indexedOutcomes m k s d indices).length ≤
      (coefficient^k * 2^((2*k+1)*(s+d+1)) * indices.length) *
        (n+1)^(degree*k) := by
  rw [length_indexedOutcomes]
  exact edgeCount_polynomial_bound h k (s+d) indices.length

end UniqueGamesTheorem.Reduction.ActualEnumeration

end

section

/-!
# Realizing the existing Håstad noise law with a finite uniform tape

A tape contains one element of `Fin D` per coordinate. The corresponding noise
bit is true exactly when that element has value zero. For `D > 0`, its law is
exactly `Foundations.Hastad.noiseWeight ((D : ℝ)⁻¹)`.

The construction also permits an empty coordinate type and `D = 1`.
-/

namespace UniqueGamesTheorem.Reduction.FiniteNoise

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Hastad (noiseWeight)

def realizedBit {D : Nat} (z : Fin D) : Bool := decide (z.val = 0)

def realizedNoise {A : Type*} {D : Nat} (z : A → Fin D) : A → Bool :=
  fun a => realizedBit (z a)

theorem realizedBit_eq_true_iff {D : Nat} (positive : 0 < D) (z : Fin D) :
    realizedBit z = true ↔ z = ⟨0, positive⟩ := by
  simp [realizedBit, Fin.ext_iff]

/-- The two fibers of a coordinate have their actual normalized finite counts. -/
theorem coordinate_fiber_sum {D : Nat} (positive : 0 < D) (b : Bool) :
    (∑ z : Fin D, if realizedBit z = b then (D : ℝ)⁻¹ else 0) =
      if b then (D : ℝ)⁻¹ else 1 - (D : ℝ)⁻¹ := by
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positive
  have ht : (∑ z : Fin D, if realizedBit z = true then (D : ℝ)⁻¹ else 0) =
      (D : ℝ)⁻¹ := by
    simp_rw [realizedBit_eq_true_iff positive]
    simp
  have htotal :
      (∑ z : Fin D, if realizedBit z = false then (D : ℝ)⁻¹ else 0) +
      (∑ z : Fin D, if realizedBit z = true then (D : ℝ)⁻¹ else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    have he (z : Fin D) :
        (if realizedBit z = false then (D : ℝ)⁻¹ else 0) +
          (if realizedBit z = true then (D : ℝ)⁻¹ else 0) = (D : ℝ)⁻¹ := by
      cases realizedBit z <;> simp
    simp_rw [he]
    simp [hd]
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · linarith
  · exact ht

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Product distributivity computes the mass of every complete Boolean noise vector. -/
theorem noiseWeight_eq_fiber_sum {D : Nat} (positive : 0 < D) (μ : A → Bool) :
    noiseWeight ((D : ℝ)⁻¹) μ =
      ∑ z : A → Fin D,
        ∏ a, if realizedBit (z a) = μ a then (D : ℝ)⁻¹ else 0 := by
  rw [← Fintype.prod_sum (fun (a : A) (z : Fin D) =>
    if realizedBit z = μ a then (D : ℝ)⁻¹ else 0)]
  unfold noiseWeight
  apply Finset.prod_congr rfl
  intro a _
  exact (coordinate_fiber_sum positive (μ a)).symm

omit [DecidableEq A] in
theorem fiber_product_eq_indicator {D : Nat} (z : A → Fin D) (μ : A → Bool) :
    (∏ a, if realizedBit (z a) = μ a then (D : ℝ)⁻¹ else 0) =
      if realizedNoise z = μ then ((D : ℝ)⁻¹) ^ Fintype.card A else 0 := by
  classical
  by_cases h : realizedNoise z = μ
  · rw [ite_eq_left h]
    have ha (a : A) : realizedBit (z a) = μ a := congrFun h a
    simp [ha]
  · rw [ite_eq_right h]
    obtain ⟨a, ha⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    exact ite_eq_right ha

/-- Exact pushforward law for every observable, using the existing noise weight. -/
theorem expect_realizedNoise {D : Nat} (positive : 0 < D) (H : (A → Bool) → ℝ) :
    (𝔼 z : A → Fin D, H (realizedNoise z)) =
      ∑ μ : A → Bool, noiseWeight ((D : ℝ)⁻¹) μ * H μ := by
  classical
  symm
  simp_rw [noiseWeight_eq_fiber_sum positive, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [fiber_product_eq_indicator]
  have he (z : A → Fin D) :
      (∑ μ : A → Bool,
        (if realizedNoise z = μ then ((D : ℝ)⁻¹) ^ Fintype.card A else 0) * H μ) =
      ((D : ℝ)⁻¹) ^ Fintype.card A * H (realizedNoise z) := by
    simp [eq_comm]
  simp_rw [he]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [div_eq_mul_inv, inv_pow]
  rw [← Finset.mul_sum]
  exact mul_comm _ _

end UniqueGamesTheorem.Reduction.FiniteNoise

end

end OAI
