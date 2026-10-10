import Mathlib
import OAI.Computability.MaxCut.Encoding.Encoding
import OAI.Computability.MaxCut.Encoding.BinaryRowTransport

namespace OAI

/-! Exact uniform sampling of linear maps on the common private coordinate target. -/

namespace MaxCutGames.Soundness.RawMapLaw
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open ConditionalIncidences PartnerMapCoordinates RawPartnerTarget BinaryRowTransport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} (J : Finset (Fin k)) (R : Type) [AddCommGroup R] [Module F2 R]

def rawMap (gamma : RawCoefficients J R) : RawPoint J →ₗ[F2] R :=
  (mapEquiv (fun _ : Fin k => false) J R gamma).comp
    (pointEquiv (fun _ : Fin k => false) J).symm.toLinearMap

theorem coefficients_rawMap (gamma : RawCoefficients J R) :
    gammaOfRawMap J (rawMap J R gamma) = gamma := by
  apply (mapEquiv (fun _ : Fin k => false) J R).injective
  apply LinearMap.ext
  intro y
  rw [← rawMap_on_partner]
  change mapEquiv (fun _ : Fin k => false) J R gamma
    ((pointEquiv (fun _ : Fin k => false) J).symm
      (pointEquiv (fun _ : Fin k => false) J y)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem rawMap_coefficients (Y : RawPoint J →ₗ[F2] R) :
    rawMap J R (gammaOfRawMap J Y) = Y := by
  apply LinearMap.ext
  intro v
  have h := rawMap_on_partner (fun _ : Fin k => false) J Y
    ((pointEquiv (fun _ : Fin k => false) J).symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

def rawMapEquiv : RawCoefficients J R ≃ (RawPoint J →ₗ[F2] R) where
  toFun := rawMap J R
  invFun := gammaOfRawMap J
  left_inv := coefficients_rawMap J R
  right_inv := rawMap_coefficients J R

instance rawMapsFintype [Fintype R] : Fintype (RawPoint J →ₗ[F2] R) := by
  classical
  exact Fintype.ofEquiv (RawCoefficients J R) (rawMapEquiv J R)

def bitsRawMapEquiv {Q : Type} : RawCoefficients J (ZeroInformation.Bits Q) ≃
    (RawPoint J →ₗ[F2] (Q → F2)) :=
  (rawBitsEquiv J).symm.trans (rawMapEquiv J (Q → F2))

theorem bits_coefficients {Q : Type} (gamma : RawCoefficients J (ZeroInformation.Bits Q)) :
    rowCoefficients J (gammaOfRawMap J (bitsRawMapEquiv J gamma)) = gamma := by
  change (rawBitsEquiv J) (gammaOfRawMap J (rawMap J (Q → F2) ((rawBitsEquiv J).symm gamma))) = gamma
  rw [coefficients_rawMap, Equiv.apply_symm_apply]

/-- This equality counts every raw coefficient and every genuine row map once. -/
theorem uniform_bits_rawMaps {Q : Type} [Fintype Q] [DecidableEq Q]
    (H : (RawPoint J →ₗ[F2] (Q → F2)) → ℝ) :
    (𝔼 gamma : RawCoefficients J (ZeroInformation.Bits Q), H (bitsRawMapEquiv J gamma)) =
      𝔼 Y, H Y :=
  Fintype.expect_equiv (bitsRawMapEquiv J) _ H (fun _ => rfl)

end
end MaxCutGames.Soundness.RawMapLaw

namespace MaxCutGames.Reduction.Explicit

variable {α : Type*} {β : Type*}

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
    List.length_cons, List.length_nil, edgeCount]
  simp only [Nat.mul_add, Nat.mul_one, Nat.pow_add]
  norm_num only
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

    ring

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

      ring

end MaxCutGames.Reduction.Explicit

/-! Actual finite linear-map enumeration for the free homogeneous coordinates.
The lists contain linear maps themselves, constructed by finite coordinate sums.
Their exhaustiveness and lack of repetitions identify the list with the uniform
map experiment. No machine running-time claim follows just from their lengths.
-/

namespace MaxCutGames.Reduction.ActualEnumeration

open Integration.BinaryLinear
open ActualHomogeneous
open _root_.OAI.MaxCutGames.Reduction.Explicit
open scoped BigOperators

variable {α : Type*} {β : Type*} {N : Type*} {n : Nat}

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

variable {m k s d noiseCount : Nat}

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

end MaxCutGames.Reduction.ActualEnumeration

end OAI
