import Mathlib
import OAI.Computability.DirectedFeedback.Games.ActualCanonical

namespace OAI


namespace DFVSGames.Reduction.Explicit

variable {α β : Type*}

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

abbrev CoordinateOutcome := (List Nat × List Nat) × (Nat × List Nat)

def edgeOutcomes (m k dimR noiseCount : Nat) : List CoordinateOutcome :=
  pairs
    (pairs (words (List.range m) k) (words [0, 1] ((2*k + 1)*dimR)))
    (pairs (List.range noiseCount) (words [0, 1] (2*k + 1)))

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

end DFVSGames.Reduction.Explicit


namespace DFVSGames.Reduction.ActualEnumeration

open Integration.BinaryLinear
open ActualHomogeneous
open _root_.OAI.DFVSGames.Reduction.Explicit
open scoped BigOperators

variable {α β N : Type*} {n m k s d noiseCount : Nat}

theorem nodup_pairs {xs : List α} {ys : List β} (hx : xs.Nodup) (hy : ys.Nodup) :
    (pairs xs ys).Nodup := hx.product hy

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

theorem length_indexedOutcomes_polynomial_bound {m n coefficient degree : Nat}
    (h : m ≤ coefficient * (n+1)^degree) (k s d : Nat) (indices : List N) :
    (indexedOutcomes m k s d indices).length ≤
      (coefficient^k * 2^((2*k+1)*(s+d+1)) * indices.length) *
        (n+1)^(degree*k) := by
  rw [length_indexedOutcomes]
  exact edgeCount_polynomial_bound h k (s+d) indices.length

end DFVSGames.Reduction.ActualEnumeration


namespace DFVSGames.Decoder.PaddedLaw

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open ConditionalIncidences PartnerProjection RawPartnerTarget RawMapLaw
open ActualCanonicalPullback
open SparseLaw

noncomputable section
attribute [local instance] Classical.propDecidable

section FinitePushforward

variable {α B : Type*} [Fintype α]

def pushforwardWeight (p : α → ℝ) (f : α → B) (y : B) : ℝ :=
  ∑ x, if f x = y then p x else 0

theorem pushforwardWeight_pi (p : α → ℝ) (f : α → B) (k : ℕ)
    (ys : Fin k → B) :
    pushforwardWeight (independentWeights p k) (fun xs i => f (xs i)) ys =
      independentWeights (pushforwardWeight p f) k ys := by
  classical
  simp only [pushforwardWeight, independentWeights]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro xs _
  simp only [Fintype.prod_ite_zero, funext_iff]
  split_ifs <;> rfl

theorem pushforwardWeight_joint_uniform_intercept {W : Type*} [Fintype W] [AddGroup W]
    (p : α → ℝ) (f : α → B) (shift : α → W) (z : W) (b : B) :
    pushforwardWeight (fun az : α × W => p az.1 * uniformWeights W az.2)
      (fun az => (az.2 + shift az.1, f az.1)) (z, b) =
        uniformWeights W z * pushforwardWeight p f b := by
  classical
  simp only [pushforwardWeight, Fintype.sum_prod_type]
  calc
    (∑ a : α, ∑ t : W,
        if (t + shift a, f a) = (z, b) then p a * uniformWeights W t else 0) =
      ∑ a : α, if f a = b then p a * uniformWeights W z else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : f a = b
        · simp only [Prod.mk.injEq, h, and_true, ite_true]
          exact joint_intercept_pushforward p shift a z
        · simp [Prod.mk.injEq, h]
    _ = uniformWeights W z * (∑ a : α, if f a = b then p a else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : f a = b <;> simp [h, mul_comm]

end FinitePushforward

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V]

abbrev BlockDraw (V : Type) := (V × V) ⊕ (Fin 3 × V)

def decodeSlot (i : Fin 3) : Slot :=
  if i = 0 then .first else if i = 1 then .second else .third

theorem slotIndex_decodeSlot (i : Fin 3) : ConcreteExtraction.slotIndex (decodeSlot i) = i := by
  fin_cases i <;> rfl

def blockAmbient : BlockDraw V → Fin 3 → V
  | .inl ab => ![ab.1, ab.2, 0]
  | .inr ia => Pi.single ia.1 ia.2

def blockSlopes (d : BlockDraw V) : V × V :=
  (blockAmbient d 0 + blockAmbient d 2, blockAmbient d 1 + blockAmbient d 2)

def blockThird (d : BlockDraw V) : V := blockAmbient d 2

omit [Module F2 V] in
@[simp] theorem blockSlopes_full (ab : V × V) : blockSlopes (.inl ab) = ab := by
  simp [blockSlopes, blockAmbient]

omit [Module F2 V] in
@[simp] theorem blockSlopes_first (a : V) :
    blockSlopes (.inr ((0 : Fin 3), a)) = (a, 0) := by
  simp [blockSlopes, blockAmbient]

omit [Module F2 V] in
@[simp] theorem blockSlopes_second (a : V) :
    blockSlopes (.inr ((1 : Fin 3), a)) = (0, a) := by
  simp [blockSlopes, blockAmbient]

omit [Module F2 V] in
@[simp] theorem blockSlopes_third (a : V) :
    blockSlopes (.inr ((2 : Fin 3), a)) = (a, a) := by
  simp [blockSlopes, blockAmbient]

def singletonPositions (d : Fin k → BlockDraw V) : Finset (Fin k) :=
  Finset.univ.filter fun j => (d j).isRight

def drawSlots (d : Fin k → BlockDraw V) (j : Fin k) : Slot :=
  match d j with
  | .inl _ => .first
  | .inr ia => decodeSlot ia.1

def drawCoefficients (d : Fin k → BlockDraw V) (z : V) :
    RawCoefficients (singletonPositions d) V
  | none => z
  | some (.inl (j, i)) =>
      match d j.val with
      | .inl ab => if i = 0 then ab.1 else ab.2
      | .inr _ => 0
  | some (.inr j) =>
      match d j.val with
      | .inl _ => 0
      | .inr ia => ia.2

def paddedMap (rhs : Fin k → Bool) (d : Fin k → BlockDraw V) (z : V) :
    ActualHomogeneous.E k →ₗ[F2] V :=
  (rawMap (singletonPositions d) V (drawCoefficients d z)).comp
    (rawProjection rhs (singletonPositions d) (drawSlots d))

omit [Module F2 V] in
theorem ambientCoefficients_draw (d : Fin k → BlockDraw V) (z : V) :
    ambientCoefficients (singletonPositions d) V (drawCoefficients d z) (drawSlots d) =
      fun j => blockAmbient (d j) := by
  funext j i
  cases hd : d j with
  | inl ab =>
      fin_cases i <;>
        simp [ambientCoefficients, singletonPositions, drawCoefficients, blockAmbient, hd]
  | inr ia =>
      simp [ambientCoefficients, singletonPositions, drawCoefficients, drawSlots,
        blockAmbient, hd, slotIndex_decodeSlot, Pi.single_apply]

def interceptShift (rhs : Fin k → Bool) (d : Fin k → BlockDraw V) : V :=
  ∑ j, ofBit (rhs j) • blockThird (d j)

theorem paddedMap_toCoefficients (rhs : Fin k → Bool) (d : Fin k → BlockDraw V)
    (z : V) :
    ActualEnumeration.toCoefficients k V (paddedMap rhs d z) =
      (z + interceptShift rhs d, fun j => blockSlopes (d j)) := by
  have hrep := raw_represents rhs (singletonPositions d) V (drawCoefficients d z) (drawSlots d)
  rw [ambientCoefficients_draw] at hrep
  have hc := ActualCanonical.extension_coefficients _ _ _ _ hrep
  have hmap : paddedMap rhs d z =
      freePullback rhs (singletonPositions d) V (drawCoefficients d z) (drawSlots d) := by
    unfold paddedMap
    rw [rawMap_pullback, coefficients_rawMap]
  rw [hmap]
  apply Prod.ext
  · exact hc.1
  · funext j
    exact Prod.ext (hc.2 j).1 (hc.2 j).2

theorem uniform_rawMaps [Fintype V] (J : Finset (Fin k))
    (H : (RawPoint J →ₗ[F2] V) → ℝ) :
    (𝔼 gamma : RawCoefficients J V, H (rawMap J V gamma)) = 𝔼 Y, H Y := by
  exact Fintype.expect_equiv (rawMapEquiv J V) _ H (fun _ => rfl)

abbrev RawTuple (J : Finset (Fin k)) (V : Type) :=
  V × ((PositionOutside J → V × V) × (PositionInside J → V))

def rawTupleEquiv (J : Finset (Fin k)) : RawTuple J V ≃ RawCoefficients J V where
  toFun a
    | none => a.1
    | some (.inl (j, i)) => if i = 0 then (a.2.1 j).1 else (a.2.1 j).2
    | some (.inr j) => a.2.2 j
  invFun gamma := ⟨gamma none,
    ⟨(fun j => (gamma (some (.inl (j, 0))), gamma (some (.inl (j, 1))))),
      (fun j => gamma (some (.inr j)))⟩⟩
  left_inv a := by
    apply Prod.ext rfl
    apply Prod.ext
    · funext j
      rfl
    · rfl
  right_inv gamma := by
    funext s
    rcases s with _ | (⟨j, i⟩ | j)
    · rfl
    · fin_cases i <;> rfl
    · rfl

def tupleDraw (J : Finset (Fin k)) (slot : Fin k → Slot) (a : RawTuple J V)
    (j : Fin k) : BlockDraw V :=
  if hj : j ∈ J then .inr (ConcreteExtraction.slotIndex (slot j), a.2.2 ⟨j, hj⟩)
  else .inl (a.2.1 ⟨j, hj⟩)

omit [Module F2 V] in
theorem tupleDraw_ambient (J : Finset (Fin k)) (slot : Fin k → Slot)
    (a : RawTuple J V) :
    (fun j => blockAmbient (tupleDraw J slot a j)) =
      ambientCoefficients J V (rawTupleEquiv J a) slot := by
  funext j i
  by_cases hj : j ∈ J
  · simp [tupleDraw, hj, blockAmbient, ambientCoefficients, rawTupleEquiv, Pi.single_apply]
  · fin_cases i <;>
      simp [tupleDraw, hj, blockAmbient, ambientCoefficients, rawTupleEquiv]

theorem paddedMap_tupleDraw (rhs : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) (a : RawTuple J V) :
    paddedMap rhs (tupleDraw J slot a) a.1 =
      (rawMap J V (rawTupleEquiv J a)).comp (rawProjection rhs J slot) := by
  have hr := raw_represents rhs J V (rawTupleEquiv J a) slot
  rw [← tupleDraw_ambient] at hr
  have hc := ActualCanonical.extension_coefficients _ _ _ _ hr
  apply (ActualEnumeration.coefficientEquiv k V).symm.injective
  change ActualEnumeration.toCoefficients k V _ = ActualEnumeration.toCoefficients k V _
  rw [paddedMap_toCoefficients, rawMap_pullback, coefficients_rawMap]
  apply Prod.ext
  · exact hc.1.symm
  · funext j
    exact Prod.ext (hc.2 j).1.symm (hc.2 j).2.symm

theorem uniform_fixed_projection_tuple [Fintype V] (rhs : Fin k → Bool)
    (J : Finset (Fin k)) (slot : Fin k → Slot)
    (H : (ActualHomogeneous.E k →ₗ[F2] V) → ℝ) :
    (𝔼 a : RawTuple J V, H (paddedMap rhs (tupleDraw J slot a) a.1)) =
      𝔼 Y : RawPoint J →ₗ[F2] V, H (Y.comp (rawProjection rhs J slot)) := by
  simp_rw [paddedMap_tupleDraw]
  exact Fintype.expect_equiv ((rawTupleEquiv J).trans (rawMapEquiv J V)) _ _ (fun _ => rfl)


variable [Fintype V]

def blockWeights (β : ℝ) : BlockDraw V → ℝ
  | .inl ab => (1 - β) * uniformWeights (V × V) ab
  | .inr ia => (β / 3) * uniformWeights V ia.2

omit [Module F2 V] in
theorem blockWeights_isProbability (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    DFVSGames.Foundations.Information.IsProbability (blockWeights (V := V) β) := by
  constructor
  · intro d
    cases d with
    | inl ab => exact mul_nonneg (sub_nonneg.mpr hβ') (uniformWeights_pos ab).le
    | inr ia => exact mul_nonneg (div_nonneg hβ (by norm_num)) (uniformWeights_pos ia.2).le
  · rw [Fintype.sum_sum_type]
    simp only [blockWeights, ← Finset.mul_sum,
      (uniformWeights_isProbability (α := V × V)).2, mul_one, Fintype.sum_prod_type,
      (uniformWeights_isProbability (α := V)).2]
    simp

omit [Module F2 V] in
theorem blockWeights_slopes (β : ℝ) (ab : V × V) :
    pushforwardWeight (blockWeights (V := V) β) blockSlopes ab =
      mixture β (singletonPairWeights V) ab := by
  have hfull : (∑ x : V × V, if blockSlopes (.inl x) = ab then
        blockWeights β (.inl x) else 0) = (1 - β) * uniformWeights (V × V) ab := by
    simp [blockWeights]
  have hsingle : (∑ ia : Fin 3 × V, if blockSlopes (.inr ia) = ab then
        blockWeights β (.inr ia) else 0) = β * singletonSamplerWeights V ab := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_three]
    simp only [blockSlopes_first, blockSlopes_second,
      blockSlopes_third, blockWeights]
    have hfactor (f : V → V × V) :
        (∑ a : V, if f a = ab then β / 3 * uniformWeights V a else 0) =
          (β / 3) * ∑ a : V, if f a = ab then uniformWeights V a else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split <;> simp_all
    simp only [hfactor, singletonSamplerWeights]
    ring
  unfold pushforwardWeight
  rw [Fintype.sum_sum_type]
  calc
    _ = (∑ x : V × V, if blockSlopes (.inl x) = ab then blockWeights β (.inl x) else 0) +
        (∑ ia : Fin 3 × V, if blockSlopes (.inr ia) = ab then blockWeights β (.inr ia) else 0) := by
      congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> split_ifs <;> rfl
    _ = _ := by rw [hfull, hsingle, singletonSamplerWeights_eq]; rfl

def drawWeights (β : ℝ) (k : ℕ) : ((Fin k → BlockDraw V) × V) → ℝ :=
  fun dz => independentWeights (blockWeights β) k dz.1 * uniformWeights V dz.2

def paddedWeights (rhs : Fin k → Bool) (β : ℝ) : ActualEnumeration.Coefficients k V → ℝ :=
  pushforwardWeight (drawWeights β k)
    (fun dz => ActualEnumeration.toCoefficients k V (paddedMap rhs dz.1 dz.2))

theorem paddedWeights_eq (rhs : Fin k → Bool) (β : ℝ)
    (a : ActualEnumeration.Coefficients k V) :
    paddedWeights rhs β a = uniformWeights V a.1 *
      independentWeights (mixture β (singletonPairWeights V)) k a.2 := by
  rcases a with ⟨z, slopes⟩
  unfold paddedWeights
  simp_rw [paddedMap_toCoefficients]
  unfold drawWeights
  have hj := pushforwardWeight_joint_uniform_intercept
    (independentWeights (blockWeights (V := V) β) k)
    (fun d j => blockSlopes (d j)) (interceptShift rhs) z slopes
  calc
    _ = uniformWeights V z * pushforwardWeight
        (independentWeights (blockWeights (V := V) β) k)
        (fun d j => blockSlopes (d j)) slopes := by
      convert hj using 1
    _ = _ := by
      rw [pushforwardWeight_pi]
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      exact blockWeights_slopes β (slopes j)

theorem uniformWeights_prod {A B : Type*} [Fintype A] [Fintype B] (ab : A × B) :
    uniformWeights (A × B) ab = uniformWeights A ab.1 * uniformWeights B ab.2 := by
  simp [uniformWeights, Fintype.card_prod, Nat.cast_mul, one_div, mul_comm]

theorem totalVariation_uniform_front {A B : Type*} [Fintype A] [Nonempty A] [Fintype B]
    (p q : B → ℝ) :
    DFVSGames.Foundations.Information.totalVariation
      (fun ab : A × B => uniformWeights A ab.1 * p ab.2)
      (fun ab : A × B => uniformWeights A ab.1 * q ab.2) =
        DFVSGames.Foundations.Information.totalVariation p q := by
  unfold DFVSGames.Foundations.Information.totalVariation
  rw [Fintype.sum_prod_type]
  simp only [← mul_sub, abs_mul, abs_of_nonneg (uniformWeights_pos _).le,
    ← Finset.mul_sum, ← Finset.sum_mul, (uniformWeights_isProbability (α := A)).2, one_mul]

theorem paddedWeights_totalVariation_eq_slope (rhs : Fin k → Bool) (β : ℝ) :
    DFVSGames.Foundations.Information.totalVariation (paddedWeights (V := V) rhs β)
      (uniformWeights (ActualEnumeration.Coefficients k V)) =
        DFVSGames.Foundations.Information.totalVariation
          (independentWeights (mixture β (singletonPairWeights V)) k)
          (uniformWeights (Fin k → V × V)) := by
  have hp : paddedWeights (V := V) rhs β = fun a => uniformWeights V a.1 *
      independentWeights (mixture β (singletonPairWeights V)) k a.2 := by
    funext a
    exact paddedWeights_eq rhs β a
  have hu : uniformWeights (ActualEnumeration.Coefficients k V) =
      fun a => uniformWeights V a.1 * uniformWeights (Fin k → V × V) a.2 := by
    funext a
    exact uniformWeights_prod a
  rw [hp, hu, totalVariation_uniform_front]

theorem paddedWeights_totalVariation (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    DFVSGames.Foundations.Information.totalVariation (paddedWeights (V := V) rhs β)
      (uniformWeights (ActualEnumeration.Coefficients k V)) ≤
        Real.sqrt ((1 + β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ^ k - 1) / 2 := by
  rw [paddedWeights_totalVariation_eq_slope]
  exact paddedSlope_totalVariation V β hβ hβ' k

abbrev ProjectionChoice := Option (Fin 3)

def choiceWeight (β : ℝ) : ProjectionChoice → ℝ
  | none => 1 - β
  | some _ => β / 3

theorem choiceWeight_isProbability (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    DFVSGames.Foundations.Information.IsProbability (choiceWeight β) := by
  constructor
  · intro c
    cases c with
    | none => exact sub_nonneg.mpr hβ'
    | some i => exact div_nonneg hβ (by norm_num)
  · rw [Fintype.sum_option]
    simp [choiceWeight]
    ring

def blockKernel : ProjectionChoice → BlockDraw V → ℝ
  | none, .inl ab => uniformWeights (V × V) ab
  | some i, .inr ja => if i = ja.1 then uniformWeights V ja.2 else 0
  | _, _ => 0

def choiceTupleWeight (β : ℝ) (c : Fin k → ProjectionChoice) : ℝ :=
  ∏ j, choiceWeight β (c j)

theorem choiceTupleWeight_isProbability (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    DFVSGames.Foundations.Information.IsProbability (choiceTupleWeight (k := k) β) := by
  exact independentWeights_isProbability (choiceWeight β)
    (choiceWeight_isProbability β hβ hβ') k

def kernelTupleWeight (c : Fin k → ProjectionChoice) (d : Fin k → BlockDraw V) : ℝ :=
  ∏ j, blockKernel (c j) (d j)

omit [AddCommGroup V] [Module F2 V] in
theorem blockWeights_choice_mixture (β : ℝ) (d : BlockDraw V) :
    blockWeights β d = ∑ c : ProjectionChoice, choiceWeight β c * blockKernel c d := by
  cases d <;>
    simp [Fintype.sum_option, choiceWeight, blockKernel, blockWeights, mul_ite]

omit [AddCommGroup V] [Module F2 V] in
theorem independent_blockWeights_mixture (β : ℝ) (d : Fin k → BlockDraw V) :
    independentWeights (blockWeights β) k d =
      ∑ c : Fin k → ProjectionChoice, choiceTupleWeight β c * kernelTupleWeight c d := by
  unfold independentWeights choiceTupleWeight kernelTupleWeight
  simp_rw [blockWeights_choice_mixture]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact Finset.prod_mul_distrib

omit [AddCommGroup V] [Module F2 V] in
theorem drawWeights_choice_mixture (β : ℝ) (dz : (Fin k → BlockDraw V) × V) :
    drawWeights β k dz = ∑ c : Fin k → ProjectionChoice,
      choiceTupleWeight β c * (kernelTupleWeight c dz.1 * uniformWeights V dz.2) := by
  rw [drawWeights, independent_blockWeights_mixture, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

omit [AddCommGroup V] [Module F2 V] in
theorem draw_expectation_choice_mixture (β : ℝ)
    (H : ((Fin k → BlockDraw V) × V) → ℝ) :
    (∑ dz, drawWeights β k dz * H dz) =
      ∑ c : Fin k → ProjectionChoice, choiceTupleWeight β c *
        ∑ dz, (kernelTupleWeight c dz.1 * uniformWeights V dz.2) * H dz := by
  simp_rw [drawWeights_choice_mixture, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro dz _
  ring

def ChoiceValue (V : Type) : ProjectionChoice → Type
  | none => V × V
  | some _ => V

instance choiceValueFintype (c : ProjectionChoice) : Fintype (ChoiceValue V c) := by
  cases c <;> dsimp [ChoiceValue] <;> infer_instance

def choiceEmbed : (c : ProjectionChoice) → ChoiceValue V c → BlockDraw V
  | none, ab => .inl ab
  | some i, a => .inr (i, a)

omit [AddCommGroup V] [Module F2 V] in
theorem blockKernel_uniform_pushforward (c : ProjectionChoice) (d : BlockDraw V) :
    blockKernel c d =
      pushforwardWeight (uniformWeights (ChoiceValue V c)) (choiceEmbed c) d := by
  cases c with
  | none =>
      cases d <;> simp [blockKernel, pushforwardWeight, choiceEmbed, ChoiceValue]
      exact fun h => False.elim (h (Finset.mem_univ _))
  | some i =>
      cases d with
      | inl ab => simp [blockKernel, pushforwardWeight, choiceEmbed, ChoiceValue]
      | inr ja =>
          rcases ja with ⟨j, a⟩
          by_cases h : i = j <;>
            simp [blockKernel, pushforwardWeight, choiceEmbed, ChoiceValue,
              Prod.mk.injEq, h]
          exact fun h => False.elim (h (Finset.mem_univ _))

theorem pushforwardWeight_pi_dep {I B : Type*} [Fintype I]
    {A : I → Type*} [∀ i, Fintype (A i)]
    (p : (i : I) → A i → ℝ) (f : (i : I) → A i → B) (ys : I → B) :
    pushforwardWeight (fun xs : ∀ i, A i => ∏ i, p i (xs i))
      (fun xs : ∀ i, A i => fun i => f i (xs i)) ys =
      ∏ i, pushforwardWeight (p i) (f i) (ys i) := by
  classical
  simp only [pushforwardWeight]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro xs _
  simp only [Fintype.prod_ite_zero, funext_iff]

theorem uniformWeights_pi {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, Fintype (A i)] (x : ∀ i, A i) :
    uniformWeights (∀ i, A i) x = ∏ i, uniformWeights (A i) (x i) := by
  simp [uniformWeights, Fintype.card_pi, Nat.cast_prod, one_div,
    Finset.prod_inv_distrib]

omit [AddCommGroup V] [Module F2 V] in
theorem kernelTuple_uniform_pushforward (c : Fin k → ProjectionChoice)
    (d : Fin k → BlockDraw V) :
    kernelTupleWeight c d =
      pushforwardWeight (uniformWeights (∀ j, ChoiceValue V (c j)))
        (fun f j => choiceEmbed (c j) (f j)) d := by
  unfold kernelTupleWeight
  simp_rw [blockKernel_uniform_pushforward]
  rw [← pushforwardWeight_pi_dep]
  have hp : (fun f : ∀ j, ChoiceValue V (c j) =>
      ∏ j, uniformWeights (ChoiceValue V (c j)) (f j)) =
      uniformWeights (∀ j, ChoiceValue V (c j)) := by
    funext f
    simp [uniformWeights, Fintype.card_pi, Nat.cast_prod, one_div,
      Finset.prod_inv_distrib]
  rw [hp]
  congr 1 ; exact Subsingleton.elim _ _

theorem sum_pushforwardWeight_mul {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (f : A → B) (H : B → ℝ) :
    (∑ b, pushforwardWeight p f b * H b) = ∑ a, p a * H (f a) := by
  classical
  simp only [pushforwardWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

theorem sum_uniformWeights_mul {A : Type*} [Fintype A] (H : A → ℝ) :
    (∑ a, uniformWeights A a * H a) = 𝔼 a, H a := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [uniformWeights, ← Finset.mul_sum]
  ring

def choiceMask (c : Fin k → ProjectionChoice) : Finset (Fin k) :=
  Finset.univ.filter fun j => (c j).isSome

def choiceSlot : ProjectionChoice → Slot
  | none => .first
  | some i => decodeSlot i

def choiceSlots (c : Fin k → ProjectionChoice) (j : Fin k) : Slot :=
  choiceSlot (c j)

theorem not_mem_choiceMask (c : Fin k → ProjectionChoice) (j : Fin k) :
    j ∉ choiceMask c ↔ c j = none := by
  cases h : c j <;> simp [choiceMask, h]

def fullChoiceValue : (c : ProjectionChoice) → ChoiceValue V c → V × V
  | none, x => x
  | some _, _ => (0, 0)

def singleChoiceValue : (c : ProjectionChoice) → ChoiceValue V c → V
  | none, _ => 0
  | some _, x => x

def readChoiceValue (q : ProjectionChoice) (full : q = none → V × V)
    (single : q.isSome = true → V) : ChoiceValue V q := by
  cases q with
  | none => exact full rfl
  | some i => exact single rfl

omit [Module F2 V] [Fintype V] in
theorem readChoiceValue_roundtrip (q : ProjectionChoice) (v : ChoiceValue V q) :
    readChoiceValue q (fun _ => fullChoiceValue q v)
      (fun _ => singleChoiceValue q v) = v := by
  cases q <;> rfl

omit [Module F2 V] [Fintype V] in
theorem readChoiceValue_full (q : ProjectionChoice) (full : q = none → V × V)
    (single : q.isSome = true → V) (h : q = none) :
    fullChoiceValue q (readChoiceValue q full single) = full h := by
  subst q
  rfl

omit [Module F2 V] [Fintype V] in
theorem readChoiceValue_single (q : ProjectionChoice) (full : q = none → V × V)
    (single : q.isSome = true → V) (h : q.isSome = true) :
    singleChoiceValue q (readChoiceValue q full single) = single h := by
  cases q with
  | none => simp at h
  | some i => rfl

def choiceValuesToRawTuple (c : Fin k → ProjectionChoice)
    (fz : (∀ j, ChoiceValue V (c j)) × V) : RawTuple (choiceMask c) V :=
  (fz.2,
    (fun j => fullChoiceValue (c j.val) (fz.1 j.val)),
      fun j => singleChoiceValue (c j.val) (fz.1 j.val))

def rawTupleToChoiceValues (c : Fin k → ProjectionChoice)
    (a : RawTuple (choiceMask c) V) (j : Fin k) : ChoiceValue V (c j) :=
  readChoiceValue (c j)
    (fun h => a.2.1 ⟨j, (not_mem_choiceMask c j).mpr h⟩)
    (fun h => a.2.2 ⟨j, by simpa [choiceMask] using h⟩)

def choiceValuesRawTupleEquiv (c : Fin k → ProjectionChoice) :
    ((∀ j, ChoiceValue V (c j)) × V) ≃ RawTuple (choiceMask c) V where
  toFun := choiceValuesToRawTuple c
  invFun a := (rawTupleToChoiceValues c a, a.1)
  left_inv fz := by
    apply Prod.ext
    · funext j
      exact readChoiceValue_roundtrip (c j) (fz.1 j)
    · rfl
  right_inv a := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext j
        have hc : c j.val = none := (not_mem_choiceMask c j.val).mp j.property
        exact readChoiceValue_full (c j.val) _ _ hc
      · funext j
        have hc : (c j.val).isSome = true := by
          simpa [choiceMask] using j.property
        exact readChoiceValue_single (c j.val) _ _ hc

omit [Module F2 V] [Fintype V] in
theorem restoreChoiceDraw (q : ProjectionChoice) (v : ChoiceValue V q) :
    (if q.isSome then
      Sum.inr (ConcreteExtraction.slotIndex (choiceSlot q),
          singleChoiceValue q v)
    else Sum.inl (fullChoiceValue q v)) = choiceEmbed q v := by
  cases q <;> simp [fullChoiceValue, singleChoiceValue, choiceEmbed, choiceSlot,
    slotIndex_decodeSlot]

omit [Module F2 V] [Fintype V] in
theorem tupleDraw_choiceValues (c : Fin k → ProjectionChoice)
    (fz : (∀ j, ChoiceValue V (c j)) × V) :
    tupleDraw (choiceMask c) (choiceSlots c) (choiceValuesRawTupleEquiv c fz) =
      fun j => choiceEmbed (c j) (fz.1 j) := by
  funext j
  change (if j ∈ choiceMask c then
      Sum.inr (ConcreteExtraction.slotIndex (choiceSlot (c j)),
        singleChoiceValue (c j) (fz.1 j))
    else Sum.inl (fullChoiceValue (c j) (fz.1 j))) = choiceEmbed (c j) (fz.1 j)
  simpa only [choiceMask, Finset.mem_filter,
    Finset.mem_univ, true_and] using restoreChoiceDraw (c j) (fz.1 j)

theorem fixed_choice_kernel_map_expectation
    (rhs : Fin k → Bool) (c : Fin k → ProjectionChoice)
    (H : (ActualHomogeneous.E k →ₗ[F2] V) → ℝ) :
    (∑ dz : (Fin k → BlockDraw V) × V,
      (kernelTupleWeight c dz.1 * uniformWeights V dz.2) *
        H (paddedMap rhs dz.1 dz.2)) =
      𝔼 Y : RawPoint (choiceMask c) →ₗ[F2] V,
        H (Y.comp (rawProjection rhs (choiceMask c) (choiceSlots c))) := by
  calc
    _ = ∑ d : Fin k → BlockDraw V, kernelTupleWeight c d *
        ∑ z : V, uniformWeights V z * H (paddedMap rhs d z) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = ∑ f : ∀ j, ChoiceValue V (c j), uniformWeights _ f *
        ∑ z : V, uniformWeights V z *
          H (paddedMap rhs (fun j => choiceEmbed (c j) (f j)) z) := by
      simp_rw [kernelTuple_uniform_pushforward]
      exact sum_pushforwardWeight_mul _ _ _
    _ = 𝔼 fz : (∀ j, ChoiceValue V (c j)) × V,
        H (paddedMap rhs (fun j => choiceEmbed (c j) (fz.1 j)) fz.2) := by
      rw [← sum_uniformWeights_mul, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro f _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [uniformWeights_prod]
      ring
    _ = 𝔼 a : RawTuple (choiceMask c) V,
        H (paddedMap rhs (tupleDraw (choiceMask c) (choiceSlots c) a) a.1) := by
      apply Fintype.expect_equiv (choiceValuesRawTupleEquiv c)
      intro fz
      rw [tupleDraw_choiceValues]
      rfl
    _ = _ := uniform_fixed_projection_tuple rhs (choiceMask c) (choiceSlots c) H

theorem actual_projection_mixture_expectation
    (rhs : Fin k → Bool) (β : ℝ)
    (H : (ActualHomogeneous.E k →ₗ[F2] V) → ℝ) :
    (∑ dz : (Fin k → BlockDraw V) × V,
      drawWeights β k dz * H (paddedMap rhs dz.1 dz.2)) =
      ∑ c : Fin k → ProjectionChoice, choiceTupleWeight β c *
        (𝔼 Y : RawPoint (choiceMask c) →ₗ[F2] V,
          H (Y.comp (rawProjection rhs (choiceMask c) (choiceSlots c)))) := by
  rw [draw_expectation_choice_mixture]
  apply Finset.sum_congr rfl
  intro c _
  rw [fixed_choice_kernel_map_expectation]

theorem uniform_rawMap_pair {K W : Type}
    [AddCommGroup K] [Module F2 K] [Fintype K]
    [AddCommGroup W] [Module F2 W] [Fintype W]
    (J : Finset (Fin k)) (H : (RawPoint J →ₗ[F2] K × W) → ℝ) :
    (𝔼 MT : (RawPoint J →ₗ[F2] K) × (RawPoint J →ₗ[F2] W),
      H (MT.1.prod MT.2)) = 𝔼 Y : RawPoint J →ₗ[F2] K × W, H Y := by
  exact Fintype.expect_equiv (LinearMap.prodEquiv F2).toEquiv _ H (fun _ => rfl)


variable [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

def paddedMapWeights (rhs : Fin k → Bool) (β : ℝ) :
    (ActualHomogeneous.E k →ₗ[F2] V) → ℝ :=
  pushforwardWeight (drawWeights β k) (fun dz => paddedMap rhs dz.1 dz.2)

omit [Fintype (ActualHomogeneous.E k →ₗ[F2] V)] in
theorem paddedMapWeights_eq (rhs : Fin k → Bool) (β : ℝ)
    (X : ActualHomogeneous.E k →ₗ[F2] V) :
    paddedMapWeights rhs β X =
      paddedWeights rhs β (ActualEnumeration.toCoefficients k V X) := by
  unfold paddedMapWeights paddedWeights pushforwardWeight
  apply Finset.sum_congr rfl
  intro dz _
  have he : paddedMap rhs dz.1 dz.2 = X ↔
      ActualEnumeration.toCoefficients k V (paddedMap rhs dz.1 dz.2) =
        ActualEnumeration.toCoefficients k V X :=
    (ActualEnumeration.coefficientEquiv k V).symm.injective.eq_iff.symm
  simp only [he]
  split_ifs <;> rfl

theorem uniform_sourceMap_coordinates (a : ActualEnumeration.Coefficients k V) :
    uniformWeights (ActualHomogeneous.E k →ₗ[F2] V)
      (ActualEnumeration.coefficientEquiv k V a) =
        uniformWeights (ActualEnumeration.Coefficients k V) a := by
  simp only [uniformWeights]
  rw [Fintype.card_congr (ActualEnumeration.coefficientEquiv k V)]

theorem paddedMapWeights_totalVariation_eq_slope (rhs : Fin k → Bool) (β : ℝ) :
    DFVSGames.Foundations.Information.totalVariation (paddedMapWeights (V := V) rhs β)
      (uniformWeights (ActualHomogeneous.E k →ₗ[F2] V)) =
        DFVSGames.Foundations.Information.totalVariation
          (independentWeights (mixture β (singletonPairWeights V)) k)
          (uniformWeights (Fin k → V × V)) := by
  have heq : DFVSGames.Foundations.Information.totalVariation
      (paddedMapWeights (V := V) rhs β)
      (uniformWeights (ActualHomogeneous.E k →ₗ[F2] V)) =
      DFVSGames.Foundations.Information.totalVariation
        (paddedWeights (V := V) rhs β)
        (uniformWeights (ActualEnumeration.Coefficients k V)) := by
    unfold DFVSGames.Foundations.Information.totalVariation
    rw [← (ActualEnumeration.coefficientEquiv k V).sum_comp]
    simp only [paddedMapWeights_eq,
      ActualEnumeration.coefficientEquiv, Equiv.coe_fn_mk,
      ActualEnumeration.to_fromCoefficients]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [show uniformWeights (ActualHomogeneous.E k →ₗ[F2] V)
      (ActualEnumeration.fromCoefficients k V a) =
        uniformWeights (ActualEnumeration.Coefficients k V) a from
          uniform_sourceMap_coordinates a]
  rw [heq]
  exact paddedWeights_totalVariation_eq_slope rhs β

theorem paddedMapWeights_totalVariation (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    DFVSGames.Foundations.Information.totalVariation (paddedMapWeights (V := V) rhs β)
      (uniformWeights (ActualHomogeneous.E k →ₗ[F2] V)) ≤
        Real.sqrt ((1 + β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ^ k - 1) / 2 := by
  rw [paddedMapWeights_totalVariation_eq_slope]
  exact paddedSlope_totalVariation V β hβ hβ' k


end
end DFVSGames.Decoder.PaddedLaw

end OAI
