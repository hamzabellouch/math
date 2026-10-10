import Mathlib
import OAI.Combinatorics.KMedianRecovery.Model

namespace OAI

namespace MetricKMedianRecovery.RationalMetricInput

def readUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: tail => some (0,tail)
  | true :: tail => do
      let (n,rest) ← readUnary tail
      pure (n+1,rest)

def readBlock (n : ℕ) (bits : List Bool) : Option (List Bool × List Bool) :=
  if n ≤ bits.length then some (bits.take n,bits.drop n) else none

def valueBits (l : List Bool) : ℕ := l.foldr Nat.bit 0

def readNat (bits : List Bool) : Option (ℕ × List Bool) := do
  let (n,tail) ← readUnary bits
  let (digits,rest) ← readBlock n tail
  pure (valueBits digits,rest)

lemma readUnary_code (n : ℕ) (tail : List Bool) :
    readUnary (List.replicate n true ++ false::tail) = some (n,tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,readUnary,ih]; rfl

lemma readBlock_code (l tail : List Bool) : readBlock l.length (l++tail) = some (l,tail) := by
  simp [readBlock]

lemma valueBits_code (n : ℕ) : valueBits (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => simp only [Nat.bits_append_bit n b h,valueBits,List.foldr_cons] at *; rw [ih]

lemma readNat_code (n : ℕ) (tail : List Bool) :
    readNat (natBits n ++ tail) = some (n,tail) := by
  simp only [natBits,List.append_assoc,List.cons_append]
  unfold readNat
  rw [readUnary_code]
  dsimp
  rw [readBlock_code]
  dsimp
  rw [valueBits_code]

def signedNumerator (neg : Bool) (n : ℕ) : ℤ := if neg then -(n:ℤ) else n

def readRational : List Bool → Option (ℚ × List Bool)
  | [] => none
  | sign::tail => do
      let (n,tail') ← readNat tail
      let (d,rest) ← readNat tail'
      pure ((signedNumerator sign n:ℚ)/(d:ℚ),rest)

lemma signedNumerator_code (r : ℚ) : signedNumerator (decide (r<0)) r.num.natAbs = r.num := by
  by_cases h : r < 0
  · have hn : r.num < 0 := lt_of_not_ge (fun hz => not_le_of_gt h (Rat.num_nonneg.mp hz))
    simpa [signedNumerator,h] using (Int.eq_neg_natAbs_of_nonpos hn.le).symm
  · have hn : 0 ≤ r.num := Rat.num_nonneg.mpr (le_of_not_gt h)
    simp [signedNumerator,h,Int.natAbs_of_nonneg hn]

lemma readRational_code (r : ℚ) (tail : List Bool) :
    readRational (rationalBits r ++ tail) = some (r,tail) := by
  simp only [rationalBits,List.append_assoc,List.cons_append,List.nil_append]
  rw [readRational,readNat_code]
  dsimp
  rw [readNat_code]
  dsimp
  rw [signedNumerator_code,Rat.num_div_den]

def readMany {α : Type} (read : List Bool → Option (α × List Bool)) :
    ℕ → List Bool → Option (List α × List Bool)
  | 0,bits => some ([],bits)
  | n+1,bits => do
      let (a,tail) ← read bits
      let (as,rest) ← readMany read n tail
      pure (a::as,rest)

lemma readMany_code {α : Type} (read : List Bool → Option (α × List Bool)) (enc : α → List Bool)
    (h : ∀ a tail, read (enc a ++ tail) = some (a,tail)) (l : List α) (tail : List Bool) :
    readMany read l.length (l.flatMap enc ++ tail) = some (l,tail) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.length_cons,List.flatMap_cons,List.append_assoc,readMany,h]
    dsimp
    rw [ih]
    rfl

def readInput (bits : List Bool) : Option (ℕ × ℕ × List Bool × List Bool × List (List ℚ)) := do
  let (n,tail) ← readNat bits
  let (k,tail) ← readNat tail
  let (clients,tail) ← readBlock n tail
  let (facilities,tail) ← readBlock n tail
  let (matrix,tail) ← readMany (readMany readRational n) n tail
  if tail = [] then pure (n,k,clients,facilities,matrix) else none

end MetricKMedianRecovery.RationalMetricInput
namespace MetricKMedianRecovery.RationalMetricInput

lemma readMany_code_on {α : Type} (read : List Bool → Option (α × List Bool)) (enc : α → List Bool)
    (l : List α) (h : ∀ a ∈ l, ∀ tail, read (enc a ++ tail) = some (a,tail))
    (tail : List Bool) :
    readMany read l.length (l.flatMap enc ++ tail) = some (l,tail) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.length_cons,List.flatMap_cons,List.append_assoc,readMany,h a (by simp)]
    dsimp
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

lemma readRationalRow_code {n : ℕ} (row : Fin n → ℚ) (tail : List Bool) :
    readMany readRational n ((List.ofFn (fun j => rationalBits (row j))).flatten ++ tail) =
      some (List.ofFn row,tail) := by
  simpa only [List.length_ofFn,List.flatMap, List.map_ofFn,Function.comp_def] using
    readMany_code readRational rationalBits readRational_code (List.ofFn row) tail

lemma readRationalMatrix_code {n : ℕ} (matrix : Fin n → Fin n → ℚ) (tail : List Bool) :
    readMany (readMany readRational n) n
      ((List.ofFn (fun i => (List.ofFn (fun j => rationalBits (matrix i j))).flatten)).flatten ++ tail) =
        some (List.ofFn (fun i => List.ofFn (matrix i)),tail) := by
  have h := readMany_code_on (readMany readRational n) (fun row : List ℚ => row.flatMap rationalBits)
    (List.ofFn (fun i => List.ofFn (matrix i))) (fun row hr tail => ?_) tail
  · simpa only [List.length_ofFn,List.flatMap,List.map_ofFn,Function.comp_def] using h
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    simpa only [List.flatMap,List.map_ofFn,Function.comp_def] using readRationalRow_code (matrix i) tail

lemma readInput_code (I : RationalMetricInput) : readInput I.bits = some
    (I.pointCount,I.budget,
     List.ofFn (fun i : Fin I.pointCount => decide (i ∈ I.clients)),
     List.ofFn (fun i : Fin I.pointCount => decide (i ∈ I.facilities)),
     List.ofFn (fun i : Fin I.pointCount => List.ofFn (I.distance i))) := by
  have hblock (f : Fin I.pointCount → Bool) (tail : List Bool) :
      readBlock I.pointCount (List.ofFn f ++ tail) = some (List.ofFn f,tail) := by
    simpa only [List.length_ofFn] using readBlock_code (List.ofFn f) tail
  unfold bits readInput
  simp only [List.append_assoc]
  rw [readNat_code]
  dsimp
  rw [readNat_code]
  dsimp
  rw [hblock]
  dsimp
  rw [hblock]
  dsimp
  rw [← List.append_nil ((List.ofFn _).flatten),readRationalMatrix_code]
  rfl

end MetricKMedianRecovery.RationalMetricInput

end OAI
