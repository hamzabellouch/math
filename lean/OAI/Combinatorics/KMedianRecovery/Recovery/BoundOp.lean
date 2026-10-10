import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Pack8
import OAI.Combinatorics.KMedianRecovery.Recovery.Pack9

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryDecision
open WordList RationalMatrix

def boundOp (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix x)
noncomputable def boundOp_computes : PolyComputes boundOp := discardPrefix_computes.pair extractPrefix_computes
lemma boundOp_pair {n : ℕ} (b : ℚ) (a : Fin n → ℚ) :
    boundOp (pairBits (BinaryRational.encode b,rowEncode a))=BinaryRow.encode ⟨a,b⟩ := by
  simp only [boundOp,extractPrefix_pairBits,discardPrefix_pairBits,BinaryRow.encode]
noncomputable def boxShape (s : Bool) (x : List Bool) : List Bool :=
  BinaryEllipsoidInitial.run (pairBits (nword x,BinaryRational.encode (if s then 1 else -1)))
noncomputable def boxShape_computes (s : Bool) : PolyComputes (boxShape s) := by
  unfold boxShape
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (nword input,BinaryRational.encode (if s then 1 else -1)))
      (g:=BinaryEllipsoidInitial.run)
      (nword_computes.pair (const_computes (BinaryRational.encode (if s then 1 else -1))))
      BinaryEllipsoidInitial.run_computes)
lemma boxShape_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) (s : Bool) :
    boxShape s (pack A b B H)=RationalMatrix.encode (fun i j=>(boundedMatrix A (.inr (s,i)) j:ℚ)) := by
  rw [boxShape,(projections_pack A b B H).1]
  change BinaryEllipsoidInitial.run (BinaryEllipsoidInitial.pack n (if s then 1 else -1))=_
  rw [BinaryEllipsoidInitial.run_pack]
  congr 1
  ext i j
  simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,boundedMatrix]
  by_cases hij : i=j
  · subst j; cases s <;> simp
  · have hji : j≠i := Ne.symm hij
    simp only [hij,hji,ite_false,Int.cast_zero,mul_zero]
noncomputable def boxWords (s : Bool) (x : List Bool) : List Bool :=
  mapWith boundOp (pairBits (BinaryRational.encode (value (bound x):ℚ),boxShape s x))
noncomputable def boxWords_computes (s : Bool) : PolyComputes (boxWords s) := by
  unfold boxWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (BinaryRational.encode (value (bound input):ℚ),boxShape s input))
      (g:=mapWith boundOp)
      ((RatOps.nat bound_computes).pair (boxShape_computes s))
      (mapWith_computes boundOp_computes))
lemma boxWords_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) (s : Bool) :
    boxWords s (pack A b B H)=BinaryRow.rowsEncode (List.ofFn (fun i=>integerRow (boundedMatrix A (.inr (s,i))) B)) := by
  simp only [boxWords,(projections_pack A b B H).2.2.1,value_bits,boxShape_pack,RationalMatrix.encode,
    mapWith_ofFn,boundOp_pair,BinaryRow.rowsEncode,List.map_ofFn,Function.comp_def,integerRow,Int.cast_natCast]
noncomputable def boundedWords (x : List Bool) : List Bool := rows x++boxWords true x++boxWords false x
noncomputable def boundedWords_computes : PolyComputes boundedWords :=
  (rows_computes.append (boxWords_computes true)).append (boxWords_computes false)
lemma boundedWords_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    boundedWords (pack A b B H)=BinaryRow.rowsEncode (boundedRows A b B) := by
  simp only [boundedWords,(projections_pack A b B H).2.2.2.2,boxWords_pack,
    boundedRows,BinaryRow.rowsEncode,List.map_append,encode_append]

def relaxedOp (x : List Bool) : List Bool :=
  pairBits (extractPrefix (discardPrefix x),BinaryRational.encode
    (BinaryRational.decode (discardPrefix (discardPrefix x))+BinaryRational.decode (extractPrefix x)))
noncomputable def relaxedOp_computes : PolyComputes relaxedOp :=
  (discardPrefix_computes.comp extractPrefix_computes).pair
    (RatOps.add (RatOps.ofWords (discardPrefix_computes.comp discardPrefix_computes))
      (RatOps.ofWords extractPrefix_computes))
lemma relaxedOp_pair {n : ℕ} (eps : ℚ) (r : Row n) :
    relaxedOp (pairBits (BinaryRational.encode eps,BinaryRow.encode r))=BinaryRow.encode (relaxedRow eps r) := by
  simp only [relaxedOp,BinaryRow.encode,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryRational.decode_encode,relaxedRow]
noncomputable def relaxedWords (x : List Bool) : List Bool := mapWith relaxedOp (pairBits (epsilon x,boundedWords x))
noncomputable def relaxedWords_computes : PolyComputes relaxedWords := by
  unfold relaxedWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (epsilon input,boundedWords input))
      (g:=mapWith relaxedOp) (epsilon_computes.pair boundedWords_computes)
      (mapWith_computes relaxedOp_computes))
lemma relaxedWords_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    relaxedWords (pack A b B H)=BinaryRow.rowsEncode (relaxedRows (gapEpsilon m n H) (boundedRows A b B)) := by
  simp only [relaxedWords,epsilon_pack,boundedWords_pack,BinaryRow.rowsEncode,mapWith_encode,
    List.map_map,Function.comp_def,relaxedOp_pair,relaxedRows]
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (nword x,pairBits (precision x,pairBits (radiusPrecision x,pairBits (radius x,relaxedWords x))))
noncomputable def prepared_computes : PolyComputes prepared :=
  nword_computes.pair (precision_computes.pair (radiusPrecision_computes.pair (radius_computes.pair relaxedWords_computes)))
lemma prepared_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    prepared (pack A b B H)=BinaryWeakSolve.pack n (precisionLog m n H) (radiusLog n B) (n*(B+1))
      (relaxedRows (gapEpsilon m n H) (boundedRows A b B)) := by
  simp only [prepared,(projections_pack A b B H).1,precision_pack,radiusPrecision_pack,radius_pack,
    relaxedWords_pack,BinaryWeakSolve.pack]
noncomputable def solved : List Bool → List Bool := BinaryWeakSolve.run ∘ prepared
noncomputable def solved_computes : PolyComputes solved := prepared_computes.comp BinaryWeakSolve.run_computes
noncomputable def run (x : List Bool) : List Bool := [!decide (solved x=[])]
noncomputable def run_computes : PolyComputes run := by
  have hh := (solved_computes.comp isEmpty_computes).cond (const_computes [false]) (const_computes [true])
  unfold run
  convert hh using 1
  funext x
  by_cases h : solved x=[] <;> simp [h]
lemma run_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) (hn : 2≤n) :
    run (pack A b B H)=[integerDecide A b B H] := by
  have hR : 1≤n*(B+1) := by nlinarith
  simp only [run,solved,Function.comp_apply,prepared_pack,BinaryWeakSolve.run_pack _ _ _ _ _ hn hR,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one,integerDecide]
  cases weakSolve (relaxedRows (gapEpsilon m n H) (boundedRows A b B)) ((n:ℚ)*(B+1))
    (precisionLog m n H) (radiusLog n B) <;> simp [WordList.Find.optionEncode]
lemma run_correct {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ)
    (hn : 2≤n) (hBH : B+1≤H) (hA : ∀ r j, |A r j|≤(H:ℤ)) (hb : ∀ r, |b r|≤(H:ℤ)) :
    run (pack A b B H)=[true] ↔
      ∃ x : Fin n → ℝ, (∀ r, (∑ j, (A r j:ℝ)*x j)≤(b r:ℝ)) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  rw [run_pack A b B H hn]
  simpa only [List.cons.injEq,and_true] using integerDecide_correct A b B H hn hBH hA hb
end BinaryDecision
end
open WordOperations BinaryArithmetic
namespace NaturalArray
open WordList

def signedOp (x : List Bool) : List Bool := Signed.encode (value (discardPrefix x):ℤ)
noncomputable def signedOp_computes : PolyComputes signedOp := Signed.cast_computes discardPrefix_computes
noncomputable def sumWords (x : List Bool) : List Bool :=
  (IntegerArray.sumWords (mapWith signedOp (pairBits ([],x)))).tail
noncomputable def sumWords_computes : PolyComputes sumWords := by
  unfold sumWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=mapWith signedOp ∘ (fun input=>pairBits ([],input)))
      (g:=List.tail ∘ IntegerArray.sumWords)
      (PolyComputes.comp (f:=fun input=>pairBits ([],input)) (g:=mapWith signedOp)
        ((const_computes []).pair id_computes) (mapWith_computes signedOp_computes))
      (PolyComputes.comp (f:=IntegerArray.sumWords) (g:=List.tail)
        IntegerArray.sumWords_computes WordOperations.tail_computes))
lemma sumWords_encode (xs : List ℕ) : sumWords (encode xs)=xs.sum.bits := by
  simp only [sumWords,encode,mapWith_encode,List.map_map,Function.comp_def,signedOp,discardPrefix_pairBits,value_bits]
  have hh := IntegerArray.sumWords_encode (xs.map (fun n : ℕ => (n:ℤ)))
  simp only [IntegerArray.encode,List.map_map,Function.comp_def] at hh
  rw [hh]
  clear hh
  have hs : (xs.map (fun n : ℕ => (n:ℤ))).sum=(xs.sum:ℤ) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih,Nat.cast_add]
  rw [hs,Signed.encode,List.tail_cons,Int.natAbs_natCast]
end NaturalArray
end MetricKMedianRecovery.BitMachine

end OAI
