import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Pack7

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open UnaryResources
namespace BinaryWeakSolve
open RationalMatrix

def pack (n p s R : ℕ) (rs : List (Row n)) : List Bool :=
  pairBits (List.replicate n true,pairBits (List.replicate p true,
    pairBits (List.replicate s true,pairBits (R.bits,BinaryRow.rowsEncode rs))))
def nword : List Bool → List Bool := extractPrefix
def rest₁ : List Bool → List Bool := discardPrefix
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest₁
def rest₃ : List Bool → List Bool := discardPrefix ∘ rest₂
def pword : List Bool → List Bool := extractPrefix ∘ rest₁
def sword : List Bool → List Bool := extractPrefix ∘ rest₂
def radius : List Bool → List Bool := extractPrefix ∘ rest₃
def rows : List Bool → List Bool := discardPrefix ∘ rest₃
noncomputable def nword_computes : PolyComputes nword := extractPrefix_computes
noncomputable def rest₁_computes : PolyComputes rest₁ := discardPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest₁_computes.comp discardPrefix_computes
noncomputable def rest₃_computes : PolyComputes rest₃ := rest₂_computes.comp discardPrefix_computes
noncomputable def pword_computes : PolyComputes pword := rest₁_computes.comp extractPrefix_computes
noncomputable def sword_computes : PolyComputes sword := rest₂_computes.comp extractPrefix_computes
noncomputable def radius_computes : PolyComputes radius := rest₃_computes.comp extractPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₃_computes.comp discardPrefix_computes
lemma projections_pack (n p s R : ℕ) (rs : List (Row n)) :
    nword (pack n p s R rs)=List.replicate n true ∧
    pword (pack n p s R rs)=List.replicate p true ∧
    sword (pack n p s R rs)=List.replicate s true ∧
    radius (pack n p s R rs)=R.bits ∧ rows (pack n p s R rs)=BinaryRow.rowsEncode rs := by
  simp only [nword,pword,sword,radius,rows,rest₁,rest₂,rest₃,Function.comp_apply,pack,
    extractPrefix_pairBits,discardPrefix_pairBits,and_self]

def twice (x : List Bool) : List Bool := nword x++nword x
noncomputable def twice_computes : PolyComputes twice := nword_computes.append nword_computes
def blocks (x : List Bool) : List Bool :=
  RepeatedAppend.copies (nword x).length (nword x)++
    RepeatedAppend.copies (twice x).length (pword x++sword x)++[true]
noncomputable def blocks_computes : PolyComputes blocks :=
  ((copy_computes nword_computes nword_computes).append
    (copy_computes twice_computes (pword_computes.append sword_computes))).append (const_computes [true])
def budgetWord (x : List Bool) : List Bool := RepeatedAppend.copies (twice x).length (blocks x)
noncomputable def budgetWord_computes : PolyComputes budgetWord := copy_computes twice_computes blocks_computes
lemma budgetWord_pack (n p s R : ℕ) (rs : List (Row n)) :
    budgetWord (pack n p s R rs)=List.replicate (iterationBudget n p s) true := by
  obtain ⟨hn,hp,hs,_,_⟩ := projections_pack n p s R rs
  simp only [budgetWord,blocks,twice,hn,hp,hs,←List.replicate_add,copies_replicate,List.length_replicate]
  change RepeatedAppend.copies (n+n) (List.replicate (n*n+(n+n)*(p+s)) true++List.replicate 1 true)=_
  rw [←List.replicate_add,copies_replicate]
  congr 1
  unfold iterationBudget iterationBlocks
  ring

noncomputable def dimBits : List Bool → List Bool := lengthBits ∘ nword
noncomputable def dimBits_computes : PolyComputes dimBits := nword_computes.comp lengthBits_computes
lemma dimBits_pack (n p s R : ℕ) (rs : List (Row n)) : dimBits (pack n p s R rs)=n.bits := by
  rw [dimBits,Function.comp_apply,lengthBits_eq,(projections_pack n p s R rs).1,List.length_replicate]
noncomputable def powerWords (x : List Bool) : List Bool := threePower (budgetWord x++[true])
noncomputable def powerWords_computes : PolyComputes powerWords :=
  (budgetWord_computes.append (const_computes [true])).comp threePower_computes
noncomputable def cubeWords (x : List Bool) : List Bool := (value (dimBits x)*value (dimBits x)*value (dimBits x)).bits
noncomputable def cubeWords_computes : PolyComputes cubeWords := by
  unfold cubeWords
  have hh := NatOps.mul (NatOps.mul dimBits_computes dimBits_computes) dimBits_computes
  simpa only [value_bits] using hh
noncomputable def gridWords (x : List Bool) : List Bool := (16*value (cubeWords x)*value (powerWords x)).bits
noncomputable def gridWords_computes : PolyComputes gridWords := by
  unfold gridWords
  have hh := NatOps.mul (NatOps.mul (const_computes (16:ℕ).bits) cubeWords_computes) powerWords_computes
  simpa only [value_bits] using hh
lemma gridWords_pack (n p s R : ℕ) (rs : List (Row n)) : gridWords (pack n p s R rs)=
    (gridDenominator n (iterationBudget n p s)).bits := by
  simp only [gridWords,cubeWords,dimBits_pack,powerWords,budgetWord_pack,threePower_eq,
    List.length_append,List.length_replicate,List.length_cons,List.length_nil,Nat.zero_add,value_bits]
  congr 1
  unfold gridDenominator
  ring

def radiusSquare (x : List Bool) : List Bool := BinaryRational.encode ((value (radius x):ℚ)*(value (radius x):ℚ))
noncomputable def radiusSquare_computes : PolyComputes radiusSquare :=
  RatOps.mul (RatOps.nat radius_computes) (RatOps.nat radius_computes)
noncomputable def shapeWords (x : List Bool) : List Bool :=
  BinaryEllipsoidInitial.run (pairBits (nword x,radiusSquare x))
noncomputable def shapeWords_computes : PolyComputes shapeWords := by
  unfold shapeWords
  simpa only [Function.comp_def] using
    (nword_computes.pair radiusSquare_computes).comp BinaryEllipsoidInitial.run_computes
lemma shapeWords_pack (n p s R : ℕ) (rs : List (Row n)) : shapeWords (pack n p s R rs)=
    RationalMatrix.encode (Ellipsoid.initialState n (R:ℚ)).shape := by
  obtain ⟨hn,_,_,hR,_⟩ := projections_pack n p s R rs
  simp only [shapeWords,radiusSquare,hn,hR,value_bits]
  change BinaryEllipsoidInitial.run (BinaryEllipsoidInitial.pack n ((R:ℚ)*(R:ℚ)))=_
  rw [BinaryEllipsoidInitial.run_pack]
  simp only [Ellipsoid.initialState,pow_two]

def centerWords (x : List Bool) : List Bool := BinaryEllipsoidInitial.zeroVector (nword x)
noncomputable def centerWords_computes : PolyComputes centerWords :=
  nword_computes.comp BinaryEllipsoidInitial.zeroVector_computes
lemma centerWords_pack (n p s R : ℕ) (rs : List (Row n)) : centerWords (pack n p s R rs)=
    rowEncode (Ellipsoid.initialState n (R:ℚ)).center := by
  rw [centerWords,(projections_pack n p s R rs).1,BinaryEllipsoidInitial.zeroVector_replicate]
  rfl
noncomputable def advanceInput (x : List Bool) : List Bool :=
  pairBits (dimBits x,pairBits (gridWords x,pairBits (rows x,pairBits (shapeWords x,centerWords x))))
noncomputable def advanceInput_computes : PolyComputes advanceInput :=
  dimBits_computes.pair (gridWords_computes.pair (rows_computes.pair (shapeWords_computes.pair centerWords_computes)))
lemma advanceInput_pack (n p s R : ℕ) (rs : List (Row n)) : advanceInput (pack n p s R rs)=
    BinaryEllipsoidAdvance.pack (gridDenominator n (iterationBudget n p s)) rs (Ellipsoid.initialState n (R:ℚ)) := by
  simp only [advanceInput,dimBits_pack,gridWords_pack,(projections_pack n p s R rs).2.2.2.2,
    shapeWords_pack,centerWords_pack,BinaryEllipsoidAdvance.pack,BinaryEllipsoidAdvance.stateEncode]
noncomputable def prepared (x : List Bool) : List Bool := pairBits (budgetWord x,pairBits (radius x,advanceInput x))
noncomputable def prepared_computes : PolyComputes prepared :=
  budgetWord_computes.pair (radius_computes.pair advanceInput_computes)
lemma prepared_pack (n p s R : ℕ) (rs : List (Row n)) : prepared (pack n p s R rs)=
    BinaryEllipsoidIteration.pack n (iterationBudget n p s) R rs := by
  simp only [prepared,budgetWord_pack,(projections_pack n p s R rs).2.2.2.1,advanceInput_pack,
    BinaryEllipsoidIteration.pack]
noncomputable def iterated : List Bool → List Bool := BinaryEllipsoidIteration.run ∘ prepared
noncomputable def iterated_computes : PolyComputes iterated := prepared_computes.comp BinaryEllipsoidIteration.run_computes
lemma iterated_pack (n p s R : ℕ) (rs : List (Row n)) (hn : 2≤n) (hR : 1≤R) :
    iterated (pack n p s R rs)=BinaryEllipsoidAdvance.pack (gridDenominator n (iterationBudget n p s)) rs
      (Ellipsoid.iterate (gridDenominator n (iterationBudget n p s)) rs (Ellipsoid.initialState n (R:ℚ)) (iterationBudget n p s)) := by
  rw [iterated,Function.comp_apply,prepared_pack,BinaryEllipsoidIteration.run_pack n _ R rs hn hR]
noncomputable def result (x : List Bool) : List Bool :=
  if BinaryEllipsoidAdvance.found x=[] then true::BinaryEllipsoidAdvance.center x else []
noncomputable def result_computes : PolyComputes result := by
  have hh := (BinaryEllipsoidAdvance.found_computes.comp isEmpty_computes).cond
    (BinaryEllipsoidAdvance.center_computes.comp (prefix_computes true)) (const_computes [])
  unfold result
  simpa only [Function.comp_def,decide_eq_true_eq] using hh
noncomputable def run : List Bool → List Bool := result ∘ iterated
noncomputable def run_computes : PolyComputes run := iterated_computes.comp result_computes
lemma run_pack (n p s R : ℕ) (rs : List (Row n)) (hn : 2≤n) (hR : 1≤R) :
    run (pack n p s R rs)=WordList.Find.optionEncode ((Ellipsoid.weakSolve rs (R:ℚ) p s).map rowEncode) := by
  rw [run,Function.comp_apply,iterated_pack n p s R rs hn hR]
  simp only [result,BinaryEllipsoidAdvance.found_pack,BinaryEllipsoidAdvance.center_pack,weakSolve]
  cases he : badRow rs (Ellipsoid.iterate (gridDenominator n (iterationBudget n p s)) rs
      (Ellipsoid.initialState n (R:ℚ)) (iterationBudget n p s)).center with
  | none => simp [WordList.Find.optionEncode]
  | some r => simp [WordList.Find.optionEncode]
end BinaryWeakSolve
end MetricKMedianRecovery.BitMachine

end OAI
