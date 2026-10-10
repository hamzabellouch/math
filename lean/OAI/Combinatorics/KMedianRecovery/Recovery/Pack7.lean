import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.VectorHeight
import OAI.Combinatorics.KMedianRecovery.Machines.LoopInput2
import OAI.Combinatorics.KMedianRecovery.Encoding.OptionEncode
import OAI.Combinatorics.KMedianRecovery.Branching.CopyComputes

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryEllipsoidInitial
open RationalMatrix WordList

def pack (n : ℕ) (q : ℚ) : List Bool := pairBits (List.replicate n true,BinaryRational.encode q)
def dummy (u : List Bool) : List Bool := repeatWords (pairBits (u,[]))
noncomputable def dummy_computes : PolyComputes dummy :=
  (id_computes.pair (const_computes [])).comp repeatWords_computes
lemma dummy_replicate (n : ℕ) : dummy (List.replicate n true)=encode (List.ofFn (fun _ : Fin n=>([]:List Bool))) := by
  rw [dummy,repeatWords_ofFn]
noncomputable def indices : List Bool → List Bool := Indices.run ∘ dummy
noncomputable def indices_computes : PolyComputes indices := dummy_computes.comp Indices.run_computes
lemma indices_replicate (n : ℕ) : indices (List.replicate n true)=WordList.encode (List.ofFn (fun i : Fin n=>i.val.bits)) := by
  rw [indices,Function.comp_apply,dummy_replicate,indices_ofFn]

def ctx : List Bool → List Bool := extractPrefix ∘ extractPrefix
def row : List Bool → List Bool := discardPrefix ∘ extractPrefix
def col : List Bool → List Bool := discardPrefix
noncomputable def ctx_computes : PolyComputes ctx := extractPrefix_computes.comp extractPrefix_computes
noncomputable def row_computes : PolyComputes row := extractPrefix_computes.comp discardPrefix_computes
noncomputable def col_computes : PolyComputes col := discardPrefix_computes

def entryWords (x : List Bool) : List Bool :=
  if value (row x)≤value (col x) then
    if value (col x)≤value (row x) then discardPrefix (ctx x) else BinaryRational.encode 0
  else BinaryRational.encode 0
noncomputable def entryWords_computes : PolyComputes entryWords := by
  unfold entryWords
  have hh := (NatOps.le row_computes col_computes).cond
    ((NatOps.le col_computes row_computes).cond (ctx_computes.comp discardPrefix_computes)
      (const_computes (BinaryRational.encode 0))) (const_computes (BinaryRational.encode 0))
  simpa only [entryWords,Function.comp_def,decide_eq_true_eq] using hh
lemma entryWords_pack (n : ℕ) (q : ℚ) (i j : Fin n) :
    entryWords (pairBits (pairBits (pack n q,i.val.bits),j.val.bits))=
      BinaryRational.encode ((q • (1:Matrix (Fin n) (Fin n) ℚ)) i j) := by
  simp only [entryWords,ctx,row,col,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    pack,value_bits,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  by_cases hij : i=j
  · subst j; simp
  · have hh : i.val≠j.val := fun h=>hij (Fin.ext h)
    split_ifs <;> simp_all; omega

noncomputable def rowInput (x : List Bool) : List Bool :=
  pairBits (x,indices (extractPrefix (extractPrefix x)))
noncomputable def rowInput_computes : PolyComputes rowInput :=
  id_computes.pair ((extractPrefix_computes.comp extractPrefix_computes).comp indices_computes)
noncomputable def rowWords : List Bool → List Bool := mapWith entryWords ∘ rowInput
noncomputable def rowWords_computes : PolyComputes rowWords :=
  rowInput_computes.comp (mapWith_computes entryWords_computes)
lemma rowWords_pack (n : ℕ) (q : ℚ) (i : Fin n) :
    rowWords (pairBits (pack n q,i.val.bits))=
      rowEncode ((q • (1:Matrix (Fin n) (Fin n) ℚ)) i) := by
  simp only [rowWords,Function.comp_apply,rowInput,extractPrefix_pairBits,pack,indices_replicate,mapWith_ofFn]
  change WordList.encode (List.ofFn (fun j=>entryWords (pairBits (pairBits (pack n q,i.val.bits),j.val.bits))))=_
  simp only [entryWords_pack,rowEncode_eq]

noncomputable def runInput (x : List Bool) : List Bool := pairBits (x,indices (extractPrefix x))
noncomputable def runInput_computes : PolyComputes runInput :=
  id_computes.pair (extractPrefix_computes.comp indices_computes)
noncomputable def run : List Bool → List Bool := mapWith rowWords ∘ runInput
noncomputable def run_computes : PolyComputes run := runInput_computes.comp (mapWith_computes rowWords_computes)
lemma run_pack (n : ℕ) (q : ℚ) : run (pack n q)=
    RationalMatrix.encode (q • (1:Matrix (Fin n) (Fin n) ℚ)) := by
  simp only [run,Function.comp_apply,runInput,pack,extractPrefix_pairBits,indices_replicate,mapWith_ofFn]
  change WordList.encode (List.ofFn (fun i=>rowWords (pairBits (pack n q,i.val.bits))))=_
  simp only [rowWords_pack,RationalMatrix.encode]

def zeroVector (x : List Bool) : List Bool := repeatWords (pairBits (x,BinaryRational.encode 0))
noncomputable def zeroVector_computes : PolyComputes zeroVector :=
  (id_computes.pair (const_computes (BinaryRational.encode 0))).comp repeatWords_computes
lemma zeroVector_replicate (n : ℕ) : zeroVector (List.replicate n true)=rowEncode (0 : Fin n → ℚ) := by
  simp only [zeroVector,repeatWords_ofFn,rowEncode_eq,Pi.zero_apply]
end BinaryEllipsoidInitial
end
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid RationalHeight
namespace BinaryEllipsoidIteration
open RationalMatrix BinaryEllipsoidAdvance

def pack (n T R : ℕ) (rs : List (Row n)) : List Bool :=
  pairBits (List.replicate T true,pairBits (R.bits,
    BinaryEllipsoidAdvance.pack (gridDenominator n T) rs (Ellipsoid.initialState n (R:ℚ))))
lemma pack_length (n T R : ℕ) (rs : List (Row n)) :
    (pack n T R rs).length=2*T+2*R.bits.length+
      (BinaryEllipsoidAdvance.pack (gridDenominator n T) rs (Ellipsoid.initialState n (R:ℚ))).length+2 := by
  simp only [pack,pairBits_length,List.length_replicate]; omega
lemma advance_pack_length {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) :
    (BinaryEllipsoidAdvance.pack D rs S).length=
      2*n.bits.length+2*D.bits.length+2*(BinaryRow.rowsEncode rs).length+
        2*(RationalMatrix.encode S.shape).length+(rowEncode S.center).length+4 := by
  simp only [BinaryEllipsoidAdvance.pack,stateEncode,pairBits_length]; omega
lemma coeff_length {n : ℕ} {rs : List (Row n)} {r : Row n} (hr : r∈rs) (i : Fin n) :
    (BinaryRational.encode (r.coeff i)).length≤(BinaryRow.rowsEncode rs).length := by
  have h₁ := WordList.length_member_le_encode (List.mem_ofFn.mpr ⟨i,rfl⟩ :
    BinaryRational.encode (r.coeff i)∈List.ofFn (fun j=>BinaryRational.encode (r.coeff j)))
  rw [←rowEncode_eq] at h₁
  have h₂ := WordList.length_member_le_encode (List.mem_map.mpr ⟨r,hr,rfl⟩ :
    BinaryRow.encode r∈rs.map BinaryRow.encode)
  change (BinaryRow.encode r).length≤(BinaryRow.rowsEncode rs).length at h₂
  simp only [BinaryRow.encode,pairBits_length] at h₂
  omega

lemma input_bounds (n T R : ℕ) (rs : List (Row n)) :
    let L := (pack n T R rs).length
    n≤ L ∧ T≤ L ∧ R≤2^L ∧
    (∀ r∈rs,∀ i,Height (r.coeff i) L) ∧
    2*n.bits.length+2*(gridDenominator n T).bits.length+2*(BinaryRow.rowsEncode rs).length+4≤ L := by
  dsimp only
  have hl := pack_length n T R rs
  have hp := advance_pack_length (gridDenominator n T) rs (Ellipsoid.initialState n (R:ℚ))
  have hn := RationalMatrix.dimension_bound (Ellipsoid.initialState n (R:ℚ)).shape
  have hR : R≤2^(pack n T R rs).length := by
    apply Nat.le_of_lt
    apply Nat.size_le.mp
    rw [←Nat.size_eq_bits_len]
    omega
  refine ⟨by omega,by omega,hR,?_,by omega⟩
  intro r hr i
  exact (BinaryRational.input_height (r.coeff i)).mono ((coeff_length hr i).trans (by omega))

noncomputable def shapePoly : Polynomial ℕ := Polynomial.X+2*Polynomial.X+(4+3*Polynomial.X+2*(Polynomial.X+1))
noncomputable def vectorPoly : Polynomial ℕ := Polynomial.X*(shapePoly+Polynomial.X+1)
noncomputable def quadPoly : Polynomial ℕ := Polynomial.X*(Polynomial.X+vectorPoly+1)
noncomputable def incrementPoly : Polynomial ℕ := Polynomial.X+1+(2*quadPoly+2*(5+Polynomial.X)+1)+vectorPoly
noncomputable def centerPoly : Polynomial ℕ := Polynomial.X*(incrementPoly+1)
noncomputable def storagePoly : Polynomial ℕ :=
  10*(Polynomial.X+1)+2*Polynomial.X*(2*(Polynomial.X*(6*shapePoly+14))+2)+Polynomial.X*(6*centerPoly+14)
lemma shapePoly_eval (L : ℕ) : shapePoly.eval L=storedShapeHeight L L L := by
  simp only [shapePoly,storedShapeHeight,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
lemma incrementPoly_eval (L : ℕ) : incrementPoly.eval L=incrementHeight L (storedShapeHeight L L L) L := by
  simp only [incrementPoly,quadPoly,vectorPoly,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,shapePoly_eval,
    incrementHeight,rootHeight,quadHeight,vectorHeight]
lemma centerPoly_eval (L : ℕ) : centerPoly.eval L=L*(incrementHeight L (storedShapeHeight L L L) L+1) := by
  simp only [centerPoly,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_one,incrementPoly_eval]
lemma storagePoly_eval (L : ℕ) : storagePoly.eval L=
    10*(L+1)+2*L*(2*(L*(6*shapePoly.eval L+14))+2)+L*(6*centerPoly.eval L+14) := by
  simp only [storagePoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_X,Polynomial.eval_one]
lemma shape_mono {n T r L : ℕ} (hn : n≤ L) (hT : T≤ L) (hr : r≤ L) :
    storedShapeHeight n T r≤ storedShapeHeight L L L := by
  unfold storedShapeHeight
  omega
lemma increment_mono {n h a N H A : ℕ} (hn : n≤ N) (hh : h≤ H) (ha : a≤ A) :
    incrementHeight n h a≤ incrementHeight N H A := by
  unfold incrementHeight rootHeight quadHeight vectorHeight
  gcongr
lemma vector_encode_height {n b : ℕ} (v : Fin n → ℚ) (hv : ∀ i,Height (v i) b) :
    (rowEncode v).length≤ n*(6*b+14) := by
  rw [rowEncode_eq]
  have hh := WordList.encode_le_bound (List.ofFn (fun i=>BinaryRational.encode (v i))) (3*b+6) (by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact BinaryRational.encode_height (hv i))
  simp only [List.length_ofFn] at hh
  convert hh using 1; ring

lemma iterate_length_bound (n T R : ℕ) (rs : List (Row n)) (hn : 2≤ n) (hR : 1≤ R)
    (t : ℕ) (ht : t≤ T) :
    (BinaryEllipsoidAdvance.pack (gridDenominator n T) rs
      (Ellipsoid.iterate (gridDenominator n T) rs (Ellipsoid.initialState n (R:ℚ)) t)).length≤
        storagePoly.eval (pack n T R rs).length := by
  let L := (pack n T R rs).length
  obtain ⟨hnL,hTL,hRL,hrows,hstatic⟩ := input_bounds n T R rs
  change n≤ L at hnL
  change T≤ L at hTL
  change R≤2^L at hRL
  change ∀ r∈rs,∀ i,Height (r.coeff i) L at hrows
  change _≤ L at hstatic
  have hs := iterate_shape_Height n T R L rs hn hR hRL t ht
  have hc := iterate_center_height n T R L L rs hn hR hRL hrows t ht
  have hm : storedShapeHeight n T L≤ shapePoly.eval L := by
    rw [shapePoly_eval]
    exact shape_mono hnL hTL le_rfl
  have hcm : t*(incrementHeight n (storedShapeHeight n T L) L+1)≤ centerPoly.eval L := by
    rw [centerPoly_eval]
    exact Nat.mul_le_mul (ht.trans hTL) (Nat.add_le_add_right
      (increment_mono hnL (shape_mono hnL hTL le_rfl) le_rfl) 1)
  have hshape := RationalMatrix.encode_height (Ellipsoid.iterate (gridDenominator n T) rs
      (Ellipsoid.initialState n (R:ℚ)) t).shape (fun i j=>(hs i j).mono hm)
  have hcenc := vector_encode_height (Ellipsoid.iterate (gridDenominator n T) rs
      (Ellipsoid.initialState n (R:ℚ)) t).center (fun i=>(hc i).mono hcm)
  have hm' : n*(2*(n*(6*shapePoly.eval L+14))+2)≤ L*(2*(L*(6*shapePoly.eval L+14))+2) := by gcongr
  have hc' : n*(6*centerPoly.eval L+14)≤ L*(6*centerPoly.eval L+14) := Nat.mul_le_mul_right _ hnL
  rw [advance_pack_length,storagePoly_eval]
  change _≤10*(L+1)+2*L*(2*(L*(6*shapePoly.eval L+14))+2)+L*(6*centerPoly.eval L+14)
  have ha := hshape.trans hm'
  have hb := hcenc.trans hc'
  simp only [Nat.mul_assoc]
  omega

noncomputable def boundCounter : PolynomialCounter storagePoly := PolynomialCounter.choose storagePoly
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (extractPrefix x,pairBits (boundCounter.word x,discardPrefix (discardPrefix x)))
noncomputable def prepared_computes : PolyComputes prepared :=
  extractPrefix_computes.pair (boundCounter.computes.pair (discardPrefix_computes.comp discardPrefix_computes))
noncomputable def run : List Bool → List Bool := BoundedIteration.run BinaryEllipsoidAdvance.run ∘ prepared
noncomputable def run_computes : PolyComputes run :=
  prepared_computes.comp (BoundedIteration.run_computes BinaryEllipsoidAdvance.run_computes)
lemma run_pack (n T R : ℕ) (rs : List (Row n)) (hn : 2≤ n) (hR : 1≤ R) :
    run (pack n T R rs)=BinaryEllipsoidAdvance.pack (gridDenominator n T) rs
      (Ellipsoid.iterate (gridDenominator n T) rs (Ellipsoid.initialState n (R:ℚ)) T) := by
  unfold run
  simp only [Function.comp_apply,prepared,pack,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [BoundedIteration.run_eq]
  · simp only [List.length_replicate,BinaryEllipsoidAdvance.iterate_pack]
  · intro j hj
    simp only [List.length_replicate] at hj
    rw [BinaryEllipsoidAdvance.iterate_pack,boundCounter.word_length]
    exact iterate_length_bound n T R rs hn hR j hj
end BinaryEllipsoidIteration
end MetricKMedianRecovery.BitMachine

end OAI
