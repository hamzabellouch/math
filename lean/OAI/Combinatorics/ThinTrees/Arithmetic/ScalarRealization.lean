import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialCoordinates
import OAI.Analysis.MatrixSigning.Complexity.PolynomialMatrixFold
import OAI.Combinatorics.ThinTrees.Arithmetic.BinaryArithmetic
import OAI.Combinatorics.ThinTrees.RationalMatrix.Squares

namespace OAI

/-! Scalar realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 AlgorithmicThinTrees.RationalGram
local notation "X" => NaturalPolynomial.variable

abbrev SquareScan := ℕ×(ℚ×List ℚ)
abbrev squareScanCode := prodCode binaryNatCode (prodCode ratCode vectorCode)
abbrev squarePayload := first binaryNatCode (prodCode ratCode vectorCode)
abbrev squareRest := second binaryNatCode (prodCode ratCode vectorCode)
abbrev squarePower := squareRest.then (first ratCode vectorCode)
abbrev squareAccum := squareRest.then (second ratCode vectorCode)

def squareScanStep (p : SquareScan) : SquareScan :=
  (p.1/4,(2*p.2.1,p.2.2++List.replicate (p.1%4) p.2.1))

def squareScan : Realizes squareScanCode squareScanCode squareScanStep :=
  (squarePayload.then (binaryDiv 4)).both
    (((constant squareScanCode ratCode 2).mul squarePower).both
      ((squareAccum.both ((squarePower.both (squarePayload.then (binaryModUnary 4))).then
        (replicateList ratCode))).then (appendList ratCode)))
instance poly_squareScan : PolyTime squareScan := by
  let : Fact (0<4) := ⟨by decide⟩
  unfold squareScan
  apply poly_both

lemma squareScan_correct (k n : ℕ) (a : ℚ) (xs : List ℚ) :
    (squareScanStep^[k] (n,(a,xs))).2.2=
      xs++(base4Squares k n).map (fun v : ℕ => a*(v:ℚ)) := by
  induction k generalizing n a xs with
  | zero => simp [base4Squares]
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    change (squareScanStep^[k] (n/4,(2*a,xs++List.replicate (n%4) a))).2.2=_
    rw [ih]
    simp only [base4Squares,List.map_append,List.map_replicate,Nat.cast_one,mul_one,
      List.map_map,Function.comp_def,List.append_assoc]
    congr 2
    apply List.map_congr_left
    intro x hx
    push_cast
    ring

lemma squareScan_invariant (p : SquareScan) {b : ℕ}
    (hf : QParts b p.2.1) (hx : ∀v∈p.2.2,QParts b v) (k : ℕ) :
    let s := squareScanStep^[k] p
    s.1≤p.1 ∧ QParts (b+k) s.2.1 ∧ s.2.2.length≤p.2.2.length+3*k ∧
      ∀v∈s.2.2,QParts (b+k) v := by
  induction k with
  | zero => exact ⟨le_rfl,by simpa using hf,by simp,by simpa using hx⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    dsimp only at ih ⊢
    generalize he : squareScanStep^[k] p=s at ih ⊢
    dsimp only [squareScanStep]
    refine ⟨(Nat.div_le_self _ _).trans ih.1,?_,?_,?_⟩
    · have htwo : QParts 1 (2:ℚ) := by norm_num [QParts]
      exact (htwo.mul ih.2.1).mono (by omega)
    · simp only [List.length_append,List.length_replicate]
      have hh := Nat.mod_lt s.1 (by decide : 0<4)
      omega
    · intro v hv
      simp only [List.mem_append,List.mem_replicate] at hv
      rcases hv with h|⟨_,rfl⟩
      · exact (ih.2.2.2 v h).mono (by omega)
      · exact ih.2.1.mono (by omega)

instance size_squareScan : IterateSize squareScan := by
  refine ⟨⟨100*(X+1)^2,?_⟩⟩
  intro p k
  let S := (squareScanCode p).length
  have hn := le_prodCode_left (ea:=binaryNatCode) (eb:=prodCode ratCode vectorCode) p
  have hr := le_prodCode_right (ea:=binaryNatCode) (eb:=prodCode ratCode vectorCode) p
  have hf := (le_prodCode_left p.2).trans hr
  have hx := (le_prodCode_right p.2).trans hr
  have hfx := (qparts_length p.2.1).mono hf
  have hxx : ∀v∈p.2.2,QParts S v := fun v hv =>
    (qparts_length v).mono ((mem_length_le_code p.2.2 hv).trans hx)
  obtain ⟨hN,hF,hX,hV⟩ := squareScan_invariant p hfx hxx k
  have hn' : (binaryNatCode (squareScanStep^[k] p).1).length≤S := by
    have h := Nat.size_le_size hN
    simpa only [binaryNatCode,KS.W01.natPayloadLength_eq_size,CurrentKS.payload_length]
      using h.trans (show p.1.size≤S by simpa only [binaryNatCode,CurrentKS.payload_length] using hn)
  have hl := (list_length_le_code ratCode p.2.2).trans hx
  have hb := (listCode_length_bound (squareScanStep^[k] p).2.2 (4*(S+k)+7)
    (fun v hv => (hV v hv).length)).trans
      (Nat.mul_le_mul_right _ (hX.trans (Nat.add_le_add_right hl _)))
  have hfl := hF.length
  change (squareScanCode (squareScanStep^[k] p)).length≤100*(S+k+1)^2
  simp only [squareScanCode,prodCode_length]
  change (ratCode (squareScanStep^[k] p).2.1).length≤4*(S+k)+7 at hfl
  change (vectorCode (squareScanStep^[k] p).2.2).length≤(S+3*k)*(2*(4*(S+k)+7)+1) at hb
  nlinarith only [hn',hb,hfl,Nat.zero_le S,Nat.zero_le k,sq_nonneg (S:ℤ),sq_nonneg (k:ℤ)]

def scalarFactorProgram : Realizes ratCode vectorCode scalarFactors :=
  let n := scalarProductBinary
  let a := (constant ratCode ratCode 1).div ratDenRat
  let start := n.both (a.both (constant ratCode vectorCode []))
  ((((n.then binarySize).both start).then squareScan.iterate).then squareAccum).congr (fun q => by
    rw [squareScan_correct]
    simp only [List.nil_append,scalarFactors]
    apply List.map_congr_left
    intro x hx
    ring)
instance poly_scalarFactorProgram : PolyTime scalarFactorProgram := by
  unfold scalarFactorProgram;infer_instance

end CurrentKS.Realization
end

end OAI
