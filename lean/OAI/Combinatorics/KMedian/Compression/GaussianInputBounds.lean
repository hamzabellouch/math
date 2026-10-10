import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalIntervals
import OAI.Combinatorics.KMedian.Compression.GaussianListSize

namespace OAI


                                           
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Finset Polynomial

structure Input where
  rows : ℕ
  cols : ℕ
  data : RatMatrix rows cols
  underdetermined : rows<cols

def Input.raw (I : Input) : List Unit × Rows :=
  (List.replicate I.cols (),matrix (values I.data))
abbrev Input.encode (I : Input) := edata I.raw

 theorem input_bounds (I : Input) :
    I.rows ≤ I.encode.length ∧ I.cols ≤ I.encode.length ∧
      ∀ i j,HasHeight (values I.data i j) I.encode.length := by
  let L := I.encode.length
  have henc : L=2*I.cols+1+(ers (matrix (values I.data))).length := by
    simp only [L,Input.raw,encodePair_length,slots_size]
  have hr := EncodedList.length_le er (matrix (values I.data))
  simp only [matrix,List.length_ofFn] at hr
  change I.rows ≤ (ers (matrix (values I.data))).length at hr
  refine ⟨by omega,by omega,?_⟩
  intro i j
  have hrow : List.ofFn (values I.data i)∈matrix (values I.data) := List.mem_ofFn.mpr ⟨i,rfl⟩
  have hq : values I.data i j∈List.ofFn (values I.data i) := List.mem_ofFn.mpr ⟨j,rfl⟩
  have h₁ := EncodedList.member_length Ratio.encode (List.ofFn (values I.data i)) _ hq
  have h₂ := EncodedList.member_length er (matrix (values I.data)) _ hrow
  change (Ratio.encode (values I.data i j)).length ≤ (er (List.ofFn (values I.data i))).length at h₁
  change (er (List.ofFn (values I.data i))).length ≤ (ers (matrix (values I.data))).length at h₂
  exact (Ratio.height_length _).mono (by omega)

 theorem residualHeight_mono {r n l R N L : ℕ} (hr : r ≤ R) (hn : n ≤ N) (hl : l ≤ L) :
    residualHeight r n l ≤ residualHeight R N L := by
  unfold residualHeight
  gcongr

 theorem returnHeight_mono {r n l R N L : ℕ} (hr : r ≤ R) (hn : n ≤ N) (hl : l ≤ L) :
    returnHeight r n l ≤ returnHeight R N L := by
  have hh := residualHeight_mono hr hn hl
  unfold returnHeight
  gcongr

 theorem input_audit (I : Input) :
    Audit I.encode.length I.encode.length (residualHeight I.encode.length I.encode.length I.encode.length)
      (returnHeight I.encode.length I.encode.length I.encode.length) I.rows I.cols I.data := by
  let L := I.encode.length
  obtain ⟨hr,hn,hh⟩ := input_bounds I
  intro B hB
  obtain ⟨P⟩ := kernelStates_certificate (values I.data) I.rows I.cols I.data (ResidualCertificate.initial _) B hB
  have hrB : B.rows ≤ I.rows := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P.row P.row_injective
  have hnB : B.cols ≤ I.cols := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P.col P.col_injective
  refine ⟨hrB.trans hr,hnB.trans hn,?_,?_⟩
  · intro i j
    have hb := kernelStates_entry_height I.rows I.cols L I.data (fun i j => (hh i j).1) (fun i j => (hh i j).2) B hB i j
    exact HasHeight.mono hb (residualHeight_mono hr hn le_rfl)
  · intro j
    have hb := kernelStates_return_height I.rows I.cols L I.data I.underdetermined
      (fun i j => (hh i j).1) (fun i j => (hh i j).2) B hB j
    exact HasHeight.mono hb (returnHeight_mono hr hn le_rfl)

noncomputable def residualPolynomial : Polynomial ℕ := X+2*X*(X+X*(X+1))+X*(X+1)
noncomputable def returnPolynomial : Polynomial ℕ := 2*X*(X+residualPolynomial*(X+1))
noncomputable def statePolynomial : Polynomial ℕ :=
  let rowH := X*(2*(3*residualPolynomial+10)+1)
  let rowK := X*(2*(3*returnPolynomial+10)+1)
  let mat := X*(2*rowH+1)
  let frame := 2*(X+1)+1+rowH
  let frames := X*(2*frame+1)
  4*X+2*mat+2*rowK+2*frames+10

 theorem residualPolynomial_eval (L : ℕ) : residualPolynomial.eval L=residualHeight L L L := by
  simp only [residualPolynomial,residualHeight,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
 theorem returnPolynomial_eval (L : ℕ) : returnPolynomial.eval L=returnHeight L L L := by
  simp only [returnPolynomial,returnHeight,eval_add,eval_mul,eval_X,eval_ofNat,eval_one,residualPolynomial_eval]
 theorem statePolynomial_eval (L : ℕ) : statePolynomial.eval L=
    stateBound L L (residualHeight L L L) (returnHeight L L L) := by
  simp only [statePolynomial,stateBound,rowBound,matrixBound,frameBound,framesBound,eval_add,eval_mul,eval_X,eval_ofNat,eval_one,residualPolynomial_eval,returnPolynomial_eval]
end MetricKMedian.Gaussian.ListOperation
end

end OAI
