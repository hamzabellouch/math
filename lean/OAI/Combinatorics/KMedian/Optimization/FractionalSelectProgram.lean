import Mathlib
import OAI.Combinatorics.KMedian.Optimization.FractionalListChecks
import OAI.Combinatorics.KMedian.Programs.ScaleListProgram

namespace OAI


                                               
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Scale

def argmin (xs : Row) (f : ℚ → ℚ) : ℚ := minimum (xs.filter (fun x => decide (f x=minimum (xs.map f))))

theorem argmin_eq (xs : Row) (A : Finset ℚ) (f : ℚ → ℚ) (hm : ∀ q, q ∈ xs ↔ q ∈ A) :
    argmin xs f=rationalArgmin A f := by
  by_cases hA : A.Nonempty
  · let v := (A.image f).min' (hA.image f)
    let B := A.filter (fun t => f t=v)
    have hB : B.Nonempty := by
      obtain ⟨t,ht,he⟩ := mem_image.mp (min'_mem (A.image f) (hA.image f))
      exact ⟨t,mem_filter.mpr ⟨ht,he⟩⟩
    have hv : minimum (xs.map f)=v := by
      apply minimum_eq_finset
      intro q
      simp only [List.mem_map,mem_image]
      exact exists_congr (fun x => and_congr_left (fun _ => hm x))
    unfold argmin
    rw [hv]
    have hh := minimum_eq_finset (xs.filter (fun t => decide (f t=v))) B hB (fun q => by
      simp only [List.mem_filter,decide_eq_true_eq,mem_filter,B,hm])
    rw [hh]
    simp only [rationalArgmin,dite_eq_left hA]
    change B.min' hB=(if h : B.Nonempty then B.min' h else 0)
    rw [dite_eq_left hB]
  · have hz : xs=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro q hq
      exact hA ⟨q,(hm q).mp hq⟩
    simp only [argmin,hz,List.map_nil,List.filter_nil,minimum,List.head?_nil,Option.getD_none,
      List.foldl_nil,rationalArgmin,dite_eq_right hA]

end Scale
namespace Input
noncomputable def zeroOutputProgram : PolyProgram Input.encode Repair.eo Input.zeroOutput := by
  let rows := Program.inputRaw.comp (fst ers Nat.bits)
  let rowZero := (constant Ratio.encode Ratio.encode 0).listMap 0
  let mat := rows.comp (rowZero.listMap [])
  let row := (rows.comp (listHead er [])).comp rowZero
  exact (row.fanout mat).congr _ (fun I => by
    change (((I.rows.head?.getD []).map (fun _ => (0:ℚ))),I.rows.map (fun ds => ds.map (fun _ => (0:ℚ))))=I.zeroOutput
    have hi : I.rows.head?.getD []=List.ofFn (I.distance ⟨0,I.mpos⟩) := by
      dsimp only [Input.rows]
      rw [List.head?_eq_getElem?]
      simp only [List.getElem?_ofFn, I.mpos, dite_eq_left, Option.getD_some]
    rw [hi]
    simp only [Input.rows,List.map_ofFn,Function.comp_def,Input.zeroOutput,List.ofFn_const])
end Input
namespace Scale

def candidate (r : ℕ) (I : Input) (B : ℚ) : Repair.Output :=
  if 0 < B then Repair.raw r (I.scale B) else I.zeroOutput

theorem candidate_eq (r : ℕ) (hr : 0 < r) (I : Input) (hd : ∀ j i, 0 ≤ I.distance j i) (B : ℚ) :
    candidate r I B=Repair.encodeData (TruncatedLP.scaledCandidate I.distance r I.k hr I.kpos hd B) := by
  unfold candidate TruncatedLP.scaledCandidate
  by_cases hB : 0 < B
  · rw [ite_eq_left hB,dite_eq_left hB]
    exact Repair.raw_eq r hr (I.scale B) (fun j i => div_nonneg (hd j i) hB.le)
  · rw [ite_eq_right hB,dite_eq_right hB]
    have hz : ProjectedSubgradient.point (Vector.replicate I.n (0:ℚ)) = (fun _ => 0) := by
      funext i
      exact Vector.getElem_replicate _
    simp only [Repair.encodeData,Input.zeroOutput,Vector.getElem_replicate,hz,List.ofFn_const]

noncomputable def candidateProgram (r : ℕ) (hr : 0 < r) :
    PolyProgram (encodePair Input.encode Ratio.encode) Repair.eo (fun x : Input × ℚ => candidate r x.1 x.2) := by
  let test := ((constant (encodePair Input.encode Ratio.encode) Ratio.encode 0).fanout (snd Input.encode Ratio.encode)).comp ratLT
  exact (ite test ((fst Input.encode Ratio.encode).comp Input.zeroOutputProgram)
    (Input.scaleProgram.comp (Repair.rawProgram r hr))).congr _ (fun _ => by
      simp only [Function.comp_apply,candidate,decide_eq_true_eq])

def feasible (r : ℕ) (I : Input) : Row := (guesses I.rows).filter (fun B => Repair.valid (candidate r I B) I.k)
def selectedScale (r : ℕ) (I : Input) : ℚ := argmin (feasible r I) (fun B => Repair.value (candidate r I B) I.rows)
def selected (r : ℕ) (I : Input) : Repair.Output := candidate r I (selectedScale r I)

theorem feasible_mem (r : ℕ) (hr : 0 < r) (I : Input) (hd : ∀ j i, 0 ≤ I.distance j i) (B : ℚ) :
    B ∈ feasible r I ↔ B ∈ TruncatedLP.feasibleScales I.distance r I.k hr I.kpos hd := by
  simp only [feasible,List.mem_filter,Input.rows,guesses_mem,candidate_eq r hr I hd,
    Repair.valid_encodeData,decide_eq_true_eq,TruncatedLP.feasibleScales,mem_filter]

theorem selected_eq (r : ℕ) (hr : 0 < r) (I : Input) (hd : ∀ j i, 0 ≤ I.distance j i) :
    selected r I=Repair.encodeData (TruncatedLP.selectFractional I.distance r I.k hr I.kpos hd) := by
  have hm (B : ℚ) : Repair.value (candidate r I B) I.rows=(TruncatedLP.scaledCandidate I.distance r I.k hr I.kpos hd B).value I.distance := by
    rw [candidate_eq r hr I hd,Input.rows,Repair.value_encodeData]
  unfold selected selectedScale
  simp only [hm]
  rw [argmin_eq _ _ _ (feasible_mem r hr I hd),candidate_eq r hr I hd]
  rfl

noncomputable def valueOfProgram (r : ℕ) (hr : 0 < r) :
    PolyProgram (encodePair Input.encode Ratio.encode) Ratio.encode (fun x : Input × ℚ => Repair.value (candidate r x.1 x.2) x.1.rows) :=
  (((candidateProgram r hr).fanout ((fst Input.encode Ratio.encode).comp (Program.inputRaw.comp (fst ers Nat.bits)))).comp Repair.valueProgram).congr _ (fun _ => rfl)

noncomputable def feasibleProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode er (feasible r) := by
  let k := (fst Input.encode Ratio.encode).comp (Program.inputRaw.comp (snd ers Nat.bits))
  let test := (((candidateProgram r hr).fanout k).comp Repair.validProgram)
  let guesses := (Program.inputRaw.comp (fst ers Nat.bits)).comp guessesProgram
  let emptyI : Input := ⟨1,1,1,by decide,by decide,by decide,le_rfl,fun _ _ => 0⟩
  exact (((identity Input.encode).fanout guesses).comp (test.listFilterWith 0 emptyI)).congr _ (fun _ => rfl)

noncomputable def selectedScaleProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode Ratio.encode (selectedScale r) := by
  let xs := feasibleProgram r hr
  let values := (((identity Input.encode).fanout xs).comp ((valueOfProgram r hr).listMapWith 0 0))
  let v := values.comp Program.minimumProgram
  let ec := encodePair Input.encode Ratio.encode
  let I := (fst ec Ratio.encode).comp (fst Input.encode Ratio.encode)
  let q := snd ec Ratio.encode
  let C := (I.fanout q).comp (valueOfProgram r hr)
  let V := (fst ec Ratio.encode).comp (snd Input.encode Ratio.encode)
  let test := (C.fanout V).comp ratEQ
  let emptyI : Input := ⟨1,1,1,by decide,by decide,by decide,le_rfl,fun _ _ => 0⟩
  let filtered := ((((identity Input.encode).fanout v).fanout xs).comp (test.listFilterWith 0 (emptyI,0)))
  exact (filtered.comp Program.minimumProgram).congr _ (fun _ => rfl)

noncomputable def selectedProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode Repair.eo (selected r) :=
  ((((identity Input.encode).fanout (selectedScaleProgram r hr)).comp (candidateProgram r hr))).congr _ (fun _ => rfl)

end Scale
end MetricKMedian.LPBinary
end

end OAI
