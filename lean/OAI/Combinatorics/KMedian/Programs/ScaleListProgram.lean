import Mathlib
import OAI.Combinatorics.KMedian.Optimization.MatrixNormalization
import OAI.Combinatorics.KMedian.Binary.BinaryDyadicPowers
import OAI.Combinatorics.KMedian.Optimization.ApproximationListProgram

namespace OAI


                                        
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Scale

def guesses (ds : Rows) : Row :=
  ds.flatten.flatMap (fun q => if 0 < q then (Dyadic.powers ds.length).map (fun t => q*t) else [])

theorem guesses_mem {n m : ℕ} (d : Fin m → Fin n → ℚ) (q : ℚ) :
    q ∈ guesses (List.ofFn (fun j => List.ofFn (d j))) ↔ q ∈ Normalization.matrixGuesses d := by
  unfold guesses Normalization.matrixGuesses
  simp only [List.mem_flatMap,List.mem_flatten,mem_biUnion,mem_univ,true_and]
  constructor
  · rintro ⟨v,⟨xs,hxs,hv⟩,hq⟩
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    by_cases h : 0 < d j i
    · simp only [ite_eq_left h,List.length_ofFn,Dyadic.powers_eq,List.mem_map,List.mem_range] at hq
      obtain ⟨z,⟨t,ht,rfl⟩,he⟩ := hq
      exact ⟨(j,i),by simp only [ite_eq_left h,mem_image,mem_range]; exact ⟨t,ht,he⟩⟩
    · simp only [ite_eq_right h,List.not_mem_nil] at hq
  · rintro ⟨⟨j,i⟩,hq⟩
    by_cases h : 0 < d j i
    · simp only [ite_eq_left h,mem_image,mem_range] at hq
      obtain ⟨t,ht,rfl⟩ := hq
      refine ⟨d j i,⟨List.ofFn (d j),List.mem_ofFn.mpr ⟨j,rfl⟩,List.mem_ofFn.mpr ⟨i,rfl⟩⟩,?_⟩
      simp only [ite_eq_left h,List.length_ofFn,Dyadic.powers_eq,List.mem_map,List.mem_range]
      exact ⟨(2:ℚ)^t,⟨t,ht,rfl⟩,rfl⟩
    · simp only [ite_eq_right h,notMem_empty] at hq

noncomputable def guessesProgram : PolyProgram ers er guesses := by
  let e := encodePair er Ratio.encode
  let q := snd er Ratio.encode
  let ps := fst er Ratio.encode
  let times := ratMul.listMapWith 0 0
  let pos := ((constant e Ratio.encode 0).fanout q).comp ratLT
  let body := ite pos (constant e er []) ((q.fanout ps).comp times)
  let powers := (listLength er []).comp Dyadic.program
  exact ((powers.fanout (listFlatten Ratio.encode 0)).comp (body.listFlatMapWith 0 0)).congr _ (fun _ => by
    simp only [Function.comp_apply,guesses,decide_eq_true_eq])

end Scale
namespace Input

def scale (I : Input) (B : ℚ) : Input := { I with distance := fun j i => I.distance j i/B }
def zeroOutput (I : Input) : Repair.Output :=
  (List.replicate I.n 0,List.replicate I.m (List.replicate I.n 0))

theorem scale_rows (I : Input) (B : ℚ) :
    (I.scale B).rows=I.rows.map (fun ds => ds.map (fun d => d/B)) := by
  simp only [rows,scale,List.map_ofFn,Function.comp_def]

noncomputable def scaleProgram : PolyProgram (encodePair Input.encode Ratio.encode) Input.encode (fun x : Input × ℚ => x.1.scale x.2) := by
  let coord := (exchange Ratio.encode Ratio.encode).comp ratDiv
  let matrix := (coord.listMapWith 0 0).listMapWith [] []
  let I := fst Input.encode Ratio.encode
  let B := snd Input.encode Ratio.encode
  let ds := I.comp (Program.inputRaw.comp (fst ers Nat.bits))
  let k := I.comp (Program.inputRaw.comp (snd ers Nat.bits))
  let raw := ((B.fanout ds).comp matrix).fanout k
  exact raw.recode id (fun _ => rfl) (fun x => by
    dsimp only [Function.comp_apply,id_eq]
    change ei ((x.1.rows.map (fun ds => ds.map (fun d => d/x.2))),x.1.k)=ei ((x.1.scale x.2).raw)
    rw [Input.raw,scale_rows]
    rfl)
end Input
end MetricKMedian.LPBinary
end

end OAI
