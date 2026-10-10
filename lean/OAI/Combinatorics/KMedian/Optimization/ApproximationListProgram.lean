import Mathlib
import OAI.Combinatorics.KMedian.Optimization.LPBinaryTrajectory
import OAI.Combinatorics.KMedian.Programs.NearestListProgram

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair
abbrev Output := Row × Rows
abbrev eo := encodePair er ers

def opening (ys : Row) (ρ : ℚ) : Row := ys.map (fun y => min 1 (y/(1-ρ)))
def weights (ds xs : Row) : Row := (ds.zip xs).map (fun p => if p.1 ≤ 1 then p.2 else 0)
def assignment (ds xs : Row) : Row := let ws := weights ds xs; ws.map (fun w => w/ws.sum)
def assignments (ds xs : Rows) : Rows := (ds.zip xs).map (fun p => assignment p.1 p.2)
def nearestRows (ds : Rows) (ys : Row) : Rows := ds.map (Nearest.filling ys)
def finish (ds : Rows) (ys : Row) (H ρ : ℚ) : Output :=
  (opening ys ρ,assignments ds (nearestRows (Truncated.matrix ds H) ys))
def raw (r : ℕ) (I : Input) : Output := finish I.rows (result r I) (rawPenalty r I.raw) (TruncatedLP.loss r I.k)

theorem opening_ofFn {n : ℕ} (y : Fin n → ℚ) (ρ : ℚ) :
    opening (List.ofFn y) ρ=List.ofFn (TruncatedLP.repairedOpening y ρ) := by
  simp only [opening,List.map_ofFn,Function.comp_def]
  rfl
theorem weights_ofFn {n : ℕ} (d x : Fin n → ℚ) :
    weights (List.ofFn d) (List.ofFn x)=List.ofFn (fun i => if d i ≤ 1 then x i else 0) := by
  simp only [weights,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,Function.comp_def]
theorem assignments_ofFn {n m : ℕ} (d x : Fin m → Fin n → ℚ) :
    assignments (List.ofFn (fun j => List.ofFn (d j))) (List.ofFn (fun j => List.ofFn (x j)))=
      List.ofFn (fun j => List.ofFn (TruncatedLP.repairedAssignment d x j)) := by
  simp only [assignments,Gaussian.ListOperation.zip_ofFn,List.map_ofFn,Function.comp_def,assignment,weights_ofFn,List.sum_ofFn]
  rfl

def encodeData {n m : ℕ} (a : TruncatedLP.FractionalData n m) : Output :=
  (List.ofFn (ProjectedSubgradient.point a.opening),List.ofFn (fun j => List.ofFn (ProjectedSubgradient.point a.assignment[j.val])))

theorem raw_eq (r : ℕ) (hr : 0 < r) (I : Input) (hd : ∀ j i, 0 ≤ I.distance j i) :
    raw r I=encodeData (TruncatedLP.approximation I.distance r I.k hr I.kpos hd) := by
  let H := TruncatedLP.penalty r I.k
  let y := ProjectedSubgradient.point (TruncatedLP.optimize I.distance r I.k H hr I.kpos (TruncatedLP.penalty_pos r I.k hr))
  have hy : ProjectedSubgradient.feasible (I.k:ℚ) y := (TruncatedLP.optimize_spec I.distance r I.k H hr I.kpos
    (TruncatedLP.penalty_pos r I.k hr) hd (ProjectedSubgradient.point (ProjectedSubgradient.initial (I.k:ℚ)))
    (ProjectedSubgradient.initial_feasible _ (by positivity))).1
  have hm : 1 ≤ ∑ i, y i := by rw [hy.2]; exact_mod_cast I.kpos
  unfold raw finish
  rw [result_eq r hr]
  change (opening (List.ofFn y) (TruncatedLP.loss r I.k),
    assignments I.rows (nearestRows (Truncated.matrix I.rows H) (List.ofFn y)))=_
  rw [opening_ofFn]
  have hn : nearestRows (Truncated.matrix I.rows H) (List.ofFn y)=
      List.ofFn (fun j => List.ofFn (ProjectedSubgradient.point (Preparation.computedNearest y (TruncatedLP.truncated I.distance H j) hy.1 hm))) := by
    simp only [Input.rows,Truncated.matrix_ofFn,nearestRows,List.map_ofFn,Function.comp_def,Nearest.filling_ofFn _ _ hy.1 hm]
  rw [hn]
  unfold Input.rows
  rw [assignments_ofFn]
  simp only [encodeData,TruncatedLP.approximation,Vector.getElem_ofFn,ProjectedSubgradient.point_ofFn]
  rfl

noncomputable def openingProgram : PolyProgram (encodePair er Ratio.encode) er (fun x : Row × ℚ => opening x.1 x.2) := by
  let y := snd Ratio.encode Ratio.encode
  let den := ((constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 1).fanout (fst Ratio.encode Ratio.encode)).comp ratSub
  let val := (y.fanout den).comp ratDiv
  let coord := ((constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 1).fanout val).comp Program.ratMin
  exact ((exchange er Ratio.encode).comp (coord.listMapWith 0 0)).congr _ (fun _ => rfl)
noncomputable def weightsProgram : PolyProgram (encodePair er er) er (fun x : Row × Row => weights x.1 x.2) := by
  let test := ((fst Ratio.encode Ratio.encode).fanout (constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 1)).comp ratLE
  let coord := ite test (constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 0) (snd Ratio.encode Ratio.encode)
  exact ((listZip Ratio.encode Ratio.encode 0 0).comp (coord.listMap (0,0))).congr _ (fun _ => by simp only [Function.comp_apply,weights,decide_eq_true_eq])
noncomputable def assignmentProgram : PolyProgram (encodePair er er) er (fun x : Row × Row => assignment x.1 x.2) := by
  let coord := (exchange Ratio.encode Ratio.encode).comp ratDiv
  let norm := ((ratSum.fanout (identity er)).comp (coord.listMapWith 0 0))
  exact (weightsProgram.comp norm).congr _ (fun _ => rfl)
noncomputable def assignmentsProgram : PolyProgram (encodePair ers ers) ers (fun x : Rows × Rows => assignments x.1 x.2) :=
  ((listZip er er [] []).comp (assignmentProgram.listMap ([],[]))).congr _ (fun _ => rfl)
noncomputable def nearestRowsProgram : PolyProgram (encodePair ers er) ers (fun x : Rows × Row => nearestRows x.1 x.2) :=
  ((exchange ers er).comp (Nearest.fillingProgram.listMapWith [] [])).congr _ (fun _ => rfl)
noncomputable def lossProgram (r : ℕ) : PolyProgram ei Ratio.encode (fun x : Rows × ℕ => TruncatedLP.loss r x.2) :=
  (((constant ei Ratio.encode (1+1/(r:ℚ))).fanout ((Program.rawPenaltyProgram r).comp ratOfNat)).comp ratDiv).congr _ (fun _ => rfl)
noncomputable def rawProgram (r : ℕ) (hr : 0 < r) : PolyProgram Input.encode eo (raw r) := by
  let ds := Program.inputRaw.comp (fst ers Nat.bits)
  let H := (Program.inputRaw.comp (Program.rawPenaltyProgram r)).comp ratOfNat
  let ρ := Program.inputRaw.comp (lossProgram r)
  let y := Program.optimizeProgram r hr
  let tr := (ds.fanout H).comp Program.truncateMatrixProgram
  let xs := (tr.fanout y).comp nearestRowsProgram
  exact (((y.fanout ρ).comp openingProgram).fanout ((ds.fanout xs).comp assignmentsProgram)).congr _ (fun _ => rfl)
end Repair
end MetricKMedian.LPBinary
end

end OAI
