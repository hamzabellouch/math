import Mathlib
import OAI.Combinatorics.KMedian.Optimization.SimplexProjection
import OAI.Combinatorics.KMedian.Binary.BinaryListContext
import OAI.Combinatorics.KMedian.Binary.BinaryRationalFold
import OAI.Combinatorics.KMedian.Optimization.LPListFacts

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

def upper (xs : Row) (a : ℚ) : Row := xs.filter (fun q => decide (a≤q))
def threshold (xs : Row) (k a : ℚ) : ℚ := ((upper xs a).sum-k)/(upper xs a).length
def thresholds (xs : Row) (k : ℚ) : Row := xs.map (threshold xs k)
def level (xs : Row) (k : ℚ) : ℚ :=
  let ts := thresholds xs k
  ts.foldl max (ts.head?.getD 0)
def project (xs : Row) (k : ℚ) : Row := xs.map (fun q => max 0 (q-level xs k))

 theorem threshold_ofFn {n : ℕ} (x : Fin n → ℚ) (k : ℚ) (a : Fin n) :
    threshold (List.ofFn x) k (x a)=Simplex.threshold x k a := by
  simp only [threshold,upper,sum_filter_ofFn,length_filter_ofFn,decide_eq_true_eq,Simplex.threshold,Simplex.upper]

 theorem thresholds_ofFn {n : ℕ} (x : Fin n → ℚ) (k : ℚ) :
    thresholds (List.ofFn x) k=List.ofFn (Simplex.threshold x k) := by
  simp only [thresholds,List.map_ofFn]
  congr 1
  funext a
  exact threshold_ofFn x k a

 theorem level_ofFn {n : ℕ} [NeZero n] (x : Fin n → ℚ) (k : ℚ) :
    level (List.ofFn x) k=Simplex.level x k := by
  unfold level
  rw [thresholds_ofFn]
  have hmem : (List.ofFn (Simplex.threshold x k)).head?.getD 0∈List.ofFn (Simplex.threshold x k) := by
    have hne : List.ofFn (Simplex.threshold x k)≠[] := by
      intro h
      have hl:=congrArg List.length h
      simp only [List.length_ofFn,List.length_nil] at hl
      exact (NeZero.ne n) hl
    generalize List.ofFn (Simplex.threshold x k)=ts at hne ⊢
    cases ts with
    | nil => contradiction
    | cons a ts => exact List.mem_cons_self
  obtain ⟨a,ha⟩ := Simplex.level_attained x k
  apply foldl_max_eq
  · obtain ⟨b,hb⟩ := List.mem_ofFn.mp hmem
    rw [← hb]
    exact Simplex.threshold_le_level x k b
  · exact List.mem_ofFn.mpr ⟨a,ha.symm⟩
  · intro v hv
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp hv
    exact Simplex.threshold_le_level x k b

 theorem project_ofFn {n : ℕ} [NeZero n] (x : Fin n → ℚ) (k : ℚ) :
    project (List.ofFn x) k=List.ofFn (Simplex.project x k) := by
  simp only [project,level_ofFn,List.map_ofFn,Function.comp_def]
  rfl

namespace Program
open Binary Binary.PolyProgram
abbrev ethreshold := encodePair (encodePair er Ratio.encode) Ratio.encode
noncomputable def upperProgram : PolyProgram (encodePair Ratio.encode er) er (fun x : ℚ × Row => upper x.2 x.1) :=
  (listFilterWith ratLE 0 0).congr _ (fun _ => rfl)
noncomputable def thresholdProgram : PolyProgram ethreshold Ratio.encode (fun x : (Row × ℚ) × ℚ => threshold x.1.1 x.1.2 x.2) := by
  let dat := fst (encodePair er Ratio.encode) Ratio.encode
  let xs := dat.comp (fst er Ratio.encode)
  let k := dat.comp (snd er Ratio.encode)
  let a := snd (encodePair er Ratio.encode) Ratio.encode
  let us := (a.fanout xs).comp upperProgram
  let sum := us.comp ratSum
  let card := (us.comp (listLength Ratio.encode 0)).comp ratOfNat
  exact (((sum.fanout k).comp ratSub).fanout card).comp ratDiv
noncomputable def thresholdsProgram : PolyProgram (encodePair er Ratio.encode) er (fun x : Row × ℚ => thresholds x.1 x.2) :=
  (((identity (encodePair er Ratio.encode)).fanout (fst er Ratio.encode)).comp
    (thresholdProgram.listMapWith 0 0)).congr _ (fun _ => rfl)
noncomputable def levelProgram : PolyProgram (encodePair er Ratio.encode) Ratio.encode (fun x : Row × ℚ => level x.1 x.2) :=
  ((thresholdsProgram.fanout (thresholdsProgram.comp (listHead Ratio.encode 0))).comp maxFold).congr _ (fun _ => rfl)
noncomputable def positivePart : PolyProgram Ratio.encode Ratio.encode (fun q => max 0 q) :=
  (((constant Ratio.encode Ratio.encode 0).fanout (identity Ratio.encode)).comp ratMax).congr _ (fun _ => rfl)
noncomputable def projectProgram : PolyProgram (encodePair er Ratio.encode) er (fun x : Row × ℚ => project x.1 x.2) := by
  let sub := ((exchange Ratio.encode Ratio.encode).comp ratSub).comp positivePart
  exact ((levelProgram.fanout (fst er Ratio.encode)).comp (sub.listMapWith 0 0)).congr _ (fun _ => rfl)
end Program
end MetricKMedian.LPBinary
end

end OAI
