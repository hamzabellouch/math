import Mathlib
import OAI.Combinatorics.KMedian.Optimization.TruncatedListCompiler
import OAI.Combinatorics.KMedian.Optimization.LPBinaryInput

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function
abbrev Context := Rows × (ℚ × (ℚ × ℚ))
abbrev ec := encodePair ers (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode))
abbrev State := Context × Row
abbrev es := encodePair ec er
abbrev ei := encodePair ers Nat.bits

def rawPenalty (r : ℕ) (x : Rows × ℕ) : ℕ := 4*r*(x.2+1)
def rawGrad (r : ℕ) (x : Rows × ℕ) : ℕ := (x.1.head?.getD []).length*(x.1.length*rawPenalty r x)^2
def rawRate (r : ℕ) (x : Rows × ℕ) : ℚ := 1/(2*(r:ℚ)*(rawGrad r x:ℚ))
def rawSteps (r : ℕ) (x : Rows × ℕ) : ℕ := 8*r^2*rawGrad r x*x.2^2
def rawContext (r : ℕ) (x : Rows × ℕ) : Context := (x.1,(rawPenalty r x,(x.2,rawRate r x)))
def rawInitial (x : Rows × ℕ) : Row := (List.range (x.1.head?.getD []).length).map (fun i => if i=0 then (x.2:ℚ) else 0)
def start (r : ℕ) (I : Input) : State := (rawContext r I.raw,rawInitial I.raw)
def update (s : State) : State := (s.1,Truncated.next s.1.1 s.2 s.1.2.1 s.1.2.2.1 s.1.2.2.2)

namespace Program
noncomputable def rawPenaltyProgram (r : ℕ) : PolyProgram ei Nat.bits (rawPenalty r) := by
  let k := snd ers Nat.bits
  let p := (k.fanout (constant ei Nat.bits 1)).comp natAdd
  exact ((constant ei Nat.bits (4*r)).fanout p |>.comp natMul).congr _ (fun _ => rfl)
noncomputable def rawGradProgram (r : ℕ) : PolyProgram ei Nat.bits (rawGrad r) := by
  let ds := fst ers Nat.bits
  let n := (ds.comp (listHead er [])).comp (listLength Ratio.encode 0)
  let m := ds.comp (listLength er [])
  let mh := (m.fanout (rawPenaltyProgram r)).comp natMul
  exact ((n.fanout ((mh.fanout mh).comp natMul)).comp natMul).congr _ (fun x => by dsimp only [Function.comp_apply,rawGrad]; rw [pow_two])
noncomputable def rawRateProgram (r : ℕ) : PolyProgram ei Ratio.encode (rawRate r) := by
  let grad := (rawGradProgram r).comp ratOfNat
  let den := ((constant ei Ratio.encode (2*(r:ℚ))).fanout grad).comp ratMul
  exact (den.comp ratInv).congr _ (fun x => by simp only [Function.comp_apply,rawRate,one_div])
noncomputable def rawStepsProgram (r : ℕ) : PolyProgram ei Nat.bits (rawSteps r) := by
  let k := snd ers Nat.bits
  let kk := (k.fanout k).comp natMul
  let g := ((constant ei Nat.bits (8*r^2)).fanout (rawGradProgram r)).comp natMul
  exact ((g.fanout kk).comp natMul).congr _ (fun _ => by dsimp only [Function.comp_apply,rawSteps]; simp only [pow_two])
noncomputable def rawContextProgram (r : ℕ) : PolyProgram ei ec (rawContext r) :=
  ((fst ers Nat.bits).fanout (((rawPenaltyProgram r).comp ratOfNat).fanout (((snd ers Nat.bits).comp ratOfNat).fanout (rawRateProgram r)))).congr _ (fun _ => rfl)
noncomputable def rawInitialProgram : PolyProgram ei er rawInitial := by
  let ids := ((fst ers Nat.bits).comp (listHead er [])).comp (listIndices Ratio.encode 0)
  let k := (snd ers Nat.bits).comp ratOfNat
  let test := (snd Ratio.encode Nat.bits).comp natZero
  let coord := ite test (constant (encodePair Ratio.encode Nat.bits) Ratio.encode 0) (fst Ratio.encode Nat.bits)
  exact ((k.fanout ids).comp (coord.listMapWith 0 0)).congr _ (fun x => by simp only [Function.comp_apply,rawInitial,decide_eq_true_eq])
noncomputable def inputRaw : PolyProgram Input.encode ei Input.raw :=
  (identity ei).recode Input.raw (fun _ => rfl) (fun _ => rfl)
noncomputable def startProgram (r : ℕ) : PolyProgram Input.encode es (start r) :=
  (inputRaw.comp ((rawContextProgram r).fanout rawInitialProgram)).congr _ (fun _ => rfl)
noncomputable def stepsProgram (r : ℕ) : PolyProgram Input.encode Nat.bits (fun I => rawSteps r I.raw) :=
  (inputRaw.comp (rawStepsProgram r)).congr _ (fun _ => rfl)
noncomputable def updateProgram : PolyProgram es es update := by
  let c := fst ec er
  let ds := c.comp (fst ers (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)))
  let hkr := c.comp (snd ers (encodePair Ratio.encode (encodePair Ratio.encode Ratio.encode)))
  let h := hkr.comp (fst Ratio.encode (encodePair Ratio.encode Ratio.encode))
  let kr := hkr.comp (snd Ratio.encode (encodePair Ratio.encode Ratio.encode))
  let args := (((ds.fanout (snd ec er)).fanout h).fanout kr)
  exact (c.fanout (args.comp nextProgram)).congr _ (fun _ => rfl)
end Program

theorem head_ofFn {α : Type} {n : ℕ} [NeZero n] (f : Fin n → α) (a : α) :
    (List.ofFn f).head?.getD a=f ⟨0,NeZero.pos n⟩ := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rw [List.ofFn_succ]; rfl

theorem rawGrad_eq (r : ℕ) (I : Input) : rawGrad r I.raw=TruncatedLP.gradSize (n:=I.n) (m:=I.m) (TruncatedLP.penalty r I.k) := by
  simp only [rawGrad,Input.raw,Input.rows,head_ofFn,List.length_ofFn,rawPenalty,TruncatedLP.gradSize,TruncatedLP.penalty]
theorem rawSteps_eq (r : ℕ) (I : Input) : rawSteps r I.raw=TruncatedLP.steps (n:=I.n) (m:=I.m) r I.k (TruncatedLP.penalty r I.k) := by
  unfold rawSteps
  rw [rawGrad_eq]
  rfl
theorem rawRate_eq (r : ℕ) (I : Input) : rawRate r I.raw=TruncatedLP.rate (n:=I.n) (m:=I.m) r (TruncatedLP.penalty r I.k) := by
  simp only [rawRate,rawGrad_eq,TruncatedLP.rate]

theorem start_eq (r : ℕ) (I : Input) : start r I=(rawContext r I.raw,I.iterate r 0) := by
  unfold start
  congr 1
  simp only [rawInitial,Input.raw,Input.rows,head_ofFn,List.length_ofFn,range_ofFn,List.map_ofFn,Input.iterate,Input.vector,ProjectedSubgradient.trajectory_zero]
  congr 1
  funext i
  simp only [ProjectedSubgradient.initial,ProjectedSubgradient.point_ofFn_apply]
  simp only [Fin.ext_iff,Function.comp_apply,Fin.val_zero]

theorem update_eq (r : ℕ) (I : Input) (t : ℕ) :
    update (rawContext r I.raw,I.iterate r t)=(rawContext r I.raw,I.iterate r (t+1)) := by
  unfold update
  congr 1
  change Truncated.next I.rows (I.iterate r t) (TruncatedLP.penalty r I.k) I.k (rawRate r I.raw)=I.iterate r (t+1)
  rw [rawRate_eq]
  unfold Input.rows Input.iterate
  rw [Truncated.next_ofFn]
  have he : Vector.ofFn (ProjectedSubgradient.point (I.vector r t))=I.vector r t := by ext index hindex; simp
  rw [he]
  rfl

theorem update_iterate (r : ℕ) (I : Input) (t : ℕ) :
    update^[t] (start r I)=(rawContext r I.raw,I.iterate r t) := by
  induction t with
  | zero => exact start_eq r I
  | succ t ih => rw [Function.iterate_succ_apply',ih,update_eq]
end MetricKMedian.LPBinary
end

end OAI
