import Mathlib
import OAI.Analysis.MatrixSigning.Realization.ValueQueryRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialOptimize

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
instance poly_weightedSum : PolyTime weightedSum := by unfold weightedSum;apply poly_then
instance poly_veP : PolyTime veP := by unfold veP;infer_instance
instance poly_veY : PolyTime veY := by unfold veY;infer_instance
instance poly_veD : PolyTime veD := by unfold veD;apply poly_then
instance poly_veN : PolyTime veN := by unfold veN;apply poly_then
instance poly_veEye : PolyTime veEye := by unfold veEye;apply poly_then
instance poly_veEps : PolyTime veEps := by unfold veEps;apply poly_then
instance poly_veTime : PolyTime veTime := by unfold veTime;apply poly_then
instance poly_veVariable (b : Bool) : PolyTime (veVariable b) := by unfold veVariable;apply poly_then
instance poly_veSum : PolyTime veSum := by unfold veSum;apply poly_then
instance poly_sandwich : PolyTime sandwich := by unfold sandwich;apply poly_then
instance poly_eta : PolyTime eta := by unfold eta;apply poly_then
instance poly_schurEval (b : Bool) : PolyTime (schurEval b) := by unfold schurEval;apply poly_then
instance poly_lowerBox (b : Bool) : PolyTime (lowerBox b) := by unfold lowerBox;apply poly_then
instance poly_upperBox (b : Bool) : PolyTime (upperBox b) := by unfold upperBox;apply poly_then
instance poly_tinyMatrix : PolyTime tinyMatrix := by unfold tinyMatrix;apply poly_then
instance poly_blockWith {α : Type*} {ea : α → Word} {f g : α → MatrixData}
    (r : Realizes ea matrixCode f) (s : Realizes ea matrixCode g) [PolyTime r] [PolyTime s] :
    PolyTime (r.blockWith s) := by unfold Realizes.blockWith;infer_instance
instance poly_valueEval : PolyTime valueEval := by unfold valueEval;apply poly_blockWith
instance poly_traceMatrix : PolyTime traceMatrix := by unfold traceMatrix;apply poly_then
instance poly_valueObjective : PolyTime valueObjective := by unfold valueObjective;apply poly_add
instance poly_valueCoeffs : PolyTime valueCoeffs := by unfold valueCoeffs;apply poly_then
instance poly_valuePencil : PolyTime valuePencil := by unfold valuePencil;apply poly_then
instance poly_vqView : PolyTime vqView := by unfold vqView;apply poly_reindex
instance poly_vqData : PolyTime vqData := by unfold vqData;apply poly_then
instance poly_vqDelta : PolyTime vqDelta := by unfold vqDelta;apply poly_then
instance poly_valueLipschitz : PolyTime valueLipschitz := by unfold valueLipschitz;apply poly_mul
instance poly_valueOuterRadius : PolyTime valueOuterRadius := by unfold valueOuterRadius;apply poly_mul
instance poly_valueInnerRadius : PolyTime valueInnerRadius := by unfold valueInnerRadius;apply poly_div
instance poly_vqOpt : PolyTime vqOpt := by unfold vqOpt;apply poly_changeOutput

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_vqFuel (a : ι → ValueQueryParams)
    (ha : IsPoly L (fun i => (valueQueryCode (a i)).length))
    (hn : IsPoly L (fun i => RationalSDP.optimizeFuel (a i).delta 100)) :
    RunsPoly L vqFuel a := by
  unfold vqFuel
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.both
  · apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
    intro hw
    apply runsPoly_ratCeil _ hw
    apply hn.mono
    intro i
    change ⌈200/(a i).delta⌉₊≤⌈2*100/(a i).delta⌉₊+3
    norm_num
  · exact RunsPoly.of_poly _ a ha

lemma runsPoly_valueQueryPoint (a : ι → ValueQueryParams)
    (ha : IsPoly L (fun i => (valueQueryCode (a i)).length))
    (hk : IsPoly L (fun i => RationalSDP.optimizeFuel (a i).delta 100))
    (hn : IsPoly L (fun i => (a i).opt.searchCount)) : RunsPoly L valueQueryPoint a := by
  unfold valueQueryPoint
  apply RunsPoly.then_with ((RunsPoly.of_poly vqOpt a ha).both (runsPoly_vqFuel a ha hk))
  intro hw
  exact runsPoly_optimize _ hw hn
lemma runsPoly_valueQuery (a : ι → ValueQueryParams)
    (ha : IsPoly L (fun i => (valueQueryCode (a i)).length))
    (hk : IsPoly L (fun i => RationalSDP.optimizeFuel (a i).delta 100))
    (hn : IsPoly L (fun i => (a i).opt.searchCount)) : RunsPoly L valueQuery a := by
  unfold valueQuery
  apply RunsPoly.congr
  exact ((RunsPoly.of_poly vqData a ha).both (runsPoly_valueQueryPoint a ha hk hn)).then_poly valueObjective

def ValueQueryParams.scanCount (p : ValueQueryParams) : ℕ :=
  (RationalSDP.optimizeFuel p.delta 100+1)*p.opt.searchCount
lemma optFuel_le_scan (p : ValueQueryParams) : RationalSDP.optimizeFuel p.delta 100≤p.scanCount := by
  have hn : 1≤p.opt.searchCount := by unfold OptParams.searchCount RationalSDP.searchFuel;omega
  exact (Nat.le_succ _).trans (le_mul_of_one_le_right (Nat.zero_le _) hn)
lemma searchCount_le_scan (p : ValueQueryParams) : p.opt.searchCount≤p.scanCount :=
  le_mul_of_one_le_left (Nat.zero_le _) (by omega)
lemma runsPoly_valueQuery_scan (a : ι → ValueQueryParams)
    (ha : IsPoly L (fun i => (valueQueryCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).scanCount)) : RunsPoly L valueQuery a :=
  runsPoly_valueQuery a ha (hn.mono (fun i => optFuel_le_scan (a i)))
    (hn.mono (fun i => searchCount_le_scan (a i)))
end CurrentKS.Realization

end

end OAI
