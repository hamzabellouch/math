import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.SurvivingWindows
import OAI.Combinatorics.RamseyFive.Marking.WindowLevels
import OAI.Combinatorics.RamseyFive.Entropy.WindowLossAggregation

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance swcProp (P : Prop) : Decidable P := Classical.propDecidable P
local instance swcBDE (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance swcIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  {w n : ℕ} [Nonempty (Fin n)] (p : Law (Slots w n→FlagPair K V))
  (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (E : Finset (Fin w)) (hE : E.Nonempty)
  {s : ℝ} (W : ReciprocalWindows p u sel (survivingOriginal E hE) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
  (c δ τ P : ℝ) (hδ : 0<δ)

abbrev WindowLevelsData (m : ℕ) :=
  (Fin (m+1)→Finset (ℙ K V))×(Fin (m+1)→Finset (ℙ K (Dual K V)))

def survivingLevelLaw : Law (WindowLevelsData (K:=K) (V:=V) E.card) :=
  originalLevelLaw (fun i=>(W.early i).firstLaw) (fun i=>(W.late i).secondLaw)
def survivingEncoded (t : VariableTreeTape f r w) (z : WindowLevelsData (K:=K) (V:=V) E.card) :
    VariableTreeMessage f r t (Finset.univ,Finset.univ) :=
  variableTreeEncoded f r t (Finset.univ,Finset.univ)
    ⟨E.card,Nat.lt_succ_of_le (by simpa using Finset.card_le_univ E)⟩ σ hσ hq hd
    (fun i=>W.firstSupport i (z.1 i)) (fun i=>W.secondSupport i (z.2 i))
    (fun i=>W.first_nonempty i _) (fun i=>W.second_nonempty i _) c δ τ P hδ

def survivingExperiment : Law ((Slots w n→FlagPair K V)×
    (WindowLevelsData (K:=K) (V:=V) E.card×VariableTreeTape f r w)) :=
  adaptiveLaw p (fun _=>adaptiveLaw (survivingLevelLaw p u sel E hE W) (fun _=>variableTreeLaw f r w))

def survivingTargetFailure (v : Fin w) (t : Fin (2*n)) : ℝ :=
  mean (survivingExperiment f r p u sel E hE W) (fun z=>
    if z.1 (middleSlot v t)∉variableTreeDomain f r z.2.2 (Finset.univ,Finset.univ)
      (survivingEncoded f r p u sel E hE W σ hσ hq hd c δ τ P hδ z.2.2 z.2.1)
      (survivorRank E v) then 1 else 0)

omit [Nonempty (Fin n)] in
lemma survivingTargetFailure_eq
    (hinc : ∀x,0<p x→∀i,Incident (x i).1 (x i).2) (v : Fin w) (hv : v∈E) (t : Fin (2*n)) :
    survivingTargetFailure f r p u sel E hE W σ hσ hq hd c δ τ P hδ v t=
      orientedTargetFailure f r σ hσ hq hd
        (fun i=>(W.early i).firstLaw) (fun i=>(W.late i).secondLaw)
        W.firstSupport W.secondSupport W.first_nonempty W.second_nonempty p
        (fun x=>(x (middleSlot v t)).1) (fun x=>(x (middleSlot v t)).2)
        c δ τ P hδ (finiteBalanced E.card)
        ((finiteRankEquiv E.card).symm ⟨(survivorRank E v).val,survivorRank_mem_lt E v hv⟩) := by
  unfold survivingTargetFailure survivingExperiment survivingEncoded survivingLevelLaw
  convert original_window_target_failure f r E hE σ hσ hq hd
    (fun i=>(W.early i).firstLaw) (fun i=>(W.late i).secondLaw)
    W.firstSupport W.secondSupport W.first_nonempty W.second_nonempty p hinc c δ τ P hδ v hv t using 1
end
end SharpRamseyFive.Marking

end OAI
