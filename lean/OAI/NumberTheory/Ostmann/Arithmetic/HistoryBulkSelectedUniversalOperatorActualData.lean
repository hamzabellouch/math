import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperatorPresent
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedJointIntegralBoundsInteger

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator
open Construction Conclusion HistoryBulkReferenceFrequencyFamily
open HistorySelectedJointIntegralBounds HistoryBulkGiantIntegerReference
open HistoryGiantXiReplacementActual HistoryGiantReferenceSourceBounds HistorySignedXiTransport
open HistoryBulkIntegralReplacement HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistoryPairSmoothXi HistoryPairBulkCoordinates HistoryGiantReferenceMean HistoryBulkGiantCorrectedBounds

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) {l : ℕ} {outside : List ℕ}
local notation "seed" => Template.initial (2*(bulkSize k L/2)) k
local notation "V" => frequencyBound Bs BD Bz k L
local notation "T" => Template.current seed l
variable {x y : InternalSourceDraws C.sources seed l}
  (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))

structure ActualReferenceData (C : InitialSourceChoice d Bs BD Bz k L E)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    {x y : InternalSourceDraws C.sources seed l} (i : RootFrequencyIndex V l)
    (r : SupportedReference C.sources seed V outside l x y i.1.val i.1.val i.2) where
  assignment : SourceAssignment C.sources T
  plus : ℤ
  minus : ℤ
  assignment_mass : (assignmentPrior C.sources T).mass assignment≠0
  left_choice_mass : choicesMass C.sources seed V l
    (assembleHistoryChoices C.sources seed V l i.2.1 x)≠0
  right_choice_mass : choicesMass C.sources seed V l
    (assembleHistoryChoices C.sources seed V l i.2.2 y)≠0
  plus_pos : 0 < plus
  minus_pos : 0 < minus
  plus_cell : |Real.log (plus:ℝ)-(C.giantCenter:ℝ)|≤1
  minus_cell : |Real.log (minus:ℝ)-(C.giantCenter:ℝ)|≤1
  left_eq : r.left=giantState (sourceState C.sources T assignment i.1.val) plus minus
  right_eq : r.right=giantState
    (sourceState C.sources T (permutedAssignment C l σ assignment) i.1.val) plus minus

end Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator

end

end OAI
