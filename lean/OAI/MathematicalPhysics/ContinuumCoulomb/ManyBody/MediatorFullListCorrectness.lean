import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MediatorThreeStageProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MediatorOffsetProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorListCorrectness
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceBondLists

namespace OAI

/-! Exact list semantics for all three computed mediator stages and their
rational scalar offset. The emitted list is the full finite spin graph. -/

namespace ContinuumCoulomb.MediatorIteration
open MediatorListProgram MediatorUnaryProgram
open scoped BigOperators

def literalInput {n r : ℕ} (F : Bonds n r) (W G : ℕ) : Input := ((r, W, G, n), F.toList)

theorem secondInput_literal {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (secondEnv (literalInput F W G).1, MediatorListProgram.spokes (literalInput F W G)) =
      literalInput (firstSpokes F W G) (secondBound r W G) G := by
  apply Prod.ext
  · simp only [literalInput, secondEnv, secondBound]
    apply Prod.ext
    · omega
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · dsimp only
          omega
  · exact (spokes_toList_input F W G).symm

theorem secondPaths_toList {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (secondPaths F W G).toList =
      MediatorListProgram.central (secondEnv (literalInput F W G).1,
        MediatorListProgram.spokes (literalInput F W G)) ++
      MediatorListProgram.spokes (secondEnv (literalInput F W G).1,
        MediatorListProgram.spokes (literalInput F W G)) := by
  rw [secondInput_literal]
  unfold secondPaths
  rw [join_toList]
  exact congrArg₂ List.append
    (central_toList_input (firstSpokes F W G) (secondBound r W G) G)
    (spokes_toList_input (firstSpokes F W G) (secondBound r W G) G)

theorem thirdInput_literal {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (thirdEnv (literalInput F W G).1,
      MediatorListProgram.central (secondEnv (literalInput F W G).1,
        MediatorListProgram.spokes (literalInput F W G)) ++
      MediatorListProgram.spokes (secondEnv (literalInput F W G).1,
        MediatorListProgram.spokes (literalInput F W G))) =
      literalInput (secondPaths F W G) (thirdBound r W G) G := by
  apply Prod.ext
  · simp only [literalInput, thirdEnv, thirdBound]
    apply Prod.ext
    · omega
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · dsimp only
          omega
  · exact (secondPaths_toList F W G).symm

theorem finalGraph_toList {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (finalGraph F W G).toList = MediatorThreeStageProgram.finalBonds (literalInput F W G) := by
  unfold finalGraph retainedCentral
  rw [join_toList, lift_toList, lift_toList, join_toList]
  have hc1 := central_toList_input F W G
  have hc3 := central_toList_input (secondPaths F W G) (thirdBound r W G) G
  have hs3 := spokes_toList_input (secondPaths F W G) (thirdBound r W G) G
  change (firstCentral F W G).toList ++
    ((thirdCentral F W G).toList ++ (thirdSpokes F W G).toList) = _
  rw [show (firstCentral F W G).toList = MediatorListProgram.central (literalInput F W G) from hc1]
  rw [show (thirdCentral F W G).toList =
    MediatorListProgram.central (literalInput (secondPaths F W G) (thirdBound r W G) G) from hc3]
  rw [show (thirdSpokes F W G).toList =
    MediatorListProgram.spokes (literalInput (secondPaths F W G) (thirdBound r W G) G) from hs3]
  rw [← thirdInput_literal]
  simp only [MediatorThreeStageProgram.finalBonds, List.append_assoc]

theorem stageOffset_toList {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    MediatorOffsetProgram.stageOffset (literalInput F W G) =
      3 * r * MediatorParameters.delta r W G + 3 * ∑ e, |F.weight e| := by
  simp only [MediatorOffsetProgram.stageOffset, literalInput, Bonds.toList,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply]

theorem offset_toList {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    MediatorOffsetProgram.offset (literalInput F W G) = offset F W G := by
  unfold MediatorOffsetProgram.offset
  rw [thirdInput_literal, secondInput_literal]
  rw [stageOffset_toList, stageOffset_toList, stageOffset_toList]
  simp only [MediatorIteration.offset, deltaOne, deltaTwo, deltaThree, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add]

theorem bonds_toList (n : ℕ) (xs : List MediatorListProgram.Bond)
    (h : SourceBondLists.bounded n xs) : (SourceBondLists.bonds n xs h).toList = xs := by
  change List.ofFn (fun e => ((xs.get e).1, (xs.get e).2.1, (xs.get e).2.2)) = xs
  simpa only [Prod.eta] using List.ofFn_get xs

theorem Bonds.matrix_toList {n r : ℕ} (F : Bonds n r) :
    SourceBondLists.matrix n F.toList = F.matrix := by
  simp only [SourceBondLists.matrix, Bonds.toList, List.map_ofFn, List.sum_ofFn]
  unfold Bonds.matrix sourceGraphMatrix
  apply Finset.sum_congr rfl
  intro e _
  simp only [Function.comp_apply, SourceBondLists.bondMatrix, Fin.is_lt, and_self,
    dite_true, Fin.eta, Complex.ofReal_ratCast]

end ContinuumCoulomb.MediatorIteration

end OAI
