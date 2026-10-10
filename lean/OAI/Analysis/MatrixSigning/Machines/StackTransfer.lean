import Mathlib
import OAI.Analysis.MatrixSigning.Machines.StackTransferSpecs

namespace OAI

section

namespace KS.W12.StackTransfer
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def program {k : ℕ} (source target scratch : Fin k) : Program k :=
  compose (KS.W04.BinaryStackMoves.moveProgram source scratch)
    (KS.W04.BinaryStackMoves.moveProgram scratch target)

def after {k : ℕ} (source target : Fin k) (before : Fin k → List Bool) : Fin k → List Bool :=
  fun j => if j = source then [] else if j = target then before source ++ before target else before j

theorem spec {k : ℕ} (source target scratch : Fin k) (hst : source ≠ target)
    (hs : source ≠ scratch) (ht : target ≠ scratch)
    (before : Fin k → List Bool) (htmp : before scratch = []) :
    RunSpec (program source target scratch) before (after source target before)
      (2 * (before source).length + 2) := by
  have h1 := KS.W15.RationalMultiply.move_spec source scratch hs before
  have h2 := KS.W15.RationalMultiply.move_spec scratch target ht.symm
    (KS.W15.RationalMultiply.moveAfter source scratch before)
  have he : KS.W15.RationalMultiply.moveAfter scratch target
      (KS.W15.RationalMultiply.moveAfter source scratch before) = after source target before := by
    funext j
    by_cases hj : j = source
    · subst j
      simp [KS.W15.RationalMultiply.moveAfter, after, hs, hst]
    · by_cases hk : j = target
      · subst j
        simp [KS.W15.RationalMultiply.moveAfter, after, hs.symm, ht, hst.symm, htmp]
      · by_cases hr : j = scratch
        · subst j
          simp [KS.W15.RationalMultiply.moveAfter, after, hs.symm, ht.symm, htmp]
        · simp [KS.W15.RationalMultiply.moveAfter, after, hj, hk, hr]
  have hlen : (KS.W15.RationalMultiply.moveAfter source scratch before scratch).length =
      (before source).length := by
    simp [KS.W15.RationalMultiply.moveAfter, hs.symm, htmp]
  have htime : ((before source).length + 1) +
      ((KS.W15.RationalMultiply.moveAfter source scratch before scratch).length + 1) =
        2 * (before source).length + 2 := by
    rw [hlen]
    omega
  have hh := h1.compose h2
  rw [he, htime] at hh
  exact hh

end KS.W12.StackTransfer

end

end OAI
