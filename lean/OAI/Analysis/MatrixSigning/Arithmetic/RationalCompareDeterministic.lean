import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.CanonicalRationalPairParser
import OAI.Analysis.MatrixSigning.Arithmetic.MultiplicationDeterministic

namespace OAI

section

namespace KS.W06.RationalCompareDeterministic

open KS.W29.Deterministic
open KS.W06.RationalCompare

theorem sign_coinIndependent {k : ℕ} (source target : Fin k) :
    CoinIndependent (signProgram source target) :=
  coinIndependent_compile (0 : Fin 1) source target (signDispatch source target)
    (fun _ _ _ _ => rfl)

theorem decode_coinIndependent {k : ℕ} (ports : Fin 3 ↪ Fin k) :
    CoinIndependent (decodeProgram ports) :=
  coinIndependent_lift3 _ ports KS.W03.MultiplicationDeterministic.frame_coinIndependent

private theorem liftedEntry_coinIndependent {k : ℕ} (M : KS.W29.BinaryMachine)
    (entry : Fin M.states) (ports : Fin 3 ↪ Fin k)
    (hM : ∀(c : KS.W29.Config M.states)(a b : Bool),M.step c a=M.step c b) :
    CoinIndependent (KS.W29.FixedSequential.ofMachine
      (KS.W01.FixedStack.lift3 (M.withEntry entry) ports)) :=
  coinIndependent_lift3 (M.withEntry entry) ports (coinIndependent_withEntry3 M entry hM)

theorem magnitudeCarry_coinIndependent {k : ℕ} (ports : Fin 3 ↪ Fin k) (carry : Bool) :
    CoinIndependent (KS.W01.MagnitudeProgram.program ports carry) :=
  liftedEntry_coinIndependent KS.W01.BinaryAdder.normalizedMachine
    (KS.W29.Sequential.leftState KS.W01.BinaryAdder.machine KS.W29.NormalizeOutput.machine
      (KS.W01.BinaryAdder.carryState carry)) ports
    (coinIndependent_compose3 KS.W01.BinaryAdder.machine KS.W29.NormalizeOutput.machine
      KS.W03.MultiplicationDeterministic.adder_coinIndependent
      KS.W03.MultiplicationDeterministic.reverse_coinIndependent)

theorem magnitude_coinIndependent {k : ℕ} (ports : Fin 3 ↪ Fin k) (signPort : Fin k) :
    CoinIndependent (magnitudeProgram ports signPort) :=
  coinIndependent_branch _ _ _ _ (magnitudeCarry_coinIndependent ports false)
    (magnitudeCarry_coinIndependent ports true) (fun _ _ _ => rfl)

theorem parse_coinIndependent : CoinIndependent parseProgram := by
  apply coinIndependent_compose
  · apply coinIndependent_compose
    · apply coinIndependent_compose
      · apply coinIndependent_compose
        · apply coinIndependent_compose
          · exact sign_coinIndependent _ _
          · exact decode_coinIndependent _
        · exact decode_coinIndependent _
      · exact sign_coinIndependent _ _
    · exact decode_coinIndependent _
  · exact decode_coinIndependent _

theorem prepare_coinIndependent : CoinIndependent prepareProgram :=
  coinIndependent_compose _ _
    (coinIndependent_compose _ _ parse_coinIndependent (magnitude_coinIndependent _ _))
    (magnitude_coinIndependent _ _)

theorem product_coinIndependent : CoinIndependent productProgram :=
  coinIndependent_compose _ _ KS.W03.MultiplicationDeterministic.loop_coinIndependent
    KS.W03.MultiplicationDeterministic.normalize_coinIndependent

theorem products_coinIndependent : CoinIndependent productsProgram :=
  coinIndependent_compose _ _ (coinIndependent_liftPorts _ _ product_coinIndependent)
    (coinIndependent_liftPorts _ _ product_coinIndependent)

theorem compare_coinIndependent {k : ℕ} (ports : Fin 3 ↪ Fin k) :
    CoinIndependent (KS.W28.FixedCompare.program ports) :=
  coinIndependent_lift3 _ _
    (coinIndependent_compile3 (KS.W28.LittleEndianCompare.encode .eq)
      KS.W28.LittleEndianCompare.dispatch (fun _ _ _ _ => rfl))

theorem signedCompare_coinIndependent {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (signLeft signRight : Fin k) : CoinIndependent (signedCompareProgram ports signLeft signRight) :=
  coinIndependent_branch _ _ _ _ (compare_coinIndependent _) (compare_coinIndependent _)
    (fun _ _ _ => rfl)

theorem coinIndependent : CoinIndependent KS.W06.RationalCompare.program :=
  coinIndependent_compose _ _
    (coinIndependent_compose _ _ prepare_coinIndependent products_coinIndependent)
    (signedCompare_coinIndependent _ _ _)

theorem singleBase_coinIndependent : CoinIndependent SingleRationalParser.baseProgram := by
  apply coinIndependent_compose
  · apply coinIndependent_compose
    · apply coinIndependent_compose
      · exact sign_coinIndependent _ _
      · exact decode_coinIndependent _
    · exact decode_coinIndependent _
  · exact magnitude_coinIndependent _ _

theorem singlePorts_coinIndependent {k : ℕ} (ports : Fin 6 ↪ Fin k) :
    CoinIndependent (SingleRationalParser.onPorts ports) :=
  coinIndependent_liftPorts _ _ singleBase_coinIndependent

theorem single_coinIndependent : CoinIndependent SingleRationalParser.program :=
  singlePorts_coinIndependent _

theorem canonicalPair_coinIndependent : CoinIndependent CanonicalRationalPairParser.program :=
  prepare_coinIndependent

end KS.W06.RationalCompareDeterministic

end

end OAI
