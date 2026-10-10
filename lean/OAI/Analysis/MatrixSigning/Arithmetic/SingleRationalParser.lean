import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalCompareProgram
import OAI.Analysis.MatrixSigning.Arithmetic.ArithmeticEncodingSize

namespace OAI

namespace KS.W06.SingleRationalParser

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare

theorem magnitude_result_canonical (carry : Bool) (xs : List Bool)
    (hx : KS.W19.CanonicalBits xs) :
    KS.W19.CanonicalBits (KS.W01.MagnitudeProgram.result carry xs) := by
  induction xs generalizing carry with
  | nil =>
    cases carry <;> simp [KS.W01.MagnitudeProgram.result, KS.W01.BinaryAdder.addBits,
      KS.W19.CanonicalBits]
  | cons b bs ih =>
    rcases hx with ⟨hbs, hlast⟩
    rw [KS.W01.MagnitudeProgram.result, KS.W01.BinaryAdder.addBits]
    refine ⟨ih _ hbs, ?_⟩
    intro hnil
    cases bs with
    | cons d ds => simp [KS.W01.BinaryAdder.addBits] at hnil
    | nil =>
      have hb : b = true := hlast rfl
      subst b
      cases carry <;>
        simp [KS.W01.BinaryAdder.addBits, KS.W01.BinaryAdder.carryBit,
          KS.W01.BinaryAdder.sumBit] at hnil ⊢

theorem magnitude_constructor_eq (z : ℤ) :
    KS.W01.MagnitudeProgram.result (negativeBit z) (constructorBits z) =
      Computability.encodeNat z.natAbs := by
  apply KS.W19.canonicalBits_injective
    (magnitude_result_canonical _ _ (KS.W19.canonicalBits_encodeNat _))
    (KS.W19.canonicalBits_encodeNat _)
  rw [KS.W01.MagnitudeProgram.result_value, KS.W19.bitsValue_encodeNat]
  simp only [KS.W19.bitsValue_encodeNat]
  cases z <;> simp [negativeBit, KS.W01.intPayload, KS.W19.digit]

def numeratorPorts : Fin 3 ↪ Fin 6 := ⟨![0,3,2], by decide⟩
def denominatorPorts : Fin 3 ↪ Fin 6 := ⟨![0,4,2], by decide⟩
def magnitudePorts : Fin 3 ↪ Fin 6 := ⟨![1,3,2], by decide⟩

def baseState (input num den sign : List Bool) : Fin 6 → List Bool :=
  ![input,[],[],num,den,sign]

def baseProgram : Program 6 :=
  compose (compose (compose (signProgram 0 5) (decodeProgram numeratorPorts))
    (decodeProgram denominatorPorts)) (magnitudeProgram magnitudePorts 5)

def baseTicks (num den : List Bool) : ℕ := 5 * num.length + 3 * den.length + 9

theorem base_spec (sign : Bool) (num den tail : List Bool) :
    RunSpec baseProgram
      (baseState (sign :: (KS.W01.frame num ++ KS.W01.frame den ++ tail)) [] [] [])
      (baseState tail (KS.W01.MagnitudeProgram.result sign num) den [sign])
      (baseTicks num den) := by
  let rest := KS.W01.frame num ++ KS.W01.frame den ++ tail
  have hs : RunSpec (signProgram (0 : Fin 6) 5)
      (baseState (sign :: rest) [] [] []) (baseState rest [] [] [sign]) 1 := by
    have h := sign_spec (0 : Fin 6) 5 (by decide) (baseState (sign :: rest) [] [] []) sign rest rfl
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  have hn : RunSpec (decodeProgram numeratorPorts) (baseState rest [] [] [sign])
      (baseState (KS.W01.frame den ++ tail) num [] [sign]) (3 * num.length + 2) := by
    have h := decode_spec numeratorPorts (baseState rest [] [] [sign])
      num (KS.W01.frame den ++ tail) (by simp [baseState, numeratorPorts, rest, List.append_assoc]) rfl rfl
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  have hd : RunSpec (decodeProgram denominatorPorts)
      (baseState (KS.W01.frame den ++ tail) num [] [sign])
      (baseState tail num den [sign]) (3 * den.length + 2) := by
    have h := decode_spec denominatorPorts (baseState (KS.W01.frame den ++ tail) num [] [sign])
      den tail rfl rfl rfl
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  have hm : RunSpec (magnitudeProgram magnitudePorts 5) (baseState tail num den [sign])
      (baseState tail (KS.W01.MagnitudeProgram.result sign num) den [sign]) (2 * num.length + 4) := by
    have h := magnitude_spec magnitudePorts 5 (baseState tail num den [sign]) sign num rfl rfl rfl rfl
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  have h := ((hs.compose hn).compose hd).compose hm
  convert h using 1 <;> (try rfl)
  unfold baseTicks
  omega

theorem singleBits_encodeRat (q : ℚ) (tail : List Bool) :
    negativeBit q.num :: (KS.W01.frame (constructorBits q.num) ++
      KS.W01.frame (Computability.encodeNat q.den) ++ tail) = KS.W01.encodeRat q ++ tail := by
  have hi (z : ℤ) : KS.W01.encodeInt z = negativeBit z :: KS.W01.frame (constructorBits z) := by
    cases z <;> simp [KS.W01.encodeInt, KS.W01.encodeNat, KS.W01.intPayload,
      negativeBit, constructorBits]
  simp [KS.W01.encodeRat, hi, KS.W01.encodeNat, List.append_assoc]

theorem canonical_base_spec (q : ℚ) (tail : List Bool) :
    RunSpec baseProgram (baseState (KS.W01.encodeRat q ++ tail) [] [] [])
      (baseState tail (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
        [decide (q.num < 0)])
      (baseTicks (constructorBits q.num) (Computability.encodeNat q.den)) := by
  have h := base_spec (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den) tail
  rw [singleBits_encodeRat, magnitude_constructor_eq] at h
  exact h

theorem canonical_ticks_le (q : ℚ) :
    baseTicks (constructorBits q.num) (Computability.encodeNat q.den) ≤
      8 * (KS.W01.ratLength q + 1) := by
  have hlen := congrArg List.length (singleBits_encodeRat q [])
  simp only [List.length_cons, List.length_append, KS.W01.length_frame,
    List.length_nil, Nat.add_zero] at hlen
  unfold baseTicks KS.W01.ratLength
  omega

def onPorts {k : ℕ} (ports : Fin 6 ↪ Fin k) : Program k :=
  KS.W29.FixedSequential.liftPorts baseProgram ports

theorem onPorts_spec {k : ℕ} (ports : Fin 6 ↪ Fin k)
    (before : Fin k → List Bool) (q : ℚ) (tail : List Bool)
    (hbefore : (fun i => before (ports i)) = baseState (KS.W01.encodeRat q ++ tail) [] [] []) :
    RunSpec (onPorts ports) before
      (replacePorts ports before
        (baseState tail (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
          [decide (q.num < 0)])) (8 * (KS.W01.ratLength q + 1)) := by
  apply (runSpec_liftPorts baseProgram ports before _ _ ?_).mono (canonical_ticks_le q)
  rw [hbefore]
  exact canonical_base_spec q tail

def normalizerPorts : Fin 6 ↪ Fin 13 := ⟨![0,1,2,10,11,12], by decide⟩
def program : Program 13 := onPorts normalizerPorts
def machine : Machine := program.toMachine

def state (tail num den : List Bool) (sign : Bool) : Fin 13 → List Bool :=
  ![tail,[],[],[],[],[],[],[],[],[],num,den,[sign]]

def inputState (input : List Bool) : Fin 13 → List Bool :=
  ![input,[],[],[],[],[],[],[],[],[],[],[],[]]

def canonicalState (q : ℚ) (tail : List Bool := []) : Fin 13 → List Bool :=
  state tail (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
    (decide (q.num < 0))

theorem canonical_spec (q : ℚ) (tail : List Bool) :
    RunSpec program (inputState (KS.W01.encodeRat q ++ tail)) (canonicalState q tail)
      (8 * (KS.W01.ratLength q + 1)) := by
  have h := onPorts_spec normalizerPorts (inputState (KS.W01.encodeRat q ++ tail)) q tail
    (by funext i; fin_cases i <;> rfl)
  convert h using 1 <;> first | rfl | (funext i; fin_cases i <;> rfl)

theorem init_eq (input : List Bool) : machine.init input = ⟨some program.initial, inputState input⟩ := by
  apply congrArg (Config.mk (some program.initial))
  funext i
  fin_cases i <;> rfl

theorem run_input (q : ℚ) (tail bits : List Bool)
    (hlen : 8 * (KS.W01.ratLength q + 1) ≤ bits.length) :
    machine.run (machine.init (KS.W01.encodeRat q ++ tail)) bits =
      ⟨none, canonicalState q tail⟩ := by
  rw [init_eq]
  exact (canonical_spec q tail).run_of_le bits hlen

theorem halts_input (q : ℚ) (tail : List Bool) :
    machine.HaltsWithin (KS.W01.encodeRat q ++ tail) (8 * (KS.W01.ratLength q + 1)) := by
  intro seed
  exact congrArg Config.state (run_input q tail (List.ofFn seed) (by simp; omega))

end KS.W06.SingleRationalParser

end OAI
