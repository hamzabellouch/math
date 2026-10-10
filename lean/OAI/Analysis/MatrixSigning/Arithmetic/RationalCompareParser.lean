import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalComparePrimitives

namespace OAI

namespace KS.W06.RationalCompare
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def fields (input sa na da sb nb db : List Bool) : Fin 13 → List Bool :=
  ![input,sa,na,da,sb,nb,db,[],[],[],[],[],[]]

def leftNumeratorPorts : Fin 3 ↪ Fin 13 := ⟨![0,2,12], by decide⟩
def leftDenominatorPorts : Fin 3 ↪ Fin 13 := ⟨![0,3,12], by decide⟩
def rightNumeratorPorts : Fin 3 ↪ Fin 13 := ⟨![0,5,12], by decide⟩
def rightDenominatorPorts : Fin 3 ↪ Fin 13 := ⟨![0,6,12], by decide⟩

def pairBits (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : List Bool :=
  sa :: (KS.W01.frame na ++ KS.W01.frame da ++
    (sb :: (KS.W01.frame nb ++ KS.W01.frame db)))

def parseProgram : Program 13 :=
  compose (compose (compose (compose (compose
    (signProgram 0 1) (decodeProgram leftNumeratorPorts))
      (decodeProgram leftDenominatorPorts)) (signProgram 0 4))
        (decodeProgram rightNumeratorPorts)) (decodeProgram rightDenominatorPorts)

def parseTicks (na da nb db : List Bool) : ℕ :=
  3 * (na.length + da.length + nb.length + db.length) + 10

theorem parse_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec parseProgram (fields (pairBits sa na da sb nb db) [] [] [] [] [] [])
      (fields [] [sa] na da [sb] nb db) (parseTicks na da nb db) := by
  let tailB := sb :: (KS.W01.frame nb ++ KS.W01.frame db)
  let tailA := KS.W01.frame na ++ KS.W01.frame da ++ tailB
  have h1 : RunSpec (signProgram (0 : Fin 13) 1)
      (fields (pairBits sa na da sb nb db) [] [] [] [] [] [])
      (fields tailA [sa] [] [] [] [] []) 1 := by
    have h := sign_spec (0 : Fin 13) 1 (by decide)
      (fields (pairBits sa na da sb nb db) [] [] [] [] [] []) sa tailA rfl
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  have h2 : RunSpec (decodeProgram leftNumeratorPorts)
      (fields tailA [sa] [] [] [] [] [])
      (fields (KS.W01.frame da ++ tailB) [sa] na [] [] [] []) (3 * na.length + 2) := by
    have h := decode_spec leftNumeratorPorts (fields tailA [sa] [] [] [] [] [])
      na (KS.W01.frame da ++ tailB) (by simp [fields, leftNumeratorPorts, tailA, List.append_assoc]) rfl rfl
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  have h3 : RunSpec (decodeProgram leftDenominatorPorts)
      (fields (KS.W01.frame da ++ tailB) [sa] na [] [] [] [])
      (fields tailB [sa] na da [] [] []) (3 * da.length + 2) := by
    have h := decode_spec leftDenominatorPorts
      (fields (KS.W01.frame da ++ tailB) [sa] na [] [] [] []) da tailB rfl rfl rfl
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  have h4 : RunSpec (signProgram (0 : Fin 13) 4)
      (fields tailB [sa] na da [] [] [])
      (fields (KS.W01.frame nb ++ KS.W01.frame db) [sa] na da [sb] [] []) 1 := by
    have h := sign_spec (0 : Fin 13) 4 (by decide) (fields tailB [sa] na da [] [] [])
      sb (KS.W01.frame nb ++ KS.W01.frame db) rfl
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  have h5 : RunSpec (decodeProgram rightNumeratorPorts)
      (fields (KS.W01.frame nb ++ KS.W01.frame db) [sa] na da [sb] [] [])
      (fields (KS.W01.frame db) [sa] na da [sb] nb []) (3 * nb.length + 2) := by
    have h := decode_spec rightNumeratorPorts
      (fields (KS.W01.frame nb ++ KS.W01.frame db) [sa] na da [sb] [] [])
      nb (KS.W01.frame db) rfl rfl rfl
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  have h6 : RunSpec (decodeProgram rightDenominatorPorts)
      (fields (KS.W01.frame db) [sa] na da [sb] nb [])
      (fields [] [sa] na da [sb] nb db) (3 * db.length + 2) := by
    have h := decode_spec rightDenominatorPorts
      (fields (KS.W01.frame db) [sa] na da [sb] nb [])
      db [] (by simp [fields, rightDenominatorPorts]) rfl rfl
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  have h := ((((h1.compose h2).compose h3).compose h4).compose h5).compose h6
  convert h using 1 <;> first | rfl | (unfold parseTicks; omega)

def constructorBits (z : ℤ) : List Bool := Computability.encodeNat (KS.W01.intPayload z)
def negativeBit (z : ℤ) : Bool := decide (z < 0)

theorem pairBits_encodeRat (q r : ℚ) :
    pairBits (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den)
      (negativeBit r.num) (constructorBits r.num) (Computability.encodeNat r.den) =
      KS.W01.encodeRat q ++ KS.W01.encodeRat r := by
  have hi (z : ℤ) : KS.W01.encodeInt z = negativeBit z :: KS.W01.frame (constructorBits z) := by
    cases z <;> simp [KS.W01.encodeInt, KS.W01.encodeNat, KS.W01.intPayload,
      negativeBit, constructorBits]
  simp [pairBits, KS.W01.encodeRat, hi, KS.W01.encodeNat, List.append_assoc]

theorem pairBits_length (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    (pairBits sa na da sb nb db).length =
      2 * (na.length + da.length + nb.length + db.length) + 6 := by
  simp only [pairBits, List.length_cons, List.length_append, KS.W01.length_frame]
  omega

end KS.W06.RationalCompare

end OAI
