import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingCalibration
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOffsetProgram

namespace OAI

/-! Literal polynomial rational programs for the crossing coefficients and penalty. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRoutingCode
open ExactQuantumFactoring.BitStackProgram

abbrev Triple := ℚ × (ℚ × ℚ)
def tripleCode : Triple → List Bool := prodCode ratCode (prodCode ratCode ratCode)

noncomputable opaque firstProgram : Procedure tripleCode ratCode Prod.fst := Procedure.first _ _
noncomputable opaque tailProgram : Procedure tripleCode (prodCode ratCode ratCode) Prod.snd :=
  Procedure.second _ _
noncomputable opaque secondProgram : Procedure tripleCode ratCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp tailProgram
noncomputable opaque thirdProgram : Procedure tripleCode ratCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp tailProgram

noncomputable def squareProgram {α : Type} {ea : α → List Bool} {f : α → ℚ}
    (p : Procedure ea ratCode f) : Procedure ea ratCode (fun x => (f x)^2) :=
  (Procedure.ratMul.comp (p.pair p)).congrFun (by intro x; dsimp; ring)

noncomputable def twiceProductProgram {α : Type} {ea : α → List Bool} {f g : α → ℚ}
    (p : Procedure ea ratCode f) (q : Procedure ea ratCode g) :
    Procedure ea ratCode (fun x => 2*f x*g x) :=
  Procedure.ratMul.comp ((Procedure.ratMul.comp
    ((Procedure.constant ea ratCode 2).pair p)).pair q)

noncomputable opaque sumPlusOneProgram : Procedure tripleCode ratCode
    (fun x => x.1+x.2.1+1) :=
  Procedure.ratAdd.comp ((Procedure.ratAdd.comp (firstProgram.pair secondProgram)).pair
    (Procedure.constant tripleCode ratCode 1))

noncomputable opaque cubeProgram : Procedure tripleCode ratCode (fun x => (x.1+x.2.1+1)^3) :=
  (Procedure.ratMul.comp ((squareProgram sumPlusOneProgram).pair sumPlusOneProgram)).congrFun
    (by intro x; dsimp; ring)

noncomputable opaque scaleProgram : Procedure tripleCode ratCode
    (fun x => 16*(x.1+x.2.1+1)^3*x.2.2+4*(x.1+x.2.1+1)+1) := by
  let leading := Procedure.ratMul.comp ((Procedure.ratMul.comp
    ((Procedure.constant tripleCode ratCode 16).pair cubeProgram)).pair thirdProgram)
  let lower := Procedure.ratMul.comp ((Procedure.constant tripleCode ratCode 4).pair sumPlusOneProgram)
  exact Procedure.ratAdd.comp ((Procedure.ratAdd.comp (leading.pair lower)).pair
    (Procedure.constant tripleCode ratCode 1))

noncomputable def scaleCertificate : Turing.TM2ComputableInPolyTime tripleCode ratCode
    (fun x => 16*(x.1+x.2.1+1)^3*x.2.2+4*(x.1+x.2.1+1)+1) := scaleProgram.toTM2

theorem scale_cast (x : Triple) :
    ((16*(x.1+x.2.1+1)^3*x.2.2+4*(x.1+x.2.1+1)+1:ℚ):ℝ) =
      qmaRoutingScale (x.1:ℝ) (x.2.1:ℝ) (x.2.2:ℝ) := by
  simp [qmaRoutingScale]

noncomputable opaque offsetProgram : Procedure tripleCode ratCode
    (fun x => 3/2+3*x.2.1^2+3*x.2.2^2) := by
  let j := Procedure.ratMul.comp ((Procedure.constant tripleCode ratCode 3).pair (squareProgram secondProgram))
  let k := Procedure.ratMul.comp ((Procedure.constant tripleCode ratCode 3).pair (squareProgram thirdProgram))
  exact Procedure.ratAdd.comp ((Procedure.ratAdd.comp
    ((Procedure.constant tripleCode ratCode (3/2)).pair j)).pair k)

def coefficients (x : Triple) : Fin 10 → ℚ :=
  ![x.1^2,x.1,x.1,2*x.1*x.2.1,2*x.1*x.2.2,
    1/2,-x.2.2,-x.2.1,2*x.2.1*x.2.2,3/2+3*x.2.1^2+3*x.2.2^2+3*x.1^2]

noncomputable opaque coefficientProgram (k : Fin 10) :
    Procedure tripleCode ratCode (fun x => coefficients x k) := by
  by_cases h0 : k = 0
  · subst k
    exact (squareProgram firstProgram).congrFun (by intro x; rfl)
  by_cases h1 : k = 1
  · subst k
    exact firstProgram.congrFun (by intro x; rfl)
  by_cases h2 : k = 2
  · subst k
    exact firstProgram.congrFun (by intro x; rfl)
  by_cases h3 : k = 3
  · subst k
    exact (twiceProductProgram firstProgram secondProgram).congrFun (by intro x; rfl)
  by_cases h4 : k = 4
  · subst k
    exact (twiceProductProgram firstProgram thirdProgram).congrFun (by intro x; rfl)
  by_cases h5 : k = 5
  · subst k
    exact (Procedure.constant tripleCode ratCode (1/2)).congrFun (by intro x; rfl)
  by_cases h6 : k = 6
  · subst k
    exact (Procedure.ratNeg.comp thirdProgram).congrFun (by intro x; rfl)
  by_cases h7 : k = 7
  · subst k
    exact (Procedure.ratNeg.comp secondProgram).congrFun (by intro x; rfl)
  by_cases h8 : k = 8
  · subst k
    exact (twiceProductProgram secondProgram thirdProgram).congrFun (by intro x; rfl)
  have h9 : k = 9 := by omega
  subst k
  exact (Procedure.ratAdd.comp (offsetProgram.pair
      (Procedure.ratMul.comp ((Procedure.constant tripleCode ratCode 3).pair
        (squareProgram firstProgram))))).congrFun (by intro x; rfl)

noncomputable opaque coefficientListProgram : Procedure tripleCode (listCode ratCode)
    (fun x => List.ofFn (coefficients x)) :=
  QuantumRawExchange.fixedListProgram tripleCode ratCode 10 (fun k x => coefficients x k) coefficientProgram

noncomputable def coefficientListCertificate : Turing.TM2ComputableInPolyTime
    tripleCode (listCode ratCode) (fun x => List.ofFn (coefficients x)) := coefficientListProgram.toTM2

theorem coefficients_spoke (x : Triple) (a : Fin 4) :
    (coefficients x ⟨a.val+1,by omega⟩ : ℝ) =
      qmaCrossingAmplitude (x.1:ℝ) (x.2.1:ℝ) (x.2.2:ℝ) a := by
  fin_cases a <;> simp [coefficients,qmaCrossingAmplitude]

theorem coefficients_perimeter (x : Triple) (a : Fin 4) :
    (coefficients x ⟨a.val+5,by omega⟩ : ℝ) = qmaCrossingWeight (x.2.1:ℝ) (x.2.2:ℝ) a := by
  fin_cases a <;> simp [coefficients,qmaCrossingWeight]

theorem coefficients_offset (x : Triple) :
    (coefficients x 9 : ℝ) = qmaCrossingOffset (x.2.1:ℝ) (x.2.2:ℝ)+3*(x.1:ℝ)^2 := by
  simp [coefficients,qmaCrossingOffset]

end ContinuumCoulomb.QuantumRoutingCode

end

end OAI
