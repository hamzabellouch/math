import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPrivateRaw

namespace OAI

/-! Polynomial machine instructions for rational private-pair subdivision. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPrivate
open QuantumRawExchange ExactQuantumFactoring.BitStackProgram

noncomputable def scalarConstructor {α : Type} {ea : α → List Bool} {J : α → ℚ}
    (p : Procedure ea ratCode J) : Procedure ea rawCode (fun x => rawScalar (J x)) :=
  (Procedure.constant ea (prodCode Procedure.boolCode Procedure.boolCode) (false,false)).pair
    ((Procedure.constant ea (prodCode Nat.bits Nat.bits) (0,0)).pair
      ((Procedure.constant ea (prodCode Procedure.boolCode Procedure.boolCode) (false,false)).pair p))

noncomputable def fieldConstructor {α : Type} {ea : α → List Bool}
    {i : α → ℕ} {a : α → Bool} {J : α → ℚ}
    (pi : Procedure ea Nat.bits i) (pa : Procedure ea Procedure.boolCode a) (pJ : Procedure ea ratCode J) :
    Procedure ea rawCode (fun x => rawField (i x) (a x) (J x)) :=
  (Procedure.constant ea (prodCode Procedure.boolCode Procedure.boolCode) (false,true)).pair
    ((pi.pair (Procedure.constant ea Nat.bits 0)).pair
      ((pa.pair (Procedure.constant ea Procedure.boolCode false)).pair pJ))

noncomputable def pairConstructor {α : Type} {ea : α → List Bool}
    {i j : α → ℕ} {a b : α → Bool} {J : α → ℚ}
    (pi : Procedure ea Nat.bits i) (pj : Procedure ea Nat.bits j)
    (pa : Procedure ea Procedure.boolCode a) (pb : Procedure ea Procedure.boolCode b)
    (pJ : Procedure ea ratCode J) : Procedure ea rawCode (fun x => rawPair (i x) (j x) (a x) (b x) (J x)) :=
  (Procedure.constant ea (prodCode Procedure.boolCode Procedure.boolCode) (true,false)).pair
    ((pi.pair pj).pair ((pa.pair pb).pair pJ))

abbrev BlockInput := (ℕ × ℚ) × (ℕ × Raw)
def blockCode : BlockInput → List Bool :=
  prodCode (prodCode Nat.bits ratCode) (prodCode Nat.bits rawCode)

noncomputable opaque envProgram : Procedure blockCode (prodCode Nat.bits ratCode) Prod.fst := Procedure.first _ _
noncomputable opaque indexRawProgram : Procedure blockCode (prodCode Nat.bits rawCode) Prod.snd := Procedure.second _ _
noncomputable opaque countProgram : Procedure blockCode Nat.bits (fun x => x.1.1) :=
  (Procedure.first _ _).comp envProgram
noncomputable opaque radiusProgram : Procedure blockCode ratCode (fun x => x.1.2) :=
  (Procedure.second _ _).comp envProgram
noncomputable opaque indexProgram : Procedure blockCode Nat.bits (fun x => x.2.1) :=
  (Procedure.first _ _).comp indexRawProgram
noncomputable opaque rawProgram : Procedure blockCode rawCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp indexRawProgram
noncomputable opaque viewProgram : Procedure blockCode QuantumRawExchange.inputCode
    (fun x => ((0,x.1.2),x.2.2)) :=
  ((Procedure.constant blockCode unaryCode 0).pair radiusProgram).pair rawProgram
noncomputable opaque freshProgram : Procedure blockCode Nat.bits (fun x => x.1.1+x.2.1) :=
  Procedure.binaryAdd.comp (countProgram.pair indexProgram)
noncomputable opaque coefficientProgram : Procedure blockCode ratCode (fun x => x.2.2.2.2.2) :=
  QuantumRawExchange.weightProgram.comp viewProgram
noncomputable opaque pairFlagProgram : Procedure blockCode Procedure.boolCode (fun x => x.2.2.1.1) :=
  QuantumRawExchange.pairFlagProgram.comp viewProgram
noncomputable opaque leftFlagProgram : Procedure blockCode Procedure.boolCode
    (fun x => x.2.2.1.1 || x.2.2.1.2) :=
  (Procedure.conditional pairFlagProgram (Procedure.constant blockCode Procedure.boolCode true)
    (QuantumRawExchange.fieldFlagProgram.comp viewProgram)).congrFun
      (by intro x; cases x.2.2.1.1 <;> rfl)
noncomputable opaque oldLeftProgram : Procedure blockCode Nat.bits (fun x => x.2.2.2.1.1) :=
  QuantumRawExchange.leftProgram.comp viewProgram
noncomputable opaque oldRightProgram : Procedure blockCode Nat.bits (fun x => x.2.2.2.1.2) :=
  QuantumRawExchange.rightProgram.comp viewProgram
noncomputable opaque axisLeftProgram : Procedure blockCode Procedure.boolCode (fun x => x.2.2.2.2.1.1) :=
  QuantumRawExchange.axisLeftProgram.comp viewProgram
noncomputable opaque axisRightProgram : Procedure blockCode Procedure.boolCode (fun x => x.2.2.2.2.1.2) :=
  QuantumRawExchange.axisRightProgram.comp viewProgram
noncomputable opaque radiusSquareProgram : Procedure blockCode ratCode (fun x => x.1.2^2) :=
  (Procedure.ratMul.comp (radiusProgram.pair radiusProgram)).congrFun
    (by intro x; change _*_ = _^2; ring)
noncomputable opaque radiusHalfProgram : Procedure blockCode ratCode (fun x => x.1.2^2/2) :=
  Procedure.ratDiv.comp (radiusSquareProgram.pair (Procedure.constant blockCode ratCode 2))
noncomputable opaque coefficientHalfProgram : Procedure blockCode ratCode (fun x => x.2.2.2.2.2/2) :=
  Procedure.ratDiv.comp (coefficientProgram.pair (Procedure.constant blockCode ratCode 2))
noncomputable opaque coefficientSquareProgram : Procedure blockCode ratCode (fun x => (x.2.2.2.2.2/2)^2) :=
  (Procedure.ratMul.comp (coefficientHalfProgram.pair coefficientHalfProgram)).congrFun
    (by intro x; change _*_ = _^2; ring)
noncomputable opaque zeroWeightProgram : Procedure blockCode ratCode
    (fun x => x.1.2^2/2+1+(x.2.2.2.2.2/2)^2) :=
  Procedure.ratAdd.comp ((Procedure.ratAdd.comp
    (radiusHalfProgram.pair (Procedure.constant blockCode ratCode 1))).pair coefficientSquareProgram)
noncomputable opaque lastWeightProgram : Procedure blockCode ratCode (fun x => -x.1.2*x.2.2.2.2.2/2) :=
  Procedure.ratDiv.comp ((Procedure.ratMul.comp
    ((Procedure.ratNeg.comp radiusProgram).pair coefficientProgram)).pair (Procedure.constant blockCode ratCode 2))

noncomputable opaque weightProgram (k : Fin 4) : Procedure blockCode ratCode
    (fun x => weight x.1.2 x.2.2.2.2.2 k) := by
  by_cases h0 : k = 0
  · subst k
    exact zeroWeightProgram.congrFun (by intro x; rfl)
  by_cases h1 : k = 1
  · subst k
    exact (Procedure.ratNeg.comp radiusHalfProgram).congrFun (by
      intro x
      change -(x.1.2^2/2) = -x.1.2^2/2
      ring)
  by_cases h2 : k = 2
  · subst k
    exact radiusProgram.congrFun (by intro x; rfl)
  have h3 : k = 3 := by omega
  subst k
  exact lastWeightProgram.congrFun (by intro x; rfl)

noncomputable opaque termProgram (k : Fin 4) : Procedure blockCode rawCode
    (fun x => rawTerm x.1.1 x.2.1 x.1.2 x.2.2 k) := by
  let p := weightProgram k
  let yes := Procedure.constant blockCode Procedure.boolCode true
  let no := Procedure.constant blockCode Procedure.boolCode false
  by_cases h0 : k = 0
  · exact (scalarConstructor p).congrFun (by intro x; simp [rawTerm,h0])
  by_cases h1 : k = 1
  · exact (fieldConstructor freshProgram no p).congrFun (by intro x; simp [rawTerm,h1])
  by_cases h2 : k = 2
  · exact (Procedure.conditional leftFlagProgram
      (pairConstructor oldLeftProgram freshProgram axisLeftProgram yes p)
      (fieldConstructor freshProgram yes p)).congrFun (by intro x; simp [rawTerm,h2])
  · exact (Procedure.conditional pairFlagProgram
      (pairConstructor oldRightProgram freshProgram axisRightProgram yes p)
      (fieldConstructor freshProgram yes p)).congrFun (by intro x; simp [rawTerm,h0,h1,h2])

noncomputable opaque blockProgram : Procedure blockCode (listCode rawCode)
    (fun x => rawBlock x.1.1 x.2.1 x.1.2 x.2.2) :=
  fixedListProgram blockCode rawCode 4 _ termProgram

noncomputable def blockCertificate : Turing.TM2ComputableInPolyTime blockCode (listCode rawCode)
    (fun x => rawBlock x.1.1 x.2.1 x.1.2 x.2.2) := blockProgram.toTM2

end ContinuumCoulomb.QuantumPrivate

end

end OAI
