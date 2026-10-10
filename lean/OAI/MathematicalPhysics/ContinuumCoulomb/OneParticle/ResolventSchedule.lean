import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalHeatBox

namespace OAI

/-! Literal polynomial-sized mesh and precision choices for the resolvent
quadrature. The radius and requested inverse accuracy are unary inputs. -/

namespace ContinuumCoulomb.ResolventSchedule
open ExactQuantumFactoring.BitStackProgram

def scale (P : ℕ) : ℕ := 16 * (P + 1)
def countPrefix (R : ℕ) : ℕ := 4096 * (R + 3) ^ 4
def count (R P : ℕ) : ℕ := countPrefix R * scale P ^ 8
def magnitude (R P : ℕ) : ℕ := (R + 3) ^ 2 * scale P
def precision (P : ℕ) : ℕ := 4 * scale P

abbrev Input := (ℕ × ℕ) × RationalHeatSample.Point
def inputCode : Input → List Bool :=
  prodCode (prodCode unaryCode unaryCode) RationalHeatSample.pointCode

def argument (x : Input) : RationalHeatBox.Input :=
  let R := x.1.1
  let P := x.1.2
  let N := count R P
  let Q := (scale P : ℚ)
  (N, (((magnitude R P, (precision P, N)), (x.2, N)), (Q⁻¹, (Q - Q⁻¹) / N)))

def approximate (x : Input) : ℚ := RationalHeatBox.value (argument x)

noncomputable opaque mulProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => x.1 * x.2) := Procedure.unaryMul

noncomputable opaque addProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => x.1 + x.2) := Procedure.unaryAdd

noncomputable opaque scaleProgram : Procedure unaryCode unaryCode scale := by
  let sixteen := Procedure.constant unaryCode unaryCode 16
  exact (mulProgram.comp (sixteen.pair Procedure.unarySuccessor)).congrFun
    (by intro P; rfl)

noncomputable opaque squareProgram : Procedure unaryCode unaryCode (fun n => n ^ 2) :=
  (mulProgram.comp ((Procedure.identity unaryCode).pair (Procedure.identity unaryCode))).congrFun
    (by intro n; exact (pow_two n).symm)

noncomputable opaque fourthProgram : Procedure unaryCode unaryCode (fun n => n ^ 4) :=
  (squareProgram.comp squareProgram).congrFun (by intro n; dsimp; ring)

noncomputable opaque eighthProgram : Procedure unaryCode unaryCode (fun n => n ^ 8) :=
  (squareProgram.comp fourthProgram).congrFun (by intro n; dsimp; ring)

noncomputable opaque constant4096Program :
    Procedure (prodCode unaryCode unaryCode) unaryCode (fun _ => 4096) :=
  (fourthProgram.comp (Procedure.constant (prodCode unaryCode unaryCode) unaryCode 8)).congrFun
    (by intro x; norm_num)

noncomputable opaque radiusOffsetProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x : ℕ × ℕ => x.1 + 3) :=
  (addProgram.comp ((Procedure.first unaryCode unaryCode).pair
    (Procedure.constant (prodCode unaryCode unaryCode) unaryCode 3))).congrFun
      (by intro x; rfl)

noncomputable opaque radiusFourthProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x : ℕ × ℕ => (x.1 + 3) ^ 4) :=
  fourthProgram.comp radiusOffsetProgram

noncomputable opaque scaleEighthProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x : ℕ × ℕ => scale x.2 ^ 8) :=
  eighthProgram.comp (scaleProgram.comp (Procedure.second unaryCode unaryCode))

noncomputable opaque countPrefixProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x : ℕ × ℕ => countPrefix x.1) :=
  (mulProgram.comp (constant4096Program.pair radiusFourthProgram)).congrFun
    (by intro x; rfl)

noncomputable opaque countFactorsProgram :
    Procedure (prodCode unaryCode unaryCode) (prodCode unaryCode unaryCode)
      (fun x : ℕ × ℕ => (countPrefix x.1, scale x.2 ^ 8)) :=
  countPrefixProgram.pair scaleEighthProgram

noncomputable opaque countRawProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x : ℕ × ℕ => countPrefix x.1 * scale x.2 ^ 8) :=
  mulProgram.comp countFactorsProgram

theorem count_value (x : ℕ × ℕ) : countPrefix x.1 * scale x.2 ^ 8 = count x.1 x.2 := by
  unfold count
  rfl

noncomputable opaque countProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => count x.1 x.2) := countRawProgram.congrFun count_value

noncomputable opaque magnitudeProgram : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => magnitude x.1 x.2) := by
  let R := Procedure.first unaryCode unaryCode
  let Q := scaleProgram.comp (Procedure.second unaryCode unaryCode)
  let three := Procedure.constant (prodCode unaryCode unaryCode) unaryCode 3
  let R3 := addProgram.comp (R.pair three)
  let square := squareProgram.comp R3
  exact (mulProgram.comp (square.pair Q)).congrFun (by
    intro x
    rfl)

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode precision := by
  let four := Procedure.constant unaryCode unaryCode 4
  exact (mulProgram.comp (four.pair scaleProgram)).congrFun (by intro P; rfl)

noncomputable opaque argumentProgram :
    Procedure inputCode RationalHeatBox.inputCode argument := by
  let rp := Procedure.first (prodCode unaryCode unaryCode) RationalHeatSample.pointCode
  let point := Procedure.second (prodCode unaryCode unaryCode) RationalHeatSample.pointCode
  let P := (Procedure.second unaryCode unaryCode).comp rp
  let Q := scaleProgram.comp P
  let N := countProgram.comp rp
  let M := magnitudeProgram.comp rp
  let p := precisionProgram.comp P
  let Qrat := Procedure.natToRat.comp (Procedure.unaryToBits.comp Q)
  let Nrat := Procedure.natToRat.comp (Procedure.unaryToBits.comp N)
  let eta := Procedure.ratInv.comp Qrat
  let width := Procedure.ratSub.comp (Qrat.pair eta)
  let step := Procedure.ratDiv.comp (width.pair Nrat)
  let settings := (M.pair (p.pair N)).pair (point.pair N)
  exact (N.pair (settings.pair (eta.pair step))).congrFun (by intro x; rfl)

noncomputable opaque program : Procedure inputCode ExactQuantumFactoring.BitStackProgram.ratCode approximate :=
  (RationalHeatBox.program.comp argumentProgram).congrFun (by intro x; rfl)

noncomputable opaque certificate :
    Turing.TM2ComputableInPolyTime inputCode ratCode approximate := program.toTM2

theorem scale_positive (P : ℕ) : 0 < scale P := by unfold scale; omega

theorem count_positive (R P : ℕ) : 0 < count R P := by
  have hscale := scale_positive P
  unfold count countPrefix
  positivity

end ContinuumCoulomb.ResolventSchedule

end OAI
