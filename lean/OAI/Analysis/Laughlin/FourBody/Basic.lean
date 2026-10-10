import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.Operators.Certificate

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators Matrix

def V (r D T p j k : ℕ) : ℤ :=
  if r ≤ j+k then U 1 r (j+k) j * U 1 (D-r) (T-r) p else 0

def yEntry (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) : ℚ :=
  let (p,j,a) := e
  let (q,l,b) := f
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  if D ≤ T then
    (a : ℚ) * (b : ℚ) * (V r D T p j k : ℚ) * (V s D T q l i : ℚ) *
    (2 : ℚ) ^ (1-2*(T : ℤ)+(p : ℤ)+(q : ℤ)-(t : ℤ)+((r+s)/2 : ℕ)) *
    ((i.factorial : ℚ) * (k.factorial : ℚ) * (t.factorial : ℚ) /
      ((T-D).factorial : ℚ))
  else 0

def yRow (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) : ℚ :=
  (row.2.2.map (fun e => (row.2.2.map (fun f => yEntry D r s row.1 e f)).sum)).sum

def Y (D r s : ℕ) : ℚ :=
  -(rows.map (yRow D r s)).sum / (10^14 : ℚ)

theorem Y_expand (D r s : ℕ) : Y D r s =
    -(yRow D r s (rows[0]!) + (yRow D r s (rows[1]!) +
      (yRow D r s (rows[2]!) + (yRow D r s (rows[3]!) +
        (yRow D r s (rows[4]!) + (yRow D r s (rows[5]!) +
          (yRow D r s (rows[6]!) + 0))))))) / (10^14 : ℚ) := by rfl

def quadruples (D : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range (D+2)).flatMap (fun a =>
    (List.range (D+2)).flatMap (fun b =>
      (List.range (D+2)).filterMap (fun c =>
        let d := D+1-a-b-c
        if a < b ∧ b < c ∧ c < d ∧ a+b+c ≤ D+1 then some (a,b,c,d) else none)))

def L (D r : ℕ) (A : ℕ × ℕ × ℕ × ℕ) : ℚ :=
  let (a,b,c,d) := A
  let term := fun (x y j k : ℕ) => ((x : ℤ)-(y : ℤ)) *
    ((x+y-1).factorial : ℤ) * (j.factorial : ℤ) * (k.factorial : ℤ) *
      V r D D (x+y-1) j k
  (2 : ℚ)^(((1 : ℤ)-2*(D : ℤ)+(r : ℤ))/2) *
    ((term a b c d - term a c b d + term a d b c + term b c a d -
      term b d a c + term c d a b : ℤ) : ℚ)

def Z (D r s : ℕ) : ℚ :=
  ((quadruples D).map (fun A =>
    let (a,b,c,d) := A
    L D r A * L D s A /
      ((a.factorial : ℚ)*(b.factorial : ℚ)*(c.factorial : ℚ)*(d.factorial : ℚ)))).sum

def copyLabel {D : ℕ} (i : Fin ((D+1)/2)) : ℕ := 2*i.val+1

def gramRational (D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ :=
  fun i j => Z D (copyLabel i) (copyLabel j)

def errorRational (D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ :=
  fun i j => Y D (copyLabel i) (copyLabel j)


theorem gram_five : gramRational 5 =
    !![48, -24, 60; -24, 12, -30; 60, -30, 75] := by
  decide +kernel

end Laughlin.Certificate

end OAI
