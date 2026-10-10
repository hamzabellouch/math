import Mathlib.Algebra.Field.Rat
import OAI.Analysis.Laughlin.FourBody.RowCompute

namespace OAI

namespace Laughlin.Certificate.GramCompute

def quadruples (D : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range (D+2)).flatMap (fun a =>
    (List.range (D+2)).flatMap (fun b =>
      (List.range (D+2)).filterMap (fun c =>
        let d := D+1-a-b-c
        if a < b ∧ b < c ∧ c < d ∧ a+b+c ≤ D+1 then some (a,b,c,d) else none)))

def LFast (D r : ℕ) (A : ℕ × ℕ × ℕ × ℕ) : ℚ :=
  let (a,b,c,d) := A
  let term := fun (x y j k : ℕ) => ((x : ℤ)-(y : ℤ)) *
    ((x+y-1).factorial : ℤ) * (j.factorial : ℤ) * (k.factorial : ℤ) *
      RowCompute.VFast r D D (x+y-1) j k
  (2 : ℚ)^(((1 : ℤ)-2*(D : ℤ)+(r : ℤ))/2) *
    ((term a b c d - term a c b d + term a d b c + term b c a d -
      term b d a c + term c d a b : ℤ) : ℚ)

def ZFast (D r s : ℕ) : ℚ :=
  ((quadruples D).map (fun A =>
    let (a,b,c,d) := A
    LFast D r A * LFast D s A /
      ((a.factorial : ℚ)*(b.factorial : ℚ)*(c.factorial : ℚ)*(d.factorial : ℚ)))).sum
end Laughlin.Certificate.GramCompute

end OAI
