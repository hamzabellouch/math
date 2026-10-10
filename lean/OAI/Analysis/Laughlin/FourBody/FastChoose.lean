import OAI.Analysis.Laughlin.FourBody.Integral

namespace OAI

namespace Laughlin.Certificate

def UFast (c z T p : ℕ) : ℤ :=
  if z ≤ T ∧ p ≤ T then
    (((List.range (min p z + 1)).filter (fun h => p + z ≤ T + h)).map
      (fun h => (-1 : ℤ) ^ (z-h) * (Nat.fast_choose z h : ℤ) *
        (Nat.fast_choose (T-z) (p-h) : ℤ) * (c : ℤ) ^ (p-h))).sum
  else 0

theorem U_eq_fast (c z T p : ℕ) : U c z T p = UFast c z T p := by
  simp only [U, UFast, Nat.choose_eq_fast_choose]

def VFast (r D T p j k : ℕ) : ℤ :=
  if r ≤ j+k then UFast 1 r (j+k) j * UFast 1 (D-r) (T-r) p else 0

theorem V_eq_fast (r D T p j k : ℕ) : V r D T p j k = VFast r D T p j k := by
  simp only [V, VFast, U_eq_fast]

def yEntryIntegralFast (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) : ℤ :=
  let (p,j,a) := e
  let (q,l,b) := f
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  if D ≤ T then
    a*b*VFast r D T p j k*VFast s D T q l i *
      (2 : ℤ)^((65-2*(T : ℤ)+(p : ℤ)+(q : ℤ)-(t : ℤ)+((r+s)/2 : ℕ)).toNat) *
      (i.factorial : ℤ)*(k.factorial : ℤ)*(t.factorial : ℤ) *
      ((24 : ℕ).descFactorial (24-(T-D)) : ℤ)
  else 0

theorem yEntryIntegral_eq_fast (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) :
    yEntryIntegral D r s t e f = yEntryIntegralFast D r s t e f := by
  simp only [yEntryIntegral, yEntryIntegralFast, V_eq_fast]

def yRowIntegralFast (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) : ℤ :=
  (row.2.2.map (fun e => (row.2.2.map (fun f => yEntryIntegralFast D r s row.1 e f)).sum)).sum

theorem yRowIntegral_eq_fast (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    yRowIntegral D r s row = yRowIntegralFast D r s row := by
  simp only [yRowIntegral, yRowIntegralFast, yEntryIntegral_eq_fast]

theorem source_yRow_eq_fastIntegral (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (yRowIntegralFast D r s (rows[n]!) : ℚ) / arithmeticScale := by
  rw [source_yRow_eq_integral D r s n hn, yRowIntegral_eq_fast]

def LFast (D r : ℕ) (A : ℕ × ℕ × ℕ × ℕ) : ℚ :=
  let (a,b,c,d) := A
  let term := fun (x y j k : ℕ) => ((x : ℤ)-(y : ℤ)) *
    ((x+y-1).factorial : ℤ) * (j.factorial : ℤ) * (k.factorial : ℤ) *
      VFast r D D (x+y-1) j k
  (2 : ℚ)^(((1 : ℤ)-2*(D : ℤ)+(r : ℤ))/2) *
    ((term a b c d - term a c b d + term a d b c + term b c a d -
      term b d a c + term c d a b : ℤ) : ℚ)

def ZFast (D r s : ℕ) : ℚ :=
  ((quadruples D).map (fun A =>
    let (a,b,c,d) := A
    LFast D r A * LFast D s A /
      ((a.factorial : ℚ)*(b.factorial : ℚ)*(c.factorial : ℚ)*(d.factorial : ℚ)))).sum

theorem L_eq_fast (D r : ℕ) (A : ℕ × ℕ × ℕ × ℕ) : L D r A = LFast D r A := by
  simp only [L, LFast, V_eq_fast]

theorem Z_eq_fast (D r s : ℕ) : Z D r s = ZFast D r s := by
  simp only [Z, ZFast, L_eq_fast]

end Laughlin.Certificate

end OAI
