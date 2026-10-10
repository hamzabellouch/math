import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

namespace OAI

/-!
# Integer arithmetic for the low-angular separators

The polynomial recurrence and integer sign inequalities in Appendix
`cert:winding` use Gaussian integer coefficients in ascending order.
-/

namespace DefocusingNLS
namespace SeparatorArithmetic

def scale : ℤ := 100000000
def centerB : ℤ := 33477607
def centerZ : ℤ := 270506819

def addCoefficients : List GaussianInt → List GaussianInt → List GaussianInt
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addCoefficients xs ys

def scaleCoefficients (a : GaussianInt) (xs : List GaussianInt) : List GaussianInt :=
  xs.map (a * ·)

/-- Multiplication by the linear polynomial `a + scale * X`. -/
def mulLinear (a : GaussianInt) (xs : List GaussianInt) : List GaussianInt :=
  addCoefficients (scaleCoefficients a xs)
    (0 :: scaleCoefficients (scale : GaussianInt) xs)

/-- The exact backward recurrence, from `n = 7` down to `n = 0`. -/
def backwardStep (ℓ n : ℕ) (xy : List GaussianInt × List GaussianInt) :
    List GaussianInt × List GaussianInt :=
  let t : GaussianInt := ⟨scale * n + 50000000 * ℓ - 3125000, -centerB⟩
  let d : GaussianInt := t - ⟨scale * (ℓ + 5), centerZ⟩
  (addCoefficients (mulLinear d xy.1) (scaleCoefficients ⟨0, -centerZ⟩ xy.2),
    mulLinear t (addCoefficients xy.1 xy.2))

def backwardCoefficients (ℓ : ℕ) : List GaussianInt × List GaussianInt :=
  [7, 6, 5, 4, 3, 2, 1, 0].foldl (fun xy n => backwardStep ℓ n xy) ([], [1])

/-- The coefficient `Im ∑ xₖ conj(yⱼ₋ₖ)` of the degree-fifteen polynomial. -/
def windingCoefficient (ℓ j : ℕ) : ℤ :=
  let xy := backwardCoefficients ℓ
  ((List.range (j + 1)).map fun k =>
    (xy.1[k]?.getD 0 * star (xy.2[j - k]?.getD 0)).im).sum

/-- Terms in the denominator-cleared evaluation of an axis polynomial at
`w = ε (q/100)²`. The coordinate is `0` for real and `1` for imaginary. -/
def evaluationTerms (ℓ c : ℕ) (ε q : ℤ) : List ℤ :=
  (List.range 8).map fun j =>
    windingCoefficient ℓ (2 * j + c) * 100 ^ (14 - 2 * j) * (-ε * q ^ 2) ^ j

def separatorMargin (ℓ c : ℕ) (ε q e : ℤ) : ℤ :=
  let terms := evaluationTerms ℓ c ε q
  (10000 * e * terms.sum) / (terms.map (fun z => |z|)).sum

/-- A positive relative integer margin proves the requested strict sign. -/
theorem sign_of_positive_margin (ℓ c : ℕ) (ε q e : ℤ)
    (h : 0 < separatorMargin ℓ c ε q e) :
    0 < e * (evaluationTerms ℓ c ε q).sum := by
  let terms := evaluationTerms ℓ c ε q
  have hd : 0 ≤ (terms.map (fun z => |z|)).sum :=
    List.sum_nonneg (fun z hz => by
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hz
      exact abs_nonneg y)
  by_cases hz : (terms.map (fun z => |z|)).sum = 0
  · simp [separatorMargin, terms, hz] at h
  · have hdpos : 0 < (terms.map (fun z => |z|)).sum := lt_of_le_of_ne hd (Ne.symm hz)
    by_contra hn
    have hnum : 10000 * e * terms.sum ≤ 0 := by
      dsimp [terms]
      nlinarith
    have hdiv := Int.ediv_nonpos_of_nonpos_of_neg hnum hdpos
    exact (not_lt_of_ge hdiv) h

def positiveArguments : ℕ → List ℤ
  | 0 => [0, 45, 90, 145, 220, 315, 450, 635, 920, 1780, 3100, 7500]
  | 1 => [0, 30, 68, 116, 173, 250, 350, 485, 680, 1005, 1880, 3210, 7500]
  | 2 => [0, 51, 78, 94, 121, 165, 218, 278, 369, 490, 720, 1080, 1930, 3340, 7500]
  | _ => [0, 57, 95, 122, 157, 205, 265, 333, 431, 559, 784, 1148, 2020, 3521, 7500]

def signCycle (j : ℕ) : ℤ × ℤ :=
  match j % 4 with
  | 0 => (1, 1)
  | 1 => (-1, 1)
  | 2 => (-1, -1)
  | _ => (1, -1)

def signOffset : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | _ => 2

/-- All margins in one row of the appendix, including the negative-argument
tests when they are required. -/
def rowMargins (ℓ : ℕ) : List ℤ :=
  let positive := (positiveArguments ℓ).zipIdx.flatMap fun (q, j) =>
    let signs := signCycle (j + signOffset ℓ)
    [separatorMargin ℓ 0 1 q signs.1, separatorMargin ℓ 1 1 q signs.2]
  let negative := if ℓ < 2 then
    [separatorMargin ℓ 0 (-1) 50 1, separatorMargin ℓ 1 (-1) 50 1,
      separatorMargin ℓ 0 (-1) 200 (-1), separatorMargin ℓ 1 (-1) 200 (-1)] else []
  positive ++ negative

/-- The four exact minimum margins reported in `cert:separator-margins`. -/
theorem row_zero_margin : (rowMargins 0).min? = some 583 := by decide +kernel

theorem row_one_margin : (rowMargins 1).min? = some 432 := by decide +kernel

theorem row_two_margin : (rowMargins 2).min? = some 80 := by decide +kernel

theorem row_three_margin : (rowMargins 3).min? = some 68 := by decide +kernel

theorem row_margin_pos (ℓ : Fin 4) (m : ℤ) (hm : m ∈ rowMargins ℓ) : 0 < m := by
  fin_cases ℓ
  · have h := (List.min?_eq_some_iff.mp row_zero_margin).2 m hm
    omega
  · have h := (List.min?_eq_some_iff.mp row_one_margin).2 m hm
    omega
  · have h := (List.min?_eq_some_iff.mp row_two_margin).2 m hm
    omega
  · have h := (List.min?_eq_some_iff.mp row_three_margin).2 m hm
    omega

end SeparatorArithmetic
end DefocusingNLS

end OAI
