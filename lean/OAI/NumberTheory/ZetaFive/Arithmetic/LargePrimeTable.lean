import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace Zeta5.Workers.W20

def nm (x : ℝ) : ℝ := 18 - x

def nd (x : ℝ) : ℝ := max 0 (16 - x)

def ns (x : ℝ) : ℝ := min (15 - nd x) (nm x)

def ha (x : ℝ) : ℝ := min (nm x) (x - 4)

def hs (x : ℝ) : ℝ := x - 6

def ib (x : ℝ) : ℝ := max 0 (min (nd x) (ha x) - hs x)

def nbad (x : ℝ) : ℝ := max 0 (nm x - hs x) + max 0 (nd x - hs x)

def j0 (x : ℝ) : ℝ := max 0 (ns x + nd x - ha x - ib x)

def fInf (x : ℝ) : ℝ := 1 + if x < 16 then 1 else 0

def gInf (x : ℝ) : ℝ := if x < 15 then 1 else 0

def largePrimeLimit (x : ℝ) : ℝ :=
  15 * (2 * fInf x - gInf x) - 8 * nd x - 6 * ns x -
    2 * max 0 (15 - x) + 2 * j0 x + gInf x * max 0 (x - nbad x)

theorem piece_01 {x : ℝ} (ha' : 9 < x) (hb' : x < 46 / 5) :
    largePrimeLimit x = 2 * x - 73 := by
  have hd : nd x = 16 - x := by
    unfold nd
    exact max_eq_right (by linarith)
  have hn : ns x = x - 1 := by
    rw [ns, hd, nm, min_eq_left (by linarith)]
    ring
  have hh : ha x = x - 4 := by
    unfold ha nm
    exact min_eq_right (by linarith)
  have hi : ib x = 2 := by
    rw [ib, hd, hh, hs, min_eq_right (by linarith)]
    rw [max_eq_right (by linarith)]
    ring
  have hb : nbad x = 46 - 4*x := by
    rw [nbad, nm, hs, hd]
    rw [max_eq_right (by linarith)]
    rw [max_eq_right (by linarith)]
    ring
  have hj : j0 x = 17 - x := by
    rw [j0, hn, hd, hh, hi]
    rw [max_eq_right (by linarith)]
    ring
  simp only [largePrimeLimit, fInf, gInf, hn, hd, hj, hb,
    ite_eq_left (by linarith : x < 16),
    ite_eq_left (by linarith : x < 15)]
  rw [max_eq_right (by linarith : 0 ≤ 15-x)]
  rw [max_eq_left (by linarith)]
  ring

theorem piece_02 {x : ℝ} (ha' : 46 / 5 < x) (hb' : x < 19 / 2) :
    largePrimeLimit x = 7 * x - 119 := by
  have hd : nd x = 16 - x := by
    unfold nd
    exact max_eq_right (by linarith)
  have hn : ns x = x - 1 := by
    rw [ns, hd, nm, min_eq_left (by linarith)]
    ring
  have hh : ha x = x - 4 := by
    unfold ha nm
    exact min_eq_right (by linarith)
  have hi : ib x = 2 := by
    rw [ib, hd, hh, hs, min_eq_right (by linarith)]
    rw [max_eq_right (by linarith)]
    ring
  have hb : nbad x = 46 - 4*x := by
    rw [nbad, nm, hs, hd]
    rw [max_eq_right (by linarith)]
    rw [max_eq_right (by linarith)]
    ring
  have hj : j0 x = 17 - x := by
    rw [j0, hn, hd, hh, hi]
    rw [max_eq_right (by linarith)]
    ring
  simp only [largePrimeLimit, fInf, gInf, hn, hd, hj, hb,
    ite_eq_left (by linarith : x < 16),
    ite_eq_left (by linarith : x < 15)]
  rw [max_eq_right (by linarith : 0 ≤ 15-x)]
  rw [max_eq_right (by linarith)]
  ring

theorem piece_03 {x : ℝ} (ha' : 19 / 2 < x) (hb' : x < 10) :
    largePrimeLimit x = 15 * x - 195 := by
  have hd : nd x = 16 - x := by
    unfold nd
    exact max_eq_right (by linarith)
  have hn : ns x = 18 - x := by
    rw [ns, hd, nm, min_eq_right (by linarith)]
  have hh : ha x = x - 4 := by
    unfold ha nm
    exact min_eq_right (by linarith)
  have hi : ib x = 2 := by
    rw [ib, hd, hh, hs, min_eq_right (by linarith)]
    rw [max_eq_right (by linarith)]
    ring
  have hb : nbad x = 46 - 4*x := by
    rw [nbad, nm, hs, hd]
    rw [max_eq_right (by linarith)]
    rw [max_eq_right (by linarith)]
    ring
  have hj : j0 x = 36 - 3*x := by
    rw [j0, hn, hd, hh, hi]
    rw [max_eq_right (by linarith)]
    ring
  simp only [largePrimeLimit, fInf, gInf, hn, hd, hj, hb,
    ite_eq_left (by linarith : x < 16),
    ite_eq_left (by linarith : x < 15)]
  rw [max_eq_right (by linarith : 0 ≤ 15-x)]
  rw [max_eq_right (by linarith)]
  ring

theorem piece_04 {x : ℝ} (ha' : 10 < x) (hb' : x < 11) :
    largePrimeLimit x = 19 * x - 235 := by
  have hd : nd x = 16 - x := by
    unfold nd
    exact max_eq_right (by linarith)
  have hn : ns x = 18 - x := by
    rw [ns, hd, nm, min_eq_right (by linarith)]
  have hh : ha x = x - 4 := by
    unfold ha nm
    exact min_eq_right (by linarith)
  have hi : ib x = 22 - 2*x := by
    rw [ib, hd, hh, hs, min_eq_left (by linarith)]
    rw [max_eq_right (by linarith)]
    ring
  have hb : nbad x = 46 - 4*x := by
    rw [nbad, nm, hs, hd]
    rw [max_eq_right (by linarith)]
    rw [max_eq_right (by linarith)]
    ring
  have hj : j0 x = 16 - x := by
    rw [j0, hn, hd, hh, hi]
    rw [max_eq_right (by linarith)]
    ring
  simp only [largePrimeLimit, fInf, gInf, hn, hd, hj, hb,
    ite_eq_left (by linarith : x < 16),
    ite_eq_left (by linarith : x < 15)]
  rw [max_eq_right (by linarith : 0 ≤ 15-x)]
  rw [max_eq_right (by linarith)]
  ring

theorem piece_05 {x : ℝ} (ha' : 11 < x) (hb' : x < 12) :
    largePrimeLimit x = 17 * x - 213 := by
  have hd : nd x = 16 - x := by
    unfold nd
    exact max_eq_right (by linarith)
  have hn : ns x = 18 - x := by
    rw [ns, hd, nm, min_eq_right (by linarith)]
  have hh : ha x = 18 - x := by
    unfold ha nm
    exact min_eq_left (by linarith)
  have hi : ib x = 0 := by
    rw [ib, hd, hh, hs, min_eq_left (by linarith)]
    rw [max_eq_left (by linarith)]
  have hb : nbad x = 24 - 2*x := by
    rw [nbad, nm, hs, hd]
    rw [max_eq_right (by linarith)]
    rw [max_eq_left (by linarith)]
    ring
  have hj : j0 x = 16 - x := by
    rw [j0, hn, hd, hh, hi]
    rw [max_eq_right (by linarith)]
    ring
  simp only [largePrimeLimit, fInf, gInf, hn, hd, hj, hb,
    ite_eq_left (by linarith : x < 16),
    ite_eq_left (by linarith : x < 15)]
  rw [max_eq_right (by linarith : 0 ≤ 15-x)]
  rw [max_eq_right (by linarith)]
  ring

theorem piece_06 {x : ℝ} (ha' : 12 < x) (hb' : x < 15) :
    largePrimeLimit x = 15 * x - 189 := by
  have hd : nd x = 16 - x := by
    unfold nd
    exact max_eq_right (by linarith)
  have hn : ns x = 18 - x := by
    rw [ns, hd, nm, min_eq_right (by linarith)]
  have hh : ha x = 18 - x := by
    unfold ha nm
    exact min_eq_left (by linarith)
  have hi : ib x = 0 := by
    rw [ib, hd, hh, hs, min_eq_left (by linarith)]
    rw [max_eq_left (by linarith)]
  have hb : nbad x = 0 := by
    rw [nbad, nm, hs, hd]
    rw [max_eq_left (by linarith)]
    rw [max_eq_left (by linarith)]
    ring
  have hj : j0 x = 16 - x := by
    rw [j0, hn, hd, hh, hi]
    rw [max_eq_right (by linarith)]
    ring
  simp only [largePrimeLimit, fInf, gInf, hn, hd, hj, hb,
    ite_eq_left (by linarith : x < 16),
    ite_eq_left (by linarith : x < 15)]
  rw [max_eq_right (by linarith : 0 ≤ 15-x)]
  rw [max_eq_right (by linarith)]
  ring

theorem piece_07 {x : ℝ} (ha' : 15 < x) (hb' : x < 16) :
    largePrimeLimit x = 12 * x - 144 := by
  have hd : nd x = 16 - x := by
    unfold nd
    exact max_eq_right (by linarith)
  have hn : ns x = 18 - x := by
    rw [ns, hd, nm, min_eq_right (by linarith)]
  have hh : ha x = 18 - x := by
    unfold ha nm
    exact min_eq_left (by linarith)
  have hi : ib x = 0 := by
    rw [ib, hd, hh, hs, min_eq_left (by linarith)]
    rw [max_eq_left (by linarith)]
  have hb : nbad x = 0 := by
    rw [nbad, nm, hs, hd]
    rw [max_eq_left (by linarith)]
    rw [max_eq_left (by linarith)]
    ring
  have hj : j0 x = 16 - x := by
    rw [j0, hn, hd, hh, hi]
    rw [max_eq_right (by linarith)]
    ring
  simp only [largePrimeLimit, fInf, gInf, hn, hd, hj, hb,
    ite_eq_left (by linarith : x < 16),
    ite_eq_right (by linarith : ¬x < 15)]
  rw [max_eq_left (by linarith : 15-x ≤ 0)]
  ring

theorem piece_08 {x : ℝ} (ha' : 16 < x) (hb' : x < 18) :
    largePrimeLimit x = 6 * x - 78 := by
  have hd : nd x = 0 := by
    unfold nd
    exact max_eq_left (by linarith)
  have hn : ns x = 18 - x := by
    rw [ns, hd, nm, min_eq_right (by linarith)]
  have hh : ha x = 18 - x := by
    unfold ha nm
    exact min_eq_left (by linarith)
  have hi : ib x = 0 := by
    rw [ib, hd, hh, hs, min_eq_left (by linarith)]
    rw [max_eq_left (by linarith)]
  have hb : nbad x = 0 := by
    rw [nbad, nm, hs, hd]
    rw [max_eq_left (by linarith)]
    rw [max_eq_left (by linarith)]
    ring
  have hj : j0 x = 0 := by
    rw [j0, hn, hd, hh, hi]
    rw [max_eq_right (by linarith)]
    ring
  simp only [largePrimeLimit, fInf, gInf, hn, hd, hj, hb,
    ite_eq_right (by linarith : ¬x < 16),
    ite_eq_right (by linarith : ¬x < 15)]
  rw [max_eq_left (by linarith : 15-x ≤ 0)]
  ring

end Zeta5.Workers.W20

end

end OAI
